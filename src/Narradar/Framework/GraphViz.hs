{-# LANGUAGE CPP #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}

module Narradar.Framework.GraphViz where

import Control.Applicative
import Control.Monad
import Control.Monad.Free.Narradar
import Data.Graph
import Data.Foldable (toList)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List hiding (unlines)
import Data.Maybe
import Text.Dot
import Text.PrettyPrint
import Prelude hiding (unlines)
#ifdef DEBUG
import System.Process
import Text.Printf
#endif
import Narradar.Types.ArgumentFiltering (fromAF)
import Narradar.Framework.Proof
import Narradar.Types
import Narradar.Utils
import qualified Language.Prolog.Syntax as Prolog

-- ----------------------------
-- GraphViz logs
-- ----------------------------
sliceWorkDone = foldFree return (Impure . f) where
    f (Or  p pi pp) = (Or  p pi $ takeWhileAndOneMore (not . isSuccess) pp)
    f (And p pi pp) = (And p pi $ takeWhileAndOneMore isSuccess pp)
    f (MPlusPar p1 p2) = if isSuccess p1 then Stage p1 else (MPlusPar p1 p2)  -- We use stage in lieu of return here
    f (MPlus    p1 p2) = if isSuccess p1 then Stage p1 else (MPlus    p1 p2)
    f (MAnd     p1 p2) = if not(isSuccess p1) then Stage p1 else (MAnd p1 p2)
    f x = x
    takeWhileAndOneMore _ []     = []
    takeWhileAndOneMore f (x:xs) = if f x then x : takeWhileAndOneMore f xs else [x]

instance Functor Dot where fmap = liftM

data Parent = N NodeId | Cluster (NodeId, Parent)
getParentNode (N n) = n
getParentNode (Cluster (_,n)) = getParentNode n

data PprDot = PprDot { showFailedPaths :: Bool }

pprDot = pprDot' PprDot{showFailedPaths=False}

pprDot' PprDot{..} prb = showDot $ do
               attribute ("size", "100,100")
               attribute ("compound", "true")
               foldFree (\_->return) f (annotate (const False) isSuccess (sliceWorkDone prb)) =<< (N <$> node [("label","0")])
  where
    f (Annotated done Success{..})    par = problemNode problem done par >>= procnode done procInfo >>= childnode' [("label", "YES"), ("color","#29431C")] (doneEdge done)
    f (Annotated done Fail{..})       par = problemNode problem done par >>= procnode done procInfo >>= childnode' [("label", "NO"),("color","#60233E")] (doneEdge done)
    f (Annotated _ MZero{})        par = return par -- childnode' [("label","Don't Know")] (doneEdge done) par
    f (Annotated done DontKnow{..})   par = procnode done procInfo par   >>= childnode' [("label","Don't Know")] (doneEdge done)
--    f (Annotated done (MAnd p1 ))par = p1 par
    f (Annotated _ MDone{})        par = return par
    f (Annotated _ (MAnd  p1 p2))  par = do
                                cme <- cluster $ do
                                             attribute ("color", "#E56A90")
                                             p1 par
                                             p2 par
                                             return par
                                return (Cluster cme)
    f (Annotated done (MPlusPar p1 p2))  par = f (Annotated done (MPlus p1 p2)) par
    f (Annotated done (MPlus p1 p2))  par = do
        dis <- childnode' [("shape","point"),("label","")] (doneEdge done) par
        p1 dis
        p2 dis
        return dis
    f (Annotated done And{subProblems=[p], procInfo = proc@(SomeInfo pi)}) par | isAFProc pi = procnode' proc done par >>= \me -> p me >> return me
    f (Annotated done And{subProblems=[p], ..}) par = f (Annotated done Or{subProblems = [p], ..}) par
    f (Annotated done And{..}) par = do
                                trs <- if (done || showFailedPaths) then problemNode problem done par else return par
                                cme <- cluster $ do
                                             attribute ("color", "#E56A90")
                                             me <- procnode done procInfo trs
                                             forM_ subProblems ($ me)
                                             return me
                                return (Cluster cme)
    f (Annotated done  Step{..}) par = f (Annotated done Or{subProblems = [subProblem], ..}) par
    f (Annotated _ (Stage p)) par = p par
    f (Annotated done Or{..})   par
      | done || showFailedPaths = problemNode problem done par >>= procnode done procInfo >>= \me -> forM_ subProblems ($ me) >> return me
      | otherwise = procnode done procInfo par   >>= \me -> forM_ subProblems ($ me) >> return me

--    problemLabel :: (Ord v, Ppr v, Ord id, Ppr id) => Problem id v -> (String, String)
    problemLabel p = ("label", pprTPDBdot p)

--    problemColor :: Problem id v -> (String, String)
    problemColor p | isPrologProblem        p = ("color", "#F6D106")
                   | isFullNarrowingProblem p = ("color", "#4488C9")
                   | isBNarrowingProblem    p = ("color", "#FD6802")
                   | isGNarrowingProblem    p = ("color", "#FD6802")
                   | isRewritingProblem     p = ("color", "#EAAAFF")
                   | otherwise = error ("problemColor")
--    problemAttrs :: (Ord v, Ppr v, Ord id, Show id) => Problem id v -> [(String,String)]
    problemAttrs p    = [problemLabel p, problemColor p, ("shape","box"), ("style","bold"),("fontname","monospace"),("fontsize","10"),("margin",".2,.2")]

    problemNode  (SomeProblem p) done par = childnode'(problemAttrs p) (doneEdge done) par
    doneEdge True     = [("color", "green")]
    doneEdge False    = [("color", "red")]

    procnode :: Bool -> SomeInfo -> Parent -> Dot Parent
    procnode done (SomeInfo (DependencyGraph gr)) par | done || showFailedPaths = do
      (cl, nn) <- cluster (attribute ("shape", "ellipse") >> pprGraph gr [])
      case nn of
        []   -> return par
        me:_ -> do case par of
                     N n             -> edge n me ([("lhead", show cl)] ++ doneEdge done)
                     Cluster (cl',n) -> edge (getParentNode n) me [("ltail", show cl'), ("lhead", show cl)]
                   return (Cluster (cl, N me))

    procnode done (SomeInfo (SCCGraph gr sccs)) par = do
      (cl, nn) <- cluster (
                    attribute ("shape", "ellipse") >>
                    pprGraph gr (zip sccs (cycle ["yellow","darkorange"
                                                 , "hotpink", "hotpink4", "purple", "brown","red","green"])))
      case (nn,par) of
        ([]  , _  )             -> return par
        (me:_, N n)             -> edge n me ([("lhead", show cl)] ++ doneEdge done) >> return (Cluster (cl, N me))
        (me:_, Cluster (cl',n)) -> edge (getParentNode n) me [("ltail", show cl'), ("lhead", show cl)] >> return (Cluster (cl, N me))


    procnode done (SomeInfo (UsableGraph gr reachable)) par = do
      (cl, nn) <- cluster (attribute ("shape", "ellipse") >> (pprGraph gr [(reachable,"blue")]))
      case (nn,par) of
        ([]  , _  )             -> return par
        (me:_, N n)             -> edge n me ([("lhead", show cl)] ++ doneEdge done) >> return (Cluster (cl, N me))
        (me:_, Cluster (cl',n)) -> edge (getParentNode n) me ([("ltail", show cl'), ("lhead", show cl)] ++ doneEdge done) >> return (Cluster (cl, N me))

    procnode done  procInfo      par = childnode'  [("label", show procInfo),("fontsize","10")] (doneEdge done) par >>= \me -> return me

    procnode' procInfo done par = childnode' [("label", show procInfo)] (doneEdge done) par >>= \me -> return me

    childnode' attrs edge_attrs (N par) = node (("URL","url"):attrs) >>= \n -> edge par n edge_attrs >> return (N n)
    childnode' attrs edge_attrs (Cluster (cl,par)) = node (("URL","url"):attrs) >>= \n -> edge (getParentNode par) n (("ltail", show cl):edge_attrs) >> return (N n)


pprTPDBdot :: (Ord v, Ppr v, Ord id, Ppr id) => Problem id v -> String
pprTPDBdot (Problem Prolog{..} _ _) =
    showPpr program ++ "\\l" ++
    unlines ["%Query: " ++ show(pprGoalAF (getSignature program) g) | g <- goals]

pprTPDBdot p@(Problem typ trs dps) = unlines $
    [ "(VAR " ++ (unwords $ map showPpr $ toList $ getVars p) ++ ")"
    , "(PAIRS\\l" ++ (unlines (map ((' ':).show.pprRule) (rules dps))) ++ ")"
    , "(RULES\\l" ++ (unlines (map ((' ':).show.pprRule) (rules trs))) ++ ")"] ++
    maybeToList (fmap (\af -> "(AF\\l" ++ pprAF af ++ ")") (getAF typ)) ++ ["\\l"]

  where pprRule (a:->b) = pprTerm a <+> text "->" <+> pprTerm b
        pprTerm = foldTerm ppr f
        f t@(getId -> Just id)
            | null tt = ppr id
            | otherwise = ppr id <> parens (hcat$ punctuate comma tt)
         where tt = toList t

pprAF af = unlines [ ' ' : unwords (intersperse ","
                          [ showPpr f ++ ": " ++ showPpr (toList aa) | (f, aa) <- xx])
                      | xx <- chunks 4 $ Map.toList $ fromAF af]

unlines = concat . intersperse "\\l"


-- --------------------
-- Graphing fgl graphs
-- --------------------

pprGraph g specials = do
  nodeids <- forM (vertices g) $ \n -> node [("label",show n), ("color", getColor n)]
  forM_ (edges g) $ \(n1,n2) -> edge (nodeids !! n1) (nodeids !! n2) [("color",getColorEdge n1 n2)]
  return nodeids
  where
     getColor node = maybe "black" snd $ find ((node `Set.member`) . fst) specials
     getColorEdge n1 n2
        | c1 == c2  = c1
        | otherwise = "black"
           where c1 = getColor n1; c2 = getColor n2
#ifdef DEBUG
debugDot x = let t = "temp" in writeFile (t ++ ".dot") (pprDot' (PprDot True) x) >> system (printf "dot %s.dot -O -Tpdf && open %s.dot.pdf" t t)
#endif
