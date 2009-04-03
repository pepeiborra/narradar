{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
module Narradar.GraphViz where

import Control.Applicative
import Control.Monad
import Control.Monad.Free
import Data.Graph
import Data.Foldable (foldMap, toList)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List hiding (unlines)
import Data.Maybe
import Text.Dot
import Text.PrettyPrint
import Prelude hiding (unlines)

import Narradar.ArgumentFiltering (fromAF)
import Narradar.Proof
import Narradar.Types
import Narradar.Utils
import TRS
import qualified Language.Prolog.Syntax as Prolog

-- ----------------------------
-- GraphViz logs
-- ----------------------------
sliceWorkDone = foldFree return (Impure . f) where
    f (Or p pi pp) = (Or p pi $ takeWhileAndOneMore (not . isSuccess) pp)
    f MPlusPar{}   = MZero
    f x = x
    takeWhileAndOneMore f []     = []
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
    f (Annotated done MZero{})        par = return par -- childnode' [("label","Don't Know")] (doneEdge done) par
    f (Annotated done DontKnow{..})   par = procnode done procInfo par   >>= childnode' [("label","Don't Know")] (doneEdge done)
--    f (Annotated done (MAnd p1 ))par = p1 par
    f (Annotated done MDone{})        par = return par
    f (Annotated done (MAnd  p1 p2))  par = do
                                cme <- cluster $ do
                                             attribute ("color", "#E56A90")
                                             p1 par
                                             p2 par
                                             return par
                                return (Cluster cme)
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
    f (Annotated done Step{..}) par = f (Annotated done Or{subProblems = [subProblem], ..}) par
    f (Annotated done Or{..})   par
      | done || showFailedPaths = problemNode problem done par >>= procnode done procInfo >>= \me -> forM_ subProblems ($ me) >> return me
      | otherwise = procnode done procInfo par   >>= \me -> forM_ subProblems ($ me) >> return me

    problemLabel :: (TRSC f, T id :<: f, Ord id, Show id) => ProblemG id f -> (String, String)
    problemLabel p = ("label", pprTPDBdot p)

    problemColor :: ProblemG id f -> (String, String)
    problemColor p | isPrologProblem        p = ("color", "#F6D106")
                   | isFullNarrowingProblem p = ("color", "#4488C9")
                   | isBNarrowingProblem    p = ("color", "#FD6802")
                   | isGNarrowingProblem    p = ("color", "#FD6802")
                   | isRewritingProblem     p = ("color", "#EAAAFF")
                   | otherwise = error ("problemColor")
    problemAttrs :: (TRSC f, T id :<: f, Ord id, Show id) => ProblemG id f -> [(String,String)]
    problemAttrs p    = [problemLabel p, problemColor p, ("shape","box"), ("style","bold"),("fontname","monospace"),("fontsize","10"),("margin",".2,.2")]

    problemNode  (SomeProblem p) done par = childnode'(problemAttrs p) (doneEdge done) par
--problemNode  (SomePrologProblem cc gg) done = childnode'(problemAttrs (mkPrologProblem cc gg :: Problem BasicId)) (doneEdge done)
    problemNode' p    = childnode (problemAttrs p)
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

    childnode attrs = childnode' attrs []
    childnode' attrs edge_attrs (N par) = node (("URL","url"):attrs) >>= \n -> edge par n edge_attrs >> return (N n)
    childnode' attrs edge_attrs (Cluster (cl,par)) = node (("URL","url"):attrs) >>= \n -> edge (getParentNode par) n (("ltail", show cl):edge_attrs) >> return (N n)


pprTPDBdot :: (TRSC f, T id :<: f, Ord id, Show id) => ProblemG id f  -> String
{-# SPECIALIZE pprTPDBdot :: Problem BBasicId -> String #-}
pprTPDBdot p@(Problem Prolog{..} _ _) =
    show (Prolog.ppr program) ++ "\\l" ++
    unlines ["%Query: " ++ show(pprGoalAF (getSignature program) g) | g <- goals]

pprTPDBdot p@(Problem typ trs dps) = unlines $
    [ "(VAR " ++ (unwords $ map show $ snub $ foldMap3 vars' (rules <$> p)) ++ ")"
    , "(PAIRS\\l" ++ (unlines (map ((' ':).show) (rules dps))) ++ ")"
    , "(RULES\\l" ++ (unlines (map ((' ':).show) (rules trs))) ++ ")"] ++
    maybeToList (fmap (\af -> "(AF\\l" ++ pprAF af ++ ")") (getGoalAF typ)) ++ ["\\l"]

pprAF af = unlines [ ' ' : unwords (intersperse ","
                          [ show f ++ ": " ++ show (toList aa) | (f, aa) <- xx])
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