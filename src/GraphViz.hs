{-# LANGUAGE RecordWildCards, ViewPatterns, PackageImports #-}
module GraphViz where

import Control.Applicative
import Control.Monad
import Control.Monad.Free
import Data.Graph.Inductive (labNodes, labEdges)
import Data.Foldable (foldMap)
import Data.List
import Text.Dot
import Text.PrettyPrint

import Proof
import Types
import TRS
import TRS.Utils

-- ----------------------------
-- GraphViz logs
-- ----------------------------
sliceWorkDone = foldFree return (Impure . f) where
    f (Or p pi pp) = (Or p pi $ takeWhileAndOneMore (not . isSuccess) pp)
    f x = x
    takeWhileAndOneMore f []     = []
    takeWhileAndOneMore f (x:xs) = if f x then x : takeWhileAndOneMore f xs else [x]

instance Functor Dot where fmap = liftM

data Parent = N NodeId | Cluster (NodeId, Parent)
getParentNode (N n) = n
getParentNode (Cluster (_,n)) = getParentNode n

pprDot prb = showDot $ do
               attribute ("compound", "true")
               foldFree trsnode' f (annotate (const False) isSuccess (sliceWorkDone prb)) =<< (N <$> node [("label","0")])
  where
    f (Annotated done Success{..})    par = trsnode problem done par >>= procnode procInfo >>= childnode [("label", "YES"), ("color","#29431C")]
    f (Annotated done Fail{..})       par = trsnode problem done par >>= procnode procInfo >>= childnode [("label", "NO"),("color","#60233E")]
    f (Annotated done MZero{})        par = return par -- childnode' [("label","Don't Know")] (doneEdge done) par
    f (Annotated done DontKnow{..})   par = trsnode problem done par >>= procnode procInfo >>= childnode [("label","Don't Know")]
    f (Annotated done (MPlus p1 p2))  par = do
        dis <- childnode' [("shape","point"),("label","")] (doneEdge done) par
        p1 dis
        p2 dis
        return dis
    f (Annotated done And{subProblems=[p], procInfo = proc@AFProc{}}) par
                         = procnode' proc done par >>= \me -> p me >> return me
    f (Annotated done And{subProblems=[p], ..}) par = f (Annotated done Or{subProblems = [p], ..}) par
    f (Annotated done And{..}) par = do
                                trs <- trsnode problem done par
                                cme <- cluster $ do
                                             attribute ("color", "#E56A90")
                                             me <- procnode procInfo trs
                                             forM_ subProblems ($ me)
                                             return me
                                return (Cluster cme)
    f (Annotated done Or{..})  par = trsnode problem done par >>= procnode procInfo >>= \me -> forM_ subProblems ($ me) >> return me

trsLabel trs      = ("label", pprTPDBdot trs)
trsColor p | isFullNarrowingProblem p = ("color", "#F97523")
           | isBNarrowingProblem    p = ("color", "#8E9C6D")
           | isRewritingProblem     p = ("color", "#60233E")
trsAttrs trs      = [trsLabel trs, trsColor trs, ("shape","box"), ("style","bold"),("fontname","monospace"),("fontsize","10"),("margin",".2,.2")]
trsnode  trs done = childnode'(trsAttrs trs) (doneEdge done)
trsnode' trs      = childnode (trsAttrs trs)
doneEdge True     = [("color", "green")]
doneEdge False    = [("color", "red")]

procnode  (DependencyGraph gr) par = do
  (cl, nn) <- cluster (attribute ("shape", "ellipse") >> (pprGraph gr))
  case nn of
    []   -> return par
    me:_ -> do case par of
                N n             -> edge n me [("lhead", show cl)]
                Cluster (cl',n) -> edge (getParentNode n) me [("ltail", show cl'), ("lhead", show cl)]
               return (Cluster (cl, N me))
procnode  procInfo      par = childnode  [("label", show procInfo)] par >>= \me -> return me
procnode' procInfo done par = childnode' [("label", show procInfo)] (doneEdge done) par >>= \me -> return me

childnode attrs = childnode' attrs []
childnode' attrs edge_attrs (N par) = node (("URL","url"):attrs) >>= \n -> edge par n edge_attrs >> return (N n)
childnode' attrs edge_attrs (Cluster (cl,par)) = node (("URL","url"):attrs) >>= \n -> edge (getParentNode par) n (("ltail", show cl):edge_attrs) >> return (N n)

pprTPDBdot :: TRS.Ppr f => Problem f -> String
pprTPDBdot PrologProblem{..} =
    show (Prolog.ppr program) ++ "\\l" ++
    unlines ["%Query: " ++ pprGoal g | g <- goals]
pprTPDBdot p@(Problem typ trs@TRS{} dps@TRS{} ) = unlines $
    [ "(VAR " ++ (unwords $ map show $ snub $ foldMap3 vars' (rules <$> p)) ++ ")"
    , "(PAIRS\\l" ++ (unlines (map ((' ':).show) (rules dps))) ++ ")"
    , "(RULES\\l" ++ (unlines (map ((' ':).show) (rules trs))) ++ ")\\l"]
unlines = concat . intersperse "\\l"


-- --------------------
-- Graphing fgl graphs
-- --------------------
pprGraph g = do
  let nodes = sortBy (compare `on` fst) (labNodes g)
      edges = labEdges g
  nodeids <- forM nodes $ \(n,_) -> node [("label",show n)]
  forM_ edges $ \(n1,n2,_) -> edge (nodeids !! n1) (nodeids !! n2) []
  return nodeids