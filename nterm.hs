module NTerm where


import Problem
import TRS
import Names
import DPairs
import OrderSorted (OrderS)

import Control.Arrow (first, second, (***))
import Data.Graph.Inductive
import Data.Graph.Inductive.Query.DFS(scc, components)
--import Data.Graph.Inductive.Query.DFS(esp)
import Data.Foldable (toList, Foldable)
import Data.List
import Data.Maybe
import Text.PrettyPrint


------------------
-- DP Problems
------------------

mkNDPProblem trs = Problem Narrowing `uncurry` ndpairs trs

graphProcessor problem@(Problem Narrowing trs dps) = And DependencyGraph problem [NotDone $ Problem Narrowing trs  (map (dps !!) ciclo) | ciclo <- cc]
    where edges = computeArcsOfDG trs dps
          cc    = dcycles trs (dps, edges)

afProcessor problem@(Problem Narrowing trs dps) = if null orProblems
                                                  then Fail NarrowingAF problem "Could not find a grounding AF"
                                                  else Or NarrowingAF problem orProblems
    where afs = snub $ concatMap (findGroundAF trs) dps
          orProblems = [And (AF af) problem [NotDone $ applyAF af (Problem Rewriting trs dps)] | af <- afs]

----------------
-- Primitives
----------------
ndepGraph trs = let (trs',dps) = ndpairs trs in (trs',dps, computeArcsOfDG trs' dps)

ndpairs trs@(((((idF, idC, idV, ar),os),strat),rm), rr) = (dptrs, dpairs1 ++ dpairs2)
    where dpairs1 = computeDepPairs trs
          dpairs2 = lDPairs  trs
          dptrs   = (((((idF', idC, idV, ar'),os),strat),rm), rr)
          idF'    = idF ++ map markNameDP idF
          ar'   f = fromMaybe (ar f) (lookup f [(markNameDP f, ar f) | f <- idF])

ncycles trs = let (trs', dps, cc) = ndepGraph trs in dcycles trs' (dps,cc)

lDPairs muTRS@((((sig@(_,constructors,variables,_),Nothing),_),_),rules) =
  [markRootDP l :-> markRootDP t |  l :-> _ <- rules, t@(F f _) <- subTerms l, f `notElem` constructors ]

dcycles muTRS@(((((_,_,_,ar),_),_),repMap),_) it@(dpairs, arcsOfDepGraph) = --(dpN,arcsN,sccsN,newMuTRS)
  let depGraph = graphDPs muTRS it
      cycs = filter (\list -> ((length list) > 1) || ((head list) `elem` (suc depGraph (head list)))) . cycles $ depGraph
  in cycs

graphDPs muTRS@(((((_,_,_,ar),_),_),repMap),_) (dpairs, arcsOfDepGraph) =
   mkUGraph [0..(length dpairs)-1] arcsOfDepGraph :: Gr () ()


findGroundAF :: MuTRS -> DP -> [AF]
findGroundAF muTRS@((((sig@(_,constructors,variables,_),Nothing),_),_),rules) dp@(l:->r) =
    snub . map (invariantExtraVars . invariantMarkedSymbs) $ (mkGround r)

  where mkGround t
          | isGround t  = []
          | F f tt <- t = (map (invert . joinAFs) . sequence . inhabiteds) [go f it | it <- zip [0..] tt]
          | isVar t     = error "mkGround: unreachable"
          where go f (i,t)
                   | isGround t   = []
                   | isVar t      = [[(f,[i])]]
                   | F f' tt <- t = [(f,[i])] : (map joinAFs . sequence . inhabiteds $ [go f' it | it <- zip [0..] tt])

        joinAFs :: [AF] -> AF
        joinAFs = map ((head *** concat) . unzip) . groupBy ((==) `on` fst) . sortBy (compare `on` snd) . concat
        invariantMarkedSymbs af = [ (f, pp) | (Just f, pp) <- map (first unDPSymbol) af] ++ af
        invert af    = [ (f, [0..getArity sig f - 1] \\ filtered) | (f,filtered) <- af ]
        invariantExtraVars af = [[(f, joinAFs (findGroundAF concat(maybeToList(lookup f pp)) ), (markNameDP f, pp) | l :-> r <- rules, let l' = applyAF l, let r' = applyAF r, 
                                    varsTerm r -!- varsTerm l, ]

---------------------------------------
-- Operations on terms
---------------------------------------
vars     = snub . foldTerm (\_ vv -> concat vv) (const []) (:[])
isGround = null . vars

unDPSymbol t | t == un_t = Nothing
             | otherwise = Just un_t
    where un_t  = unMarkIfNeccessary t

unmarkRule (l :-> r) = renameRoot (unMarkIfNeccessary (rootTerm l)) l :->
                       renameRoot (unMarkIfNeccessary (rootTerm r)) r


class ApplyAF t where applyAF :: AF -> t -> t

instance (ApplyAF a, ApplyAF b) => ApplyAF (a,b) where applyAF af (a,b)     = (applyAF af a, applyAF af b)
instance (Functor f, ApplyAF a) => ApplyAF (f a) where applyAF af = fmap (applyAF af)
instance ApplyAF RewRule                         where applyAF af (l :-> r) = applyAF af l :-> applyAF af r
instance ApplyAF Signature                       where applyAF af (idf,idc,idv,arity) = (idf,idc,idv, applyAF af arity)
instance ApplyAF OrderS {- HACK! not filtered-}  where applyAF af = id
instance ApplyAF Strat  {- HACK! not filtered-}  where applyAF af = id
instance ApplyAF RepMap {- HACK! not filtered-}  where applyAF af = id
instance ApplyAF Arity                           where applyAF af arfun f
                                                           | Just ii <- lookup f af = length ii
                                                           | otherwise              = arfun f
instance ApplyAF Problem                         where applyAF af (Problem typ trs dps) = Problem typ (applyAF af trs) (applyAF af dps)
instance ApplyAF Terms where
  applyAF af = foldTerm f C V
    where f n tt | Just ii <- lookup n af = F n (select tt ii)
                 | otherwise = F n tt

foldTerm f c v (C x) = c x
foldTerm f c v (V x) = v x
foldTerm f c v (F t tt) = f t (map (foldTerm f c v) tt)


----------------------
-- Utils
----------------------

inhabiteds = filter (not.null)

snub :: Ord a => [a] -> [a]
snub  = map head . group . sort

on cmp f x y = cmp (f x) (f y)

select xx ii = go 0 xx (sort ii)
    where go _ [] _ = []
          go _ _ [] = []
          go n (x:xx) (i:ii) | n == i = x : go (succ n) xx ii
                             | otherwise = go (succ n) xx (i:ii)

propSelect xx ii = map (xx!!) ii' == select xx ii'
  where types = (xx::[Int], ii::[Int])
        ii'   = filter (< length xx) (map abs ii)

-- Implementacion libre de:
--  "A new way to enumerate cycles in graph" - Hongbo Liu, Jiaxin Wang
--
-- TODO reimplementar liuwang con Data.Sequence
cycles :: Graph gr => gr a b -> [[Node]]
cycles gr = (snub  . map (sort . getNodes)) (concatMap liuwang [[(n,n)] | n <- nodes gr])
    where liuwang path = [ path ++ [closure] | let closure = (tpath, phead path), closure `elem` edges gr] ++
                        concatMap liuwang [path++[(tpath,n)] | n <- suc gr tpath, n /= hpath, (tpath,n) `notElem` path]
                                    where tpath = ptail path
                                          hpath = phead path
          phead = fst . head
          ptail = snd . last
          getNodes = snub . map fst

------------------------
-- Testing
------------------------
g = mkUGraph [1..3] [(1,1),(3,2),(2,1),(1,3)] :: Gr () ()


