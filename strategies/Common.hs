{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PartialTypeSignatures #-}

module Common where

import Control.Monad
import Control.Monad.Free
import Control.Monad.Logic
import Control.Monad.Stream
import Control.Parallel.Strategies
import Control.Monad.Logic
import qualified Data.Foldable as F
import qualified Data.Traversable as T
import qualified Data.Term.Family as Family
import Narradar hiding (Strategy)
import Narradar.Processor.NonDP
import Narradar.Processor.RPO as RPO
import Narradar.Processor.WPO as WPO
import Debug.Hoed.Observe
import MuTerm.Framework.Proof

import Control.Exception
import System.IO
import GHC.Stack

-- main
#ifndef WEB
import Narradar.Interface.Cli
commonMain o =
   catchJust (\e -> if e == StackOverflow || e == UserInterrupt then Just e else Nothing)
            (narradarMain runStream o)
            (\e -> do
                 stack <- currentCallStack
                 putStrLn (if e == StackOverflow then "Stack overflow:" else "Interrupted:")
                 forM_ stack $ \l -> putStrLn ("  " ++ l)
                 throwIO e
            )
#else
import Narradar.Interface.Cgi
commonMain o = narradarCgi (id :: [a] -> [a]) o
#endif

{- Missing dispatcher cases -}
instance (IsProblem typ, Pretty typ) => Dispatch (Problem typ trs) where dispatch p = error("This version of Narradar does not handle DP problems of type " ++ show (pPrint $ getFramework p))

instance (IsProblem typ, Pretty typ) => Dispatch (Problem (NonDP typ) trs) where
    dispatch p = error ("This version of Narradar does not handle non-DP problems of type " ++ show (pPrint $ getBaseProblemFramework p))

{- Non DP problems -}

-- instance Dispatch (NProblem (NonDP Rewriting) Id) where dispatch = lfpBounded 8 (noRules `orElse` lpoMono2O) >=> final
instance (FrameworkProblem p (NTRS Id), GetPairs p, Dispatch (NProblem p Id)) => Dispatch (NProblem (NonDP p) Id) where dispatch = applyE ToDP >=> dispatch

{- Relative -}
instance (Dispatch (NProblem base id), GetPairs base
         ,FrameworkProblemN base id
         ,id ~ DPIdentifier id', Ord id'
         ) => Dispatch (NProblem (Relative (NTRS id) base) id) where
  dispatch = (applyE RelativeToRegularIPL14 `orElse1` applyE RegularImpliesRelative) >=> dispatch

instance Dispatch (NProblem (Relative (NTRS Id) Rewriting) Id) where   dispatch = applyE RelativeToRegularIPL14 >=> dispatch


{- Solvers -}
dg  = applyE DependencyGraphSCC{useInverse=False}
dgI = applyE DependencyGraphSCC{useInverse=True}

qrO p = gdmobservers "QRewriting" applyO RewritingToQRewriting p
qr p = applyE RewritingToQRewriting p
qshrink p = applyE ReduceQ p

sc = applyE SubtermCriterion
--dgsc p = lfp(dg >=> sc) p
ev    = applyE ExtraVarsP
evO p = gdmobservers "extra vars" applyO ExtraVarsP p
inn  = applyE ToInnermost >=> dispatch
innO = gdmobservers "innermost" applyO ToInnermost -- >=> dispatch
ur    = applyE UsableRules
narr = applyE (NarrowingP Nothing)
narrP p x = applyE (NarrowingP (Just p)) x
inst  = applyE Instantiation
rew   = applyE RewritingP
finst    = applyE FInstantiation
scO p = gdmobservers "Subterm criterion" applyO SubtermCriterion p
urO p = gdmobservers "Usable Rules" applyO UsableRules p
instO p = gdmobservers "Instantiation" applyO Instantiation p
finstO p = gdmobservers "Forward instantiation" applyO FInstantiation p
rewO p = gdmobservers "Rewriting" applyO RewritingP p
narrO = gdmobservers "Narrowing" applyO (NarrowingP Nothing)
dgO p = gdmobservers "Graph" applyO (DependencyGraphSCC False) p
lpo  = applyE (RPOProc RPO.LPOAF  All True)
mpo  = applyE (RPOProc MPOAF  Needed True)
lpos = applyE (RPOProc LPOSAF Needed True)
rpo  = applyE (RPOProc RPOAF  Needed True)
rpos = applyE (RPOProc RPOSAF All True)
lpoO p = gdmobservers "lpo" applyO (RPOProc RPO.LPOAF All True) p
rposO p = gdmobservers "rpos" applyO (RPOProc RPO.RPOSAF All True) p

max   = applyE (WPOReductionPair MAX  All)
lpoViaWpo = applyE (WPOReductionPair WPO.LPOAF All)
mpol x y  = applyE (WPOReductionPair (MPOL x y) All)
--mpolO p = gdmobservers "mpolO" applyO (WPOReductionPair MPOL All) p
msum  = applyE (WPOReductionPair MSUM All)
sum   = applyE (WPOReductionPair SUM  All)
kboaf = applyE (WPOReductionPair KBOAF All)

--monopolo = applyE (WPOReductionPair MONOPOLO All)

polo x y  = applyE (WPORuleRemoval (POLO (Just x) (Just y)))
poloU = applyE (WPORuleRemoval (POLO (Just 0) Nothing))
--poloO p = gdmobservers "polo" applyO (WPORuleRemoval POLO) p
kbo  = applyE (WPORuleRemoval KBO )
tkbo = applyE (WPORuleRemoval TKBO)
lpoMono = applyE (WPORuleRemoval LPO)

lpoMono2 = applyE (RPORuleRemoval RPO.LPOAF)
lpoMono2O p = gdmobservers "LPO mono" applyO (RPORuleRemoval RPO.LPOAF) p
rpoMono2 = applyE (RPORuleRemoval RPO.RPOAF)
lposMono = applyE (RPORuleRemoval RPO.LPOSAF)
rposMono = applyE (RPORuleRemoval RPO.RPOSAF)

noRules = applyE NoRules

rpoPlus transform
   = repeatSolver 1 ((lpoO .|. rpos .|. transform) >=> dg)

rpoPlusPar transform = withStrategy parallelize . f where
 f = repeatSolver 5 ( (lpo.||. rpos .||. transform) >=> dg)
  where
    lpo  = applyE (RPOProc RPO.LPOAF  Needed True)
    rpos = applyE (RPOProc RPOSAF Needed True)
 
--gt1 = rew `orElse` (narr .||. finst .||. inst)
gt1 = rew `orElse1` (inst `orElse1` narr) -- `orElse` finst
gt2 = narr .||. finst .||. inst

-- parOrF  s other = return other

-- Explicit type signature for commonMain to ensure coherent type class selection
commonMain :: (trs ~ NTRS Id, t ~ TermF Id
                    ,Dispatch (Problem Rewriting  trs)
                    ,Dispatch (Problem IRewriting trs)
                    ,Dispatch (Problem (NonDP Rewriting)  trs)
                    ,Dispatch (Problem (NonDP IRewriting)  trs)
                    ,Dispatch (Problem (QRewriting (Family.TermF trs))  trs)
                    ,Dispatch (Problem (InitialGoal t Rewriting) trs)
                    ,Dispatch (Problem (InitialGoal t IRewriting) trs)
                    ,Dispatch (Problem (Relative  trs (InitialGoal t Rewriting))  trs)
                    ,Dispatch (Problem (Relative  trs (InitialGoal t IRewriting))  trs)
                    ,Dispatch (Problem (Relative  trs Rewriting)  trs)
                    ,Dispatch (Problem (Relative  trs IRewriting)  trs)
                    ,Dispatch (Problem (NonDP (Relative  trs Rewriting))  trs)
                    ,Dispatch (Problem (NonDP (Relative  trs IRewriting)) trs)
                    ,Dispatch (Problem Narrowing  trs)
                    ,Dispatch (Problem CNarrowing trs)
                    ,Dispatch (Problem (InitialGoal t Narrowing) trs)
                    ,Dispatch (Problem (InitialGoal t INarrowing) trs)
                    ,Dispatch PrologProblem
                    ) => Observer -> IO ()
