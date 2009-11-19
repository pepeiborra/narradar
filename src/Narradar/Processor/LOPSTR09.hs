{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, OverlappingInstances, TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

module Narradar.Processor.LOPSTR09 where

import Control.Applicative
import Control.Monad
import qualified Data.Set as Set
import Data.Traversable (Traversable)
import Lattice

import Language.Prolog.Representation hiding (addMissingPredicates)

import Narradar.Constraints.VariableCondition
import Narradar.Framework
import Narradar.Types
import Narradar.Types.ArgumentFiltering (AF_, ApplyAF, PolyHeuristic, MkHeu(..),mkHeu)
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types.Problem.Infinitary as Infinitary
import Narradar.Processor.PrologProblem hiding (SKTransformProof)

instance Pretty SKTransformProof where
  pPrint SKTransformProof
      = text "Transformed into an initial goal narrowing problem" $$
        text "(Schneider-Kamp transformation)"

instance Pretty id => Pretty (InfinitaryToRewritingProof id) where
    pPrint InfinitaryToRewritingFail = text "Failed to find a safe argument filtering"

    pPrint (InfinitaryToRewritingProof af) = text "Termination of the following rewriting DP problem implies" <+>
                                               text "termination of the original problem (FLOPS08)." $$
                                               text "The argument filtering used is:" $$
                                               pPrint af


-- SK Transform
-- ------------

data SKTransform = SKTransform
instance Info info SKTransformProof =>
         Processor info SKTransform
                   PrologProblem {- ==> -} (NProblem (NarrowingGoal DRP) DRP)
 where
  apply SKTransform p0@PrologProblem{..} =
   andP SKTransformProof p0
     [ mkNewProblem (narrowingGoal (IdDP <$> skTransformGoal goal)) sk_p
         | let sk_p = prologTRS'' rr (getSignature rr)
               rr   = skTransformWith id (prepareProgram $ addMissingPredicates program)
         , goal    <- goals
     ]
data SKTransformProof = SKTransformProof
  deriving (Eq, Show)

data SKTransformInf heu = SKTransformInf (MkHeu heu)
instance (Info info SKTransformProof
         ,PolyHeuristic heu DRP
         ) =>
         Processor info (SKTransformInf heu)
                   PrologProblem {- ==> -} (NProblem (Infinitary DRP Rewriting) DRP)
 where
  apply (SKTransformInf heu) p0@PrologProblem{..} =
   andP SKTransformProof p0 =<< sequence
     [  msum (map return probs)
         | goal    <- goals
         , let probs = mkDerivedInfinitaryProblem (IdDP <$> skTransformGoal goal) heu (mkNewProblem rewriting sk_p)
     ]
    where
       sk_p = prologTRS'' rr (getSignature rr)
       rr   = skTransformWith id (prepareProgram $ addMissingPredicates program)

-- Solving narrowing as infinitary problems
-- -----------------------------------------
data InfinitaryToRewriting heu = InfinitaryToRewriting (MkHeu heu)
instance (t   ~ TermF id
         ,v   ~ Var
         ,trs ~ NTRS id
         ,HasSignature (NProblem typ id), id ~ SignatureId (NProblem typ id)
         ,ICap t v (typ, trs), IUsableRules t v typ trs
         ,PolyHeuristic heu id, Lattice (AF_ id), Ord id, Pretty id
         ,MkDPProblem typ (NTRS id), Traversable (Problem typ)
         ,ApplyAF (NProblem typ id)
         ,Info info (InfinitaryToRewritingProof id)
         ) =>
    Processor info (InfinitaryToRewriting heu)
              (NProblem (Infinitary id typ) id)
              (NProblem typ id)
  where
  applySearch (InfinitaryToRewriting mk) p
    | null orProblems = [dontKnow (InfinitaryToRewritingFail :: InfinitaryToRewritingProof id) p]
    | otherwise = orProblems
   where
     orProblems = do
       let heu = mkHeu mk p
           base_p = getProblemType (Infinitary.baseProblem p)
       af' <-  Set.toList $ invariantEV heu p (Infinitary.pi p)
       let p' = mkDerivedDPProblem base_p p
       return $ singleP (InfinitaryToRewritingProof af') p (AF.apply af' p')

data InfinitaryToRewritingProof id where
    InfinitaryToRewritingProof :: AF_ id -> InfinitaryToRewritingProof id
    InfinitaryToRewritingFail  :: InfinitaryToRewritingProof id
