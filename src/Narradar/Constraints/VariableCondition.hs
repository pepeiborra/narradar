{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE Rank2Types #-}
module Narradar.Constraints.VariableCondition where

import Control.Applicative
import Control.Exception (assert)
import Control.Monad.Fix (fix)
import Control.RMonad
import Data.Foldable (Foldable)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable (Traversable)

import Narradar.Types.ArgumentFiltering
import Narradar.Types.Term
import Narradar.Types.Var
import Narradar.Framework.Ppr

import Lattice

import Prelude hiding (Monad(..))

import qualified Data.Term.Family as Family

-- --------------------
-- Variable Condition
-- --------------------

invariantEV :: --forall id t v trs.
               ( id ~ Family.Id1 t
               , Traversable t, HasId t
               , Pretty id, Ord id, Lattice (AF_ id)
               , Ord v
               , ApplyAF (Term t v)
               , ApplyAF (Term (WithNote1 Position t) (WithNote Position v))
               ) =>
               Heuristic id -> [Rule t v] -> AF_ id -> Set (AF_ id)

invariantEV heu trs pi = let pi' = (selectBest . Set.toList . fix subinvariantEV) pi
                         in assert (all (`isSoundAF` trs) pi') (Set.fromList pi')
  where
        subinvariantEV f af
                | null extra = return af
                | otherwise  = foldM cutEV af trs >>= f
              where extra = extraVars (apply af trs)

--        cutEV :: AF_ id -> Rule t v -> Set (AF_ id)
        cutEV af rule@(_:->r)
            | orig_poss <- noteV <$> extraVars (apply af (annotateWithPos <$> rule))
            = cutWith heu af r orig_poss


cutWith :: (id ~ Id1 t, Pretty id, Ord id, Foldable t, HasId t) => Heuristic id -> AF_ id -> Term t v -> [Position] -> Set (AF_ id)
cutWith _   af _ [] = return af
cutWith heu af t pp = foldM (\af' pos -> (runHeu heu af' t pos >>= \(f,p) ->
--                           trace ("term: " ++ show(ppr t) ++ ", pos: " ++ show pos ++ ", symbol:" ++ show (ppr f) ++ ", i: " ++ show p) $
                             return$ cut f p af'))
                            af pp
