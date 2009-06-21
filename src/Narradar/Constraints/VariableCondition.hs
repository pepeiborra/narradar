{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
module Narradar.Constraints.VariableCondition where

import Control.Applicative
import Control.Exception (assert)
import Control.Monad.Fix (fix)
import Control.RMonad
import Data.Set (Set)
import qualified Data.Set as Set

import Narradar.Types.ArgumentFiltering
import Narradar.Types.Term
import Narradar.Types.Var
import Narradar.Utils.Ppr

import Lattice

import Prelude hiding (Monad(..))

-- --------------------
-- Variable Condition
-- --------------------

invariantEV :: ( Ppr id, Ord id, Lattice (AF_ id), HasRules (TermF id) Var trs
               , ExtraVars v trs, ApplyAF trs id) =>
               Heuristic id (TermF id) -> trs -> AF_ id -> Set (AF_ id)
invariantEV heu trs pi = let pi' = (selectBest . Set.toList . fix subinvariantEV) pi
                         in assert (all (`isSoundAF` trs) pi') (Set.fromList pi')
  where
        subinvariantEV f af
                | null extra = return af
                | otherwise  = foldM cutEV af (rules trs) >>= f
              where extra = extraVars (apply af trs)
        cutEV af rule@(_:->r)
            | orig_poss <- noteV <$> extraVars (apply af (annotateWithPos <$> rule))
            = cutWith heu af r orig_poss


--cutWith :: (Ppr id, Ord id) => Heuristic id t -> AF_ id -> TermN id v -> [Position] -> Set.Set (AF_ id)
cutWith _   af _ [] = return af
cutWith heu af t pp = foldM (\af' pos -> (runHeu heu af' t pos >>= \(f,p) ->
--                           trace ("term: " ++ show(ppr t) ++ ", pos: " ++ show pos ++ ", symbol:" ++ show (ppr f) ++ ", i: " ++ show p) $
                             return$ cut f p af'))
                            af pp
--cutWith heu af t pp = mconcat `liftM` (mapM (heu af t >=> \(f,p) -> return$ cut f p af) pp)
