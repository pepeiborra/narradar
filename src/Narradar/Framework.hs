{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs #-}

module Narradar.Framework (
        module Narradar.Framework,
        module MuTerm.Framework.Problem,
        module MuTerm.Framework.Processor,
        module MuTerm.Framework.Proof,
        module MuTerm.Framework.Strategy)
  where

import Control.Monad
import Data.Foldable (toList)
import Data.Term (foldTerm, getId)

import MuTerm.Framework.DotRep
import MuTerm.Framework.Problem
import MuTerm.Framework.Processor
import MuTerm.Framework.Proof
import MuTerm.Framework.Strategy

import Narradar.Framework.Ppr
import Narradar.Utils ((<$$>))

-- ----------------------
-- Framework extensions
-- ----------------------

class FrameworkExtension ext where
    getBaseFramework :: ext base -> base
    getBaseProblem   :: Problem (ext base) trs -> Problem base trs
    setBaseProblem   :: Problem base trs -> Problem (ext base) trs ->  Problem (ext base) trs
    liftProcessor    :: ( Processor info tag (Problem base trs) (Problem base trs)
                        , Info info (Problem base trs)
                        , MonadPlus m
                        ) =>
                        tag -> Problem (ext base) trs -> Proof info m (Problem (ext base) trs)
    liftProcessorS :: ( Processor info tag (Problem base trs) (Problem base trs)
                     , Info info (Problem base trs)
                     , MonadPlus m
                     ) => tag -> Problem (ext base) trs -> [Proof info m (Problem (ext base) trs)]

    liftProcessor tag p = do
      p' <- apply tag (getBaseProblem p)
      return (setBaseProblem p' p)

    liftProcessorS tag p = (`setBaseProblem` p) <$$> applySearch tag (getBaseProblem p)

liftFramework :: FrameworkExtension ext =>
                     (Problem base trs -> Problem base trs) -> Problem (ext base) trs -> Problem (ext base) trs
liftFramework f p = setBaseProblem (f(getBaseProblem p)) p

-- ---------- --
-- Strategies --
-- ---------- --

data Standard
data Innermost
data Strategy st where
    Standard  :: Strategy Standard
    Innermost :: Strategy Innermost

class IsDPProblem typ => HasStrategy typ st | typ -> st where
  getStrategy :: typ -> Strategy st

instance (FrameworkExtension ext, IsDPProblem (ext b), HasStrategy b st) => HasStrategy (ext b) st where
  getStrategy = getStrategy . getBaseFramework

-- ---------- --
-- Minimality --
-- ---------- --

data Minimality  = M | A   deriving (Eq, Ord, Show)

class IsDPProblem typ => HasMinimality typ where
  getMinimality :: typ -> Minimality
  setMinimality :: Minimality -> Problem typ trs -> Problem typ trs

getMinimalityFromProblem :: HasMinimality typ => Problem typ trs -> Minimality
getMinimalityFromProblem = getMinimality . getProblemType

instance (IsDPProblem (p b), HasMinimality b, FrameworkExtension p) => HasMinimality (p b)
   where getMinimality = getMinimality . getBaseFramework
         setMinimality m = liftFramework (setMinimality m)

-- -------------
-- forDPProblem
-- -------------

forDPProblem f p = f (getProblemType p) (getR p) (getP p)

-- -------------------------
-- printing TPDB problems --
-- -------------------------

class PprTPDB p where pprTPDB :: p -> Doc


pprTermTPDB t = foldTerm pPrint f t where
        f t@(getId -> Just id)
            | null tt = pPrint id
            | otherwise = pPrint id <> parens (hcat$ punctuate comma tt)
         where tt = toList t
