{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances, FlexibleContexts, FlexibleInstances #-}
module Narradar.Framework (
        module Narradar.Framework,
        module MuTerm.Framework.DotRep,
        module MuTerm.Framework.Problem,
        module MuTerm.Framework.Processor,
        module MuTerm.Framework.Proof,
        module MuTerm.Framework.Strategy)
  where

import Control.Monad

import MuTerm.Framework.DotRep
import MuTerm.Framework.Problem
import MuTerm.Framework.Processor
import MuTerm.Framework.Proof
import MuTerm.Framework.Strategy

import Narradar.Framework.Ppr
import Narradar.Utils ((<$$>))


class Dispatch thing where
    dispatch :: MonadPlus m => thing -> Proof (PrettyInfo, DotInfo) m ()

class FrameworkExtension typ where
    getBaseFramework :: typ typ' -> typ'
    getBaseProblem   :: Problem (typ typ') trs -> Problem typ' trs
    setBaseProblem   :: Problem typ' trs -> Problem (typ typ') trs ->  Problem (typ typ') trs
    liftProcessor    :: ( Processor info tag (Problem base trs) (Problem base trs)
                        , Info info (Problem base trs)
                        , MonadPlus m
                        ) =>
                        tag -> Problem (typ base) trs -> Proof info m (Problem (typ base) trs)
    liftProcessorS :: ( Processor info tag (Problem base trs) (Problem base trs)
                     , Info info (Problem base trs)
                     , MonadPlus m
                     ) => tag -> Problem (typ base) trs -> [Proof info m (Problem (typ base) trs)]

    liftProcessor tag p = do
      p' <- apply tag (getBaseProblem p)
      return (setBaseProblem p' p)

    liftProcessorS tag p = (`setBaseProblem` p) <$$> applySearch tag (getBaseProblem p)

mkDispatcher :: Monad m => (a -> Proof info m b) ->  a -> Proof info m ()
mkDispatcher f = fmap (const ()) . f

