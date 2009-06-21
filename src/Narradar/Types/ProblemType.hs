{-# LANGUAGE TypeSynonymInstances, TemplateHaskell #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module Narradar.Types.ProblemType where

import Control.Applicative
import Data.DeriveTH
import Data.Derive.Foldable
import Data.Derive.Functor
import Data.Derive.Traversable
import Data.Foldable (Foldable(..))
import Data.Traversable (Traversable(..))
import Data.Maybe
import Data.Monoid
import Prelude hiding (pi)
import Text.PrettyPrint

import Narradar.Types.ArgumentFiltering as AF
import Narradar.Types.Goal
import Narradar.Types.DPIdentifiers
import Narradar.Types.Term
import Narradar.Utils
import Narradar.Utils.Convert
import Narradar.Utils.Ppr (Ppr)

import qualified Language.Prolog.Syntax as Prolog hiding (ident)

#ifdef HOOD
import Debug.Observe
#endif

type ProblemType id = ProblemTypeF (AF_ id)

data ProblemTypeF pi   = Rewriting   | InnermostRewriting
                       | Narrowing   | NarrowingModes   {pi, goal::pi}
                       | GNarrowing  | GNarrowingModes  {pi, goal::pi}
                       | BNarrowing  | BNarrowingModes  {pi, goal::pi}
                       | LBNarrowing | LBNarrowingModes {pi, goal::pi}
	               | Prolog {goals::[AF_ String], program::Prolog.Program String}
                    deriving (Eq, Ord, Show)

narrowingModes,bNarrowingModes,gNarrowingModes :: HasSignature sig String => sig -> Goal -> ProblemType Id
narrowingModes sig goal  = NarrowingModes { goal = AF.extendToTupleSymbols afG
                                          , pi   = AF.extendToTupleSymbols (AF.init sig `mappend` afG) }
    where afG = mkGoalAF goal
bNarrowingModes sig goal  = BNarrowingModes { goal = AF.extendToTupleSymbols afG
                                          , pi   = AF.extendToTupleSymbols (AF.init sig `mappend` afG) }
    where afG = mkGoalAF goal
gNarrowingModes sig goal  = GNarrowingModes { goal = AF.extendToTupleSymbols afG
                                          , pi   = AF.extendToTupleSymbols (AF.init sig `mappend` afG) }
    where afG = mkGoalAF goal

instance Ppr (ProblemType id) where
    ppr Prolog{}                  = text "Prolog"
    ppr typ | isFullNarrowing typ = text "NDP"
    ppr typ | isGNarrowing    typ = text "Ground NDP"
    ppr typ | isBNarrowing    typ = text "BNDP"
    ppr typ | isRewriting     typ = text "DP"

instance (Convert id id', Ord id') => Convert (ProblemType id)  (ProblemType id') where convert = fmap convert

isAnyNarrowing = isFullNarrowing .|. isBNarrowing .|. isGNarrowing

isRewriting Rewriting =True; isRewriting InnermostRewriting = True; isRewriting _ = False

isInnermostRewriting InnermostRewriting = True; isInnermostRewriting _ = False
isInnermostLike InnermostRewriting = True
isInnermostLike x = isGNarrowing x

isFullNarrowing Narrowing{} = True
isFullNarrowing NarrowingModes{} = True
isFullNarrowing _ = False

isBNarrowing BNarrowing{}  = True
isBNarrowing LBNarrowing{} = True
isBNarrowing BNarrowingModes{} = True
isBNarrowing LBNarrowingModes{} = True
isBNarrowing _ = False

isGNarrowing GNarrowing{}  = True
isGNarrowing GNarrowingModes{} = True
isGNarrowing _ = False

isProlog Prolog{} = True ; isProlog _ = False

isLeftStrategy LBNarrowingModes{} = True; isLeftStrategy _ = False

getAF NarrowingModes{pi}   = Just pi
getAF BNarrowingModes{pi}  = Just pi
getAF GNarrowingModes{pi}  = Just pi
getAF LBNarrowingModes{pi} = Just pi
getAF _                    = Nothing

getGoalAF NarrowingModes{goal}   = Just goal
getGoalAF BNarrowingModes{goal}  = Just goal
getGoalAF GNarrowingModes{goal}  = Just goal
getGoalAF LBNarrowingModes{goal} = Just goal
getGoalAF _ = Nothing

isModed = isJust . getGoalAF

narrowingModes0 =   NarrowingModes  {goal=error "narrowingModes0", pi=error "narrowingModes0"}
bnarrowingModes0 =  BNarrowingModes {goal=error "bnarrowingModes0", pi=error "bnarrowingModes0"}
gnarrowingModes0 =  GNarrowingModes {goal=error "gnarrowingModes0", pi=error "gnarrowingModes0"}
lbnarrowingModes0 = LBNarrowingModes{goal=error "lbnarrowingModes0", pi=error "lbnarrowingModes0"}

$(derive makeFunctor     ''ProblemTypeF)
$(derive makeFoldable    ''ProblemTypeF)
$(derive makeTraversable ''ProblemTypeF)

#ifdef HOOD
instance Show a => Observable (ProblemTypeF a) where observer = observeBase
#endif
