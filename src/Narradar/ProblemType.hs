{-# LANGUAGE TypeSynonymInstances, TemplateHaskell #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE CPP #-}
module Narradar.ProblemType where

import Control.Applicative
import Data.DeriveTH
import Data.Derive.Foldable
import Data.Derive.Functor
import Data.Derive.Traversable
import Data.Foldable (Foldable(..))
import Data.Traversable (Traversable(..))
import Data.Maybe
import Prelude hiding (pi)
import Text.PrettyPrint

import Narradar.Utils
import Narradar.ArgumentFiltering

import qualified Language.Prolog.Syntax as Prolog hiding (ident)
import qualified Language.Prolog.TypeChecker as Prolog
import qualified Language.Prolog.Parser as Prolog

#ifdef HOOD
import Debug.Observe
#endif

type ProblemType id = ProblemTypeF (AF_ id)

data ProblemTypeF pi   = Rewriting   | InnermostRewriting
                       | Narrowing   | NarrowingModes   {pi, goal::pi}
                       | GNarrowing  | GNarrowingModes  {pi, goal::pi}
                       | BNarrowing  | BNarrowingModes  {pi, goal::pi}
                       | LBNarrowing | LBNarrowingModes {pi, goal::pi}
	               | Prolog {goals::[AF_ String], program::Prolog.Program}
                    deriving (Eq, Show)

instance Ppr (ProblemType id) where
    ppr Prolog{}                  = text "Prolog"
    ppr typ | isFullNarrowing typ = text "NDP"
    ppr typ | isGNarrowing    typ = text "Ground NDP"
    ppr typ | isBNarrowing    typ = text "BNDP"
    ppr typ | isRewriting     typ = text "DP"

isAnyNarrowing = isFullNarrowing .|. isBNarrowing .|. isGNarrowing

isRewriting Rewriting =True; isRewriting InnermostRewriting = True; isRewriting _ = False

isInnermostRewriting InnermostRewriting = True; isInnermostRewriting _ = False

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

isLeftStrategy LBNarrowingModes{} = True; isLeftStrategy _ = False

--isModed = isJust . getGoalAF

getProblemAF = getGoalAF
getGoalAF NarrowingModes{pi}   = Just pi
getGoalAF BNarrowingModes{pi}  = Just pi
getGoalAF GNarrowingModes{pi}  = Just pi
getGoalAF LBNarrowingModes{pi} = Just pi
getGoalAF _ = Nothing

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