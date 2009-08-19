{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverlappingInstances, TypeSynonymInstances #-}

module Narradar.Framework.Ppr (Ppr(..), module Text.PrettyPrint) where

import MuTerm.Framework.Ppr
import Language.Prolog.Syntax ()
import Text.PrettyPrint ( Doc, (<>), (<+>), ($$), vcat, cat, hcat, sep, hsep, fsep,
                          text, int, char, parens, punctuate, comma, nest, colon)

import Data.Map as Map (Map, toList)
import Data.Set as Set (Set, toList)

import Data.Term
import Data.Term.Rules
import qualified Data.Term.Ppr as Term

import qualified Language.Prolog.Syntax as Prolog



instance (Ppr (f(Free f a)), Ppr a) => Ppr (Term f a) where
    ppr (Impure t) = ppr t; ppr (Pure a) = ppr a
instance Ppr a => Ppr (RuleF a) where
    ppr (l :-> r) = ppr l <+> text "->" <+> ppr r
instance Ppr a => Ppr (EqModulo a) where ppr = ppr . eqModulo
instance (Ppr var, Ppr (Free termF var)) => Ppr (Substitution termF var) where
    ppr = braces . hcat . punctuate comma . map (\(v,t) -> ppr v <+> equals <+> ppr t) . Map.toList . unSubst


instance Ppr a => Ppr [a] where
    ppr = brackets . hcat . punctuate comma . map ppr
    pprDebug = brackets . hcat . punctuate comma . map pprDebug

instance Ppr a => Ppr (Set a)            where ppr = braces   . hcat . punctuate comma . map ppr . Set.toList
instance (Ppr k, Ppr a) => Ppr (Map k a) where
    ppr m = vcat$ concat [[ppr k, nest 2 (ppr v)] | (k,v) <-  Map.toList m]
instance (Ppr a, Ppr b) => Ppr (Either a b) where ppr = either ppr ppr


instance Term.Ppr (Prolog.ClauseF a) => Ppr (Prolog.ClauseF a) where ppr = Term.ppr
instance Term.Ppr (Prolog.GoalF id a) => Ppr (Prolog.GoalF id a) where ppr = Term.ppr


-- instance Ppr a => Term.Ppr a where ppr = ppr