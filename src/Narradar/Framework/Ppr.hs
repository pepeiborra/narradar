{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverlappingInstances, TypeSynonymInstances #-}

module Narradar.Framework.Ppr (module Text.PrettyPrint.HughesPJClass) where

import Text.PrettyPrint.HughesPJClass
                        ( Pretty(..), Doc, (<>), (<+>), ($$), vcat, cat, hcat, sep, hsep, fsep, equals,
                          text, int, char, parens, punctuate, comma, nest, colon, empty, render)

import Data.Term.Rules ()
import Data.Term.Ppr ()
import Language.Prolog.Syntax ()




--instance Ppr a => Term.Ppr a where ppr = ppr