module Narradar.Utils.Ppr (Ppr(..), module Text.PrettyPrint) where

import Data.Term.Ppr
import Language.Prolog.Syntax ()
import Text.PrettyPrint ( Doc, (<>), (<+>), ($$), vcat, cat, hcat, sep, fsep,
                          text, int, char, parens, punctuate, comma)