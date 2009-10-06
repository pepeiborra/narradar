{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverlappingInstances, TypeSynonymInstances, FlexibleInstances #-}

module Narradar.Framework.Ppr (module Text.PrettyPrint.HughesPJClass) where

import Data.Array

import Text.PrettyPrint.HughesPJClass
                        ( Pretty(..), Doc, (<>), (<+>), ($$), ($+$), vcat, cat, hcat, sep, hsep, fsep, equals,
                          text, int, char, parens, brackets, punctuate, comma, nest, colon, empty, render)

import Data.Term.Rules ()
import Data.Term.Ppr ()
import Language.Prolog.Syntax ()


instance (Ix i, Ix j, Enum i, Enum j, Pretty a) => Pretty (Array (i,j) a) where
    pPrint a = vcat [ hsep [ pPrint (a ! (x,y))
                                 | y <- [min_y..max_y]]
                      | x <- [min_x .. max_x]]
     where
       ((min_x,min_y), (max_x,max_y)) = bounds a

instance (Ix i, Ix j, Enum i, Enum j) => Pretty (Array (i,j) String) where
    pPrint a = vcat [ hsep [ text (a ! (x,y))
                                 | y <- [min_y..max_y]]
                      | x <- [min_x .. max_x]]
     where
       ((min_x,min_y), (max_x,max_y)) = bounds a
