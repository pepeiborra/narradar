{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverlappingInstances, TypeSynonymInstances, FlexibleInstances #-}

module Narradar.Framework.Ppr (module Narradar.Framework.Ppr, module Text.PrettyPrint.HughesPJClass) where

import Data.Array

import qualified Text.PrettyPrint.HughesPJClass as Ppr
import Text.PrettyPrint.HughesPJClass
                        ( Pretty(..), Doc, equals,
                          text, int, char, comma, colon, empty, render)

import Data.Term.Rules ()
import Data.Term.Ppr ()
import Data.Strict(Pair(..), (:!:))
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

instance (Pretty a, Pretty b) => Pretty (Pair a b) where pPrint (a:!:b) = pPrint (a,b)


(<+>) :: (Pretty a, Pretty b) => a -> b -> Doc
a <+> b = pPrint a Ppr.<+> pPrint b

(<>) :: (Pretty a, Pretty b) => a -> b -> Doc
a <> b = pPrint a Ppr.<> pPrint b

($$) :: (Pretty a, Pretty b) => a -> b -> Doc
a $$ b = pPrint a Ppr.$$ pPrint b

($+$) :: (Pretty a, Pretty b) => a -> b -> Doc
a $+$ b = pPrint a Ppr.$+$ pPrint b

vcat, cat, hcat, sep, hsep, fsep :: Pretty a => [a] -> Doc

hcat = Ppr.hcat . map pPrint
vcat = Ppr.vcat . map pPrint
cat  = Ppr.cat  . map pPrint

sep  = Ppr.sep  . map pPrint
fsep  = Ppr.fsep  . map pPrint
hsep  = Ppr.hsep  . map pPrint

parens, brackets :: Pretty a => a -> Doc
parens = Ppr.parens . pPrint
brackets = Ppr.brackets. pPrint

nest :: Pretty a => Int -> a -> Doc
nest i = Ppr.nest i . pPrint

punctuate :: (Pretty a, Pretty b) => a -> [b] -> [Doc]
punctuate c xx = Ppr.punctuate (pPrint c) (map pPrint xx)
