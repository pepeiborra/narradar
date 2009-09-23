{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Narradar.Utils.Html (module Narradar.Utils.Html, module H, module MuTerm.Framework.Output) where

import Data.HashTable (hashString)
import Text.XHtml as H (HTML(..), thediv, identifier, thestyle, hotlink, theclass, thespan, renderHtml, (<<), (+++), (!), p)

import MuTerm.Framework.Output

thickbox thing c | label <- hashHtml thing =
         thediv ! [H.identifier ("tb"++label), H.thestyle "display:none"] << p << thing +++
         H.hotlink ("#TB_inline?height=600&width=600&inlineId=tb" ++ label) ! [theclass "thickbox"] << c

hashHtml = show . abs . hashString . H.renderHtml