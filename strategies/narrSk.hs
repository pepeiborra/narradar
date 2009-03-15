#!/usr/bin/env runhaskell

{-# LANGUAGE NoImplicitPrelude #-}
import Prelude hiding (Monad(..))

import Narradar
import Narradar.PrologProblem
import Language.Prolog.Parser as Prolog

main = getContents >=> parse Prolog.program >=> print . skTransform
