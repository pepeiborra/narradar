#!/usr/bin/env runhaskell

import Data.Maybe (listToMaybe)
import SGST07
import Narradar.Interface.Cli

main = narradarMain listToMaybe
