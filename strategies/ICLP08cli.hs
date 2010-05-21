#!/usr/bin/env runhaskell

import Data.Maybe (listToMaybe)
import ICLP08
import Narradar.Interface.Cli

main = narradarMain listToMaybe
