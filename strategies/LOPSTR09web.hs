#!/usr/bin/env runhaskell

import Data.Maybe (listToMaybe)
import LOPSTR09
import Narradar.Interface.Cgi

main = narradarCgi listToMaybe
