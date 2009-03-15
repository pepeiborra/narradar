#!/usr/bin/env runhaskell

{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators #-}

import Prelude hiding (Monad(..))
import qualified Prelude
import Narradar
import Narradar.PrologProblem
import Narradar.PrologIdentifiers
import Narradar.Utils
import qualified Narradar.ArgumentFiltering as AF
import Debussy.Hanus hiding (main)
import System.Environment

import TRS.Bottom
import Debussy.TermK

type PointedPS = Var :+: T PS :+: Hole :+: Bottom :+: VarK
instance HashConsed PointedPS

main :: IO ()
main = go $ do
  [file] <- getArgs
  Problem Prolog{..} _ _  <- readFile file >>= parsePrologProblem :: IO PrologProblem
  let trs  = skTransform program
      the_goals =
                [ term (InId f) vars
                     | pi <- goals
                     , (f,_) <- AF.toList pi
                     , let vars = take (getArity trs (InId f)) (repeat varK :: [Term PointedPS])]
      ints = tpInterpretations_abs 20 (reinject <$$> rules trs) the_goals
  printInts ints :: IO ()
  return ()

printInts (i:ii) = go $ do
                            print i
                            c <- getChar
                            case c of
                              'q' -> returnM () :: IO ()
                              _   -> putStr "\n" >> printInts ii

instance Show e => Bind (Either e) IO IO where e >>= iof = eitherIO e >>= iof
instance Show e => Bind IO (Either e) IO where io >>= fe = io >>= eitherIO . fe