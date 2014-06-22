module Narradar.Utils.Memo where

import Control.Concurrent.MVar
import qualified Data.Map as M
import System.IO.Unsafe(unsafePerformIO)

import Narradar.Framework.Ppr
import Narradar.Utils

-- Code below is extracted from the uglymemo package

-- | Memoize the given function by allocating a memo table,
-- and then updating the memo table on each function call.
memoIO :: (Ord a, Pretty a)
       => (a -> b)           -- ^Function to memoize
       -> IO (a -> IO b)
memoIO f = do
    v <- pprTrace "Allocating new memoization table" $ newMVar (0::Int, M.empty)
    let f' x = do
            (version, m) <- pprTrace "reading memoization table" $ readMVar v
            case M.lookup x m of
                Nothing -> do
                  let r = f x
                  pprTrace ("Inserting new entry in memoization table" <+>
                            parens("version" <+> version <> comma <+> "size" <+> M.size m)
                           ) $ return ()
                  modifyMVar_ v $ \m' -> do
                     let m' = M.insert x r m
                         v' = version + 1
                     return (v',m')
                  (v',m') <- readMVar v
                  pprTrace ("Inserted new entry in memoization table" <+>
                               parens("version" <+> v' <> comma <+> "size" <+> M.size m')
                              ) $ return ()
                  return r
                Just r  ->
                  pprTrace ("Reusing a result in memoization table" <+>
                            parens("version" <+> version <> comma <+> "size" <+> M.size m)
                           ) $ return r
    return f'

-- | The pure version of 'memoIO'.
{-# NOINLINE memo #-}
{-# NOINLINE memoIO #-}
memo :: (Ord a, Pretty a)
     => (a -> b)           -- ^Function to memoize
     -> (a -> b)
memo f = let f' = unsafePerformIO (memoIO f) in \ x -> unsafePerformIO (f' x)
