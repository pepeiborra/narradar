
module TaskPoolSTM ( parSequence, parSequence', parSequence_
                   , parMapM, parMapM_, parMapM', parMapMS_
                   , parForM, parForM_, parForM', parForMS_
                   ) where

import Operad

import Control.Concurrent
import Control.Concurrent.Chan
import Control.Concurrent.MVar
import Control.Concurrent.STM
import Control.Exception as CE
import Control.Monad
import Control.Monad.STM
import System.IO


data Job a = Job a | Done
data Res a = Suc a | Failed

tasksdebug :: String -> IO ()
tasksdebug = hPutStrLn stderr . ("TASKS - " ++) -- debugM "TASKS"

-- | Blocks until all the elements have been processed
parSequence :: Int -> [IO a] -> IO [a]
parSequence n jobs = do
  results_c <- parSequence' n jobs
  results   <- atomically $ replicateM (length jobs) (readTChan results_c)
  return [ r | Suc r <- results ]
{-
parSequenceT :: Traversable t => Int -> t(IO a) -> IO (t a)
parSequenceT n t = do
  let comp = asComp t
-}

-- | non-blocking version
parSequence' :: Int -> [IO b] -> IO (TChan (Res b))
parSequence' n jobs = do
  jobqueue  <- newTChanIO
  results_c <- newTChanIO
  forkTimes n (worker jobqueue results_c)
  atomically $ do mapM_ (writeTChan jobqueue . Job) jobs
                  replicateM_ n (writeTChan jobqueue Done)
  return results_c

parSequence_ :: Int -> [IO a] -> IO ()
parSequence_ n jobs = do
  jobqueue <- newTChanIO
  workers  <- newTVarIO n
  replicateM_ n $ forkWorker workers (worker_ jobqueue)
  atomically $ do mapM_ (writeTChan jobqueue . Job) jobs
                  replicateM_ n (writeTChan jobqueue Done)
  waitFor workers


parSequenceS_ :: [state] -> [state -> IO a] -> IO ()
parSequenceS_ states0 jobs = do
  let n = length states0
  jobqueue <- newTChanIO
  workers  <- newTVarIO n
  forM states0 $ \s0 -> forkWorker workers (workerS_ s0 jobqueue)
  atomically $ do mapM_ (writeTChan jobqueue . Job) jobs
                  replicateM_ n (writeTChan jobqueue Done)
  waitFor workers

forkTimes  k act = replicateM_ k $ forkIO act
forkWorker count act = forkIO $ act
                          `finally`
                         (atomically $ modifyTVar_ count pred)

modifyTVar_ tv f = readTVar tv >>= writeTVar tv . f

worker jobqueue results_c = loop where
 loop = do
         job <- atomically $ readTChan jobqueue
         case job of
           Done  -> return ()
           Job x -> do (x >>= atomically . writeTChan results_c . Suc)
                             `CE.catch` \e -> atomically (writeTChan results_c Failed) >>
                                              tasksdebug ("A task failed: " ++ show e)
                       loop

worker_ jobqueue = loop where
 loop = do
         job <- atomically $ readTChan jobqueue
         case job of
           Done  -> return ()
           Job x -> ((x >> return ()) `CE.catch` (tasksdebug . ("A task failed: " ++) . show)) >> loop

workerS_ s0 jobqueue = loop where
 loop = do
         job <- atomically $ readTChan jobqueue
         case job of
           Done  -> return ()
           Job x -> ((x s0 >> return ()) `CE.catch` (tasksdebug . ("A task failed: " ++) . show)) >> loop

waitForChan c = atomically (check =<< isEmptyTChan c)
waitFor var   = atomically $ do
                  x <- readTVar var
                  check (x == 0)

getTChanContents c = atomically go where
  go = do
    empty <- isEmptyTChan c
    if empty then return []
      else do
        x <- readTChan c
        xx <- go
        return (x:xx)

parMapM :: Int -> (a -> IO b) -> [a] -> IO [b]
parMapM n f xx = parSequence n $ map f xx
parMapM_ :: Int -> (a -> IO b) -> [a] -> IO ()
parMapM_ n f xx = parSequence_ n $ map f xx
parMapM' :: Int -> (a -> IO b) -> [a] -> IO (TChan (Res b))
parMapM' n f xx = parSequence' n (map f xx)

parMapMS_ s0 f xx = parSequenceS_ s0 $ map f xx

parForM  n = flip (parMapM  n)
parForM' n = flip (parMapM' n)
parForM_ n = flip (parMapM_ n)
parForMS_ s0 = flip (parMapMS_ s0)