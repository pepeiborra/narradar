{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Narradar.Constraints.SAT.Solve where

import Control.Arrow (first,second)
import Control.Monad.State
import Data.Array.Unboxed
import Data.List (unfoldr)
import Data.Monoid
import Data.NarradarTrie (HasTrie, (:->:))
import qualified Data.NarradarTrie as Trie
import Funsat.Circuit (BEnv, and,or,not)
import Funsat.Types (Clause)
import Funsat.Solver
import System.Directory
import System.FilePath
import System.IO
import System.IO.Unsafe
import System.Process
import Text.Printf

import Narradar.Constraints.SAT.RPOCircuit hiding (nat)
import Narradar.Framework.Ppr
import Narradar.Utils(debug)

import qualified Control.Exception as CE
import qualified Funsat.Types as Funsat
import qualified Funsat.ECircuit as ECircuit
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as LBS
import qualified Narradar.Constraints.SAT.RPOCircuit as RPOCircuit
import qualified Language.CNF.Parse.ParseDIMACS as ParseCNF

import Prelude hiding (and, not, or, any, all, lex, (>))
import qualified Prelude as P

-- --------
-- MonadSAT
-- --------
newtype Var = V Int deriving (Eq, Ord, Show, Num, Enum)
instance Bounded Var where minBound = V 0; maxBound = V maxBound
newtype Natural v = Natural {encodeNatural::[v]} deriving (Eq,Ord,Show)

lit (V i) = Funsat.L i

instance Pretty Var where pPrint (V i) = text "v" <> i

nat :: (Ord v, HasTrie v, Show v) => NatCircuit repr => Natural v -> repr v
nat (Natural n) = ECircuit.nat n

type Weight = Int
type SharedClause id v = [Shared id v]

class Monad m => MonadSAT id v m | m -> id v where
  boolean :: m v
  natural :: Int -> m (Natural v)
  assert  :: SharedClause id v -> m ()
  assertW :: Weight -> Clause -> m ()

-- ---------------------
-- Interpreting booleans
-- ---------------------
type Precedence = [Integer]

class Decode a b var | a b -> var where decode :: a -> EvalM var b

instance Decode (Eval var) Bool var where decode = evalB
instance Decode (Eval var) Integer var  where decode = evalN
instance Decode (Eval var) Int var  where decode = liftM fromInteger . evalN
instance Decode a b var => Decode [a] [b] var where decode = mapM decode
instance (Decode a a' var, Decode b b' var ) => Decode (a, b) (a',b') var where
  decode (a, b) = do {va <- decode a; vb <- decode b; return (va,vb)}

--instance Decode var Bool var where decode = evalB . input
instance Decode Var Bool Var where decode = evalB . input
instance (Ord v, HasTrie v, Show v) => Decode (Natural v) Integer v where decode = evalN . nat

evalDecode :: (Ord var, HasTrie var, Show var) => Decode (Eval var) b var => Eval var -> EvalM var b
evalDecode x = decode x

-- ------------------------
-- MonadSAT implementation
-- ------------------------
data St id v = St { pool     :: [v]
                  , circuit  :: !(Shared id v)
                  , weightedClauses :: [(Weight, Clause)]}

newtype SAT id v a = SAT {unSAT :: State (St id v) a} deriving (Functor, Monad, MonadState (St id v))

instance (Ord v, HasTrie v, Show v) => MonadSAT id v (SAT id v) where
  boolean = do {st <- get; put st{pool=tail (pool st)}; return (head $ pool st)}
  natural bitsize = do {st <- get; put st{pool = drop bitsize (pool st)}; return (Natural $ take bitsize $ pool st)}
  assert   [] = return ()
  assert    a = do {st <- get; put st{circuit = foldr or false a `and` circuit st}}
  assertW w a = do {st <- get; put st{weightedClauses = ( w, a) : weightedClauses st}}

assertAll :: MonadSAT id v m => [Shared id v] -> m ()
assertAll = mapM_ (assert . (:[]))

st0 = St [minBound..] true []

-- -------
-- Solvers
-- -------

-- *** Funsat solver by simplification to vanilla Circuits

solveFun :: (HasTrie id, Ord id, Bounded v, Enum v, Ord v, HasTrie v, Show v) => SAT id v (EvalM v a) -> Maybe a
solveFun = fmap (uncurry $ flip runEvalM) . runFun

solveFunDirect :: (HasTrie id, Ord id, Show id, Bounded v, Enum v, Ord v, HasTrie v, Show v) => SAT id v (EvalM v a) -> Maybe a
solveFunDirect = fmap (uncurry $ flip runEvalM) . runFunDirect

runFunDirect :: (HasTrie id, Ord id, Show id, Bounded v, Enum v, Ord v, HasTrie v, Show v) => SAT id v a -> Maybe (a, BEnv v)
runFunDirect (SAT m) = let
    (val, St _ circuit _weighted) = runState m st0

    -- Skip weighted booleans as Funsat does not do weighted SAT
    circuitProb = unsafePerformIO $ toCNFRPO  (runShared circuit)
    (sol,_,_)   = solve1 . asCNF . either (error.show) id . ParseCNF.parseByteString "input" . asDimacs $ rpoProblemCnf circuitProb

  in case sol of
       Sat{}   -> Just (val, projectRPOCircuitSolution sol circuitProb)
       Unsat{} -> Nothing
 where
 -- | Convert parsed CNF to internal representation.
  asCNF :: ParseCNF.CNF -> CNF
  asCNF (ParseCNF.CNF v c is) =
    CNF {numVars = v
        ,numClauses = c
        ,clauses = map (map fromIntegral . elems) $ is}


runFun :: (HasTrie id, Ord id, Bounded v, Enum v, Ord v, HasTrie v, Show v) => SAT id v a -> Maybe (a, BEnv v)
runFun (SAT m) = let
    (val, St _ circuit _weighted) = runState m st0

    -- Skip weighted booleans as Funsat does not do weighted SAT
    circuitProb = toCNF  (runShared circuit)
    (sol,_,_)   = solve1 (problemCnf circuitProb)

  in case sol of
       Sat{}   -> Just (val, projectCircuitSolution sol circuitProb)
       Unsat{} -> Nothing

data YicesOpts = YicesOpts {maxWeight :: Int, timeout :: Maybe Int}
defaultYicesOpts = YicesOpts 0 Nothing

-- *** Yices based solvers

solveYices = solveYicesDirect

{-
solveYicesMem :: YicesOpts -> SAT id (EvalM Var a) -> IO (Maybe a)
solveYicesMem  YicesOpts{..} (SAT m) = do
    let (val, St _ circuit weighted) = runState m (St [V 1 ..] true [])

        circuitProb   = toCNF  (runShared circuit)
        !cnf          = problemCnf circuitProb
        nv            = numVars cnf
--        nc            = numClauses cnf

    -- feed the problem to Yices
        cs     = map (\c -> unwords (bshow maxWeight : map bshow c ++ ["0"] ))
                     (clauses cnf)
        wcs    = map (\(w,c) -> unwords (bshow w : map bshow c ++ ["0"]))
                     weighted

--        header = printf "p wcnf %d %d %d" (numVars cnf) (numClauses cnf + length weighted) maxWeight
        header = printf "p wcnf %d %d %d" (100000::Int) (1000000::Int) maxWeight
--        opts =  ["-e","-d","-ms", "-mw", show maxWeight] ++ maybe [] (\t -> ["-tm", show t]) timeout

--        wcnf = LBS.unlines (LBS.pack header : cs)

    tmp <- getTemporaryDirectory
    let tempFile = tmp </> "narradar.wcnf"
        opts     =  ["-e","-d"] ++ maybe [] (\t -> ["-tm", show t]) timeout ++ [tempFile]

    hPutStrLn stderr header
    h <- openFile tempFile WriteMode
    mapM_ (hPutStrLn h) (header : cs)
    CE.evaluate nv
--  evaluate nc
    hClose h

    ( code, the_stdout, the_stderr ) <- readProcessWithExitCodeBS "yices" opts (LBS.empty) -- wcnf
    case BS.lines the_stdout of
        (BS.unpack -> "sat") : xs : _ -> do
            hPutStrLn stderr "satisfiable"
            processSolution xs nv circuitProb' val

        _ -> do {hPutStrLn stderr "not satisfiable"; return Nothing}
  where
    bshow = show
-}


solveYicesSimp yo = (fmap.fmap) (uncurry $ flip runEvalM) . runYicesSimp yo

runYicesSimp YicesOpts{..} (SAT m) = do
    let (val, St _ circuit weighted) = runState m (St [minBound..] true [])
        !frozen   = runShared circuit

        !circuitProb = toCNF frozen
        cnf = problemCnf circuitProb
        nv  = numVars cnf
        nc  = numClauses cnf

    -- feed the problem to Yices
        header = LBS.pack $ printf "p cnf %d %d" nv nc
        cs     = map (\c -> LBS.unwords ({-bshow maxWeight : -} map bshow c ++ [LBS.pack "0"] ))
                     (clauses cnf)
        opts     = ["-e","-d"] ++ maybe [] (\t -> ["-tm", show t]) timeout

    debug (LBS.unpack header) -- (LBS.unpack( LBS.unlines (header:cs)))
    debug "\n"
    hFlush stderr

    ( code, the_stdout, the_stderr ) <- readProcessWithExitCodeBS "yices" opts (LBS.unlines (header:cs))
    case BS.lines the_stdout of
        (BS.unpack -> "sat") : xs : _ -> do
            debug "satisfiable"
            let xx  = unfoldr (fmap(second BS.tail) . BS.readInt) (xs `BS.snoc` ' ')
            let sol = Sat $ array (Funsat.V 0, Funsat.V nv) [ (Funsat.V(abs x), x) | x <- take nv xx]
            return $ Just $ (val, projectCircuitSolution sol circuitProb)

        _ -> do
          debug "not satisfiable"
          return Nothing
  where
    bshow = LBS.pack . show

solveYicesSimp1 yo = (fmap.fmap) (uncurry $ flip runEvalM) . runYicesSimp1 yo

runYicesSimp1 YicesOpts{..} (SAT m) = do
    let (val, St _ circuit weighted) = runState m (St [minBound ..] true [])
        !frozen   = runShared circuit
{-
        frozenGr = isGraph $ shareGraph' frozen
        isGraph :: Gr a b -> Gr a b
        isGraph = id
    print frozen
    tmp <- getTemporaryDirectory
    (tmpFile,hTmpFile) <- openTempFile tmp "shareGraph.dot"
    hPutStrLn hTmpFile (graphviz' frozenGr)
    hClose hTmpFile
    system (printf "dot -Tpdf %s -O && open %s" tmpFile (tmpFile <.> "pdf"))
-}
    !circuitProb <- toCNFBS frozen
    let cnf = eproblemCnf circuitProb
        nv  = numVarsBS cnf
        nc  = numClausesBS cnf

    -- feed the problem to Yices
        wcs = map (\(w,c) -> unwords (bshow w : map bshow c ++ ["0"]))
                     weighted

--        header = printf "p wcnf %d %d %d" (numVars cnf) (numClauses cnf + length weighted) maxWeight
--        header = printf "p wcnf %d %d %d" nv nc maxWeight
--        opts =  ["-e","-d","-ms", "-mw", show maxWeight] ++ maybe [] (\t -> ["-tm", show t]) timeout

--        wcnf = LBS.unlines (LBS.pack header : cs)

        opts     = ["-e","-d"] ++ maybe [] (\t -> ["-tm", show t]) timeout

        problem  = asDimacs cnf -- `mappend` wcnf

    debug (LBS.unpack $ head $ LBS.lines problem)
    debug "\n"
    hFlush stderr

    ( code, the_stdout, the_stderr ) <- readProcessWithExitCodeBS "yices" opts problem
    case BS.lines the_stdout of
        (BS.unpack -> "sat") : xs : _ -> do
            debug "satisfiable"
            let xx  = unfoldr (fmap(second BS.tail) . BS.readInt) (xs `BS.snoc` ' ')
            let sol = Sat $ array (Funsat.V 0, Funsat.V nv) [ (Funsat.V(abs x), x) | x <- take nv xx]
            return $ Just (val, projectECircuitSolution sol circuitProb)

        _ -> do {debug "not satisfiable"; return Nothing}
  where
    bshow = show


solveYicesDirect :: (HasTrie id, Ord id, Show id, Bounded v, Enum v, Show v, Ord v, HasTrie v) => YicesOpts -> SAT id v (EvalM v a) -> IO (Maybe a)
solveYicesDirect yo = (fmap.fmap) (uncurry $ flip runEvalM) . runYicesDirect yo

runYicesDirect :: (HasTrie id, Ord id, Show id, Bounded v, Enum v, Show v, Ord v, HasTrie v) => YicesOpts -> SAT id v a -> IO (Maybe (a, BEnv v))
runYicesDirect  YicesOpts{..} (SAT m) = do
    let (val, St _ circuit weighted) = runState m (St [minBound ..] true [])
        !frozen   = runShared circuit
{-
        frozenGr = isGraph $ shareGraph' frozen
        isGraph :: Gr a b -> Gr a b
        isGraph = id
    print frozen
    tmp <- getTemporaryDirectory
    (tmpFile,hTmpFile) <- openTempFile tmp "shareGraph.dot"
    hPutStrLn hTmpFile (graphviz' frozenGr)
    hClose hTmpFile
    system (printf "dot -Tpdf %s -O && open %s" tmpFile (tmpFile <.> "pdf"))
-}
    !circuitProb <- toCNFRPO frozen
    let cnf = rpoProblemCnf circuitProb
        nv  = numVarsBS cnf
        nc  = numClausesBS cnf

    -- feed the problem to Yices
        wcs = map (\(w,c) -> unwords (bshow w : map bshow c ++ ["0"]))
                     weighted

--        header = printf "p wcnf %d %d %d" (numVars cnf) (numClauses cnf + length weighted) maxWeight
--        header = printf "p wcnf %d %d %d" nv nc maxWeight
--        opts =  ["-e","-d","-ms", "-mw", show maxWeight] ++ maybe [] (\t -> ["-tm", show t]) timeout

--        wcnf = LBS.unlines (LBS.pack header : cs)

        opts     = ["-e","-d"] ++ maybe [] (\t -> ["-tm", show t]) timeout

        problem  = asDimacs cnf -- `mappend` wcnf

    debug $ LBS.unpack $ head $ LBS.lines problem
--    debug "\n"
    hFlush stderr

    ( code, the_stdout, the_stderr ) <- readProcessWithExitCodeBS "yices" opts problem
--    debug (BS.unpack the_stdout)
 --   debug (BS.unpack the_stderr)
    case BS.lines the_stdout of
        (BS.unpack -> "sat") : xs : _ -> do
            debug "satisfiable"
            let xx  = unfoldr (fmap(second BS.tail) . BS.readInt) (xs `BS.snoc` ' ')
            let sol = Sat $ array (Funsat.V 0, Funsat.V nv) [ (Funsat.V(abs x), x) | x <- take nv xx]
            return $ Just (val, projectRPOCircuitSolution sol circuitProb)

        _ -> do {debug "not satisfiable"; debug (BS.unpack the_stdout); return Nothing}
  where
    bshow = show

-- Helpers

{-
processSolution xs nv circuitProb val =
            let xx  = unfoldr (fmap(second BS.tail) . BS.readInt) (xs `BS.snoc` ' ')
                sol = Sat $ array (V 0, V nv) [ (V(abs x), x) | x <- take nv xx]
            in Just $ runEvalM (projectCircuitSolution sol circuitProb) val
-}
readProcessWithExitCodeBS exec args input = do
        (hIn, hOut, hErr, hProc) <- runInteractiveProcess exec args Nothing Nothing
        CE.try(LBS.hPut hIn input) :: IO (Either CE.SomeException ())
        stdout <- BS.hGetContents hOut
        stderr <- BS.hGetContents hErr
        code   <- waitForProcess hProc
        return (code, stdout, stderr)


instance HasTrie Var where
  newtype Var :->: x = VarTrie (Int :->: x)
  empty = VarTrie Trie.empty
  lookup (V i) (VarTrie t) = Trie.lookup i t
  insert (V i) v (VarTrie t) = VarTrie (Trie.insert i v t)
  toList (VarTrie t) = map (first V) (Trie.toList t)
