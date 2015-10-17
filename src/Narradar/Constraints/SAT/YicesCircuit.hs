{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PartialTypeSignatures #-}

module Narradar.Constraints.SAT.YicesCircuit
   (solveRPO, solveWPO, RPOM, WPOM
   ) where

import           Control.Applicative                 ((<$>))
import           Control.Arrow                       (second)
import           Control.DeepSeq                     (NFData)
import           Control.Exception as CE             (catch, SomeException)
import           Control.Monad.Reader
import           Control.Monad.State.Strict          hiding ((>=>), forM_)
import           Data.Foldable                       (toList)
import           Data.List                           (sortBy)
import           Data.Hashable
import           Data.Monoid                         ( Monoid(..) )
import           Data.Sequence                       ( Seq, (<|) )
import           Data.Set                            ( Set )
import           Math.SMT.Yices.Syntax
import           Math.SMT.Yices.Pipe
import           Narradar.Types.Term
import           Narradar.Constraints.SAT.MonadSAT   hiding (and,or)
import           Narradar.Constraints.SAT.RPOAF (EnvRPO(..))
import           Narradar.Constraints.SAT.WPO   (EnvWPO(..))
import           Narradar.Utils                      (on,debug,debug',withTempFile)
import           Text.PrettyPrint.HughesPJClass
import           System.IO
import           Prelude                             hiding( not, and, or, (>), fromInteger )
import qualified Prelude                             as P

import qualified Data.HashMap                        as HashMap
import           Data.Maybe                          (fromMaybe)
import qualified Data.Set                            as Set
import qualified Data.Map                            as Map
import qualified Narradar.Types                      as Narradar
import qualified Data.Term.Family                    as Family

import           Funsat.ECircuit                     (Circuit(..), Co, CastCircuit(..), ECircuit(..), NatCircuit(..), ExistCircuit(..), MaxCircuit(..), BIEnv, Natural(..))

import           Funsat.TermCircuit                   ( TermCircuit(..), CoTerm_, OneCircuit(..), AssertCircuit(..), runEvalM)
import           Funsat.TermCircuit.Ext               ( TermExtCircuit(..), lexpgt, lexpeq )
import           Funsat.TermCircuit.RPO               as RPO
import qualified Funsat.TermCircuit.WPO               as WPO

import Debug.Hoed.Observe

deriving instance Eq  ExpY
deriving instance Ord ExpY
deriving instance Eq  TypY
deriving instance Ord TypY
--deriving instance Generic ExpY
--instance Observable ExpY
instance Observable ExpY where observer = observeOpaque "ExpY"

type k :->: v = HashMap.HashMap k v

newtype YicesSource id var = YicesSource { unYicesSource :: State (YState id var) ExpY}

type instance Family.TermF (YicesSource id)   = TermF id
type instance Family.Id    (YicesSource id)   = id
type instance Family.Var   (YicesSource id v) = v

instance Observable v => Observable (YicesSource id v) where
  observer fn ctxt = YicesSource $ do
    res <- unYicesSource fn
    return (observer res ctxt)

data YVar = YV Int String

instance Eq YVar where
  YV a _ == YV b _ = a == b
instance Ord YVar where
  compare (YV a _) (YV b _) = compare a b

instance Show YVar where show (YV i msg) = 'y' : 'v' : show i ++ msg
instance Pretty YVar where pPrint = text . show
instance Hashable YVar where hashWithSalt s (YV i _) = hashWithSalt s i
instance Enum YVar where
  toEnum          i = YV i "fromEnum"
  fromEnum (YV i _) = i

data YState id var = YState
    { internal  :: !([YVar])
    , variables :: !(Set (var, TypY))
    , assertions :: !(Seq ExpY)
    , varmaps    :: VarMaps (YVar, ExpY) id var
    , w0         :: Maybe (Natural var)
    }
   deriving Show

updateGtMap f it@YState{varmaps} = it{ varmaps = varmaps{ termGtMap = f (termGtMap varmaps)}}
updateGeMap f it@YState{varmaps} = it{ varmaps = varmaps{ termGeMap = f (termGeMap varmaps)}}
updateEqMap f it@YState{varmaps} = it{ varmaps = varmaps{ termEqMap = f (termEqMap varmaps)}}

emptyYState = YState [YV 2 "" ..] mempty mempty mempty Nothing

solveYices :: (Hashable id, Ord id, Read var, Ord var, Show var) => YicesSource id var -> IO (Maybe (BIEnv var))
solveYices = solveDeclarations Nothing . runYices

runYices :: (Hashable id, Ord id, Ord var, Show var) => YicesSource id var -> [CmdY]
runYices y = let (me,stY) = runYices' emptyYState y
             in generateDeclarations stY ++
                [ ASSERT x | x <- me : toList(assertions stY)]


runYices' stY (YicesSource y) = runState y stY

generateDeclarations :: (Hashable id, Ord var, Show var) => YState id var -> [CmdY]
generateDeclarations YState{varmaps=VarMaps{..},..} =
   [DEFINE (show v, typ) Nothing | (v,typ) <- Set.toList variables] ++
   [DEFINE (show v, VarT "bool")  (Just c)
        | (v, c) <- sortBy (compare `on` fst) (HashMap.elems termEqMap ++
                                               HashMap.elems termGtMap ++
                                               HashMap.elems termGeMap)]

solveDeclarations :: (Ord v, Read v) => Maybe Int -> [CmdY] -> IO (Maybe (BIEnv v))
solveDeclarations mb_timeout cmds = do
#ifdef DEBUG
  withTempFile "/tmp" "narradar.yices" $ \fp h -> do
       mapM_ (hPutStrLn h . show) cmds
       hPutStrLn h "(max-sat)"
       hPutStrLn stderr ("Yices problem written to " ++ fp)
       hClose h
       return (False, ())
#endif
  let opts = maybe [] (\tm -> ["-tm", show tm]) mb_timeout
  debug (unlines $ map show cmds)
  res <- quickCheckY' "yices" opts (cmds ++ [MAXSAT])
         `catch` \(e :: SomeException) -> error ("An error ocurred calling Yices: " ++ show e)
  case res of
    Sat values -> do
       debug ("\n***** Yices returned Sat, the solutions are:\n" ++ show values)
       return . Just . Map.fromList $
                   [ (read v, Right val) | (VarE v := LitB val) <- values] ++
                   [ (read v, Left (P.fromInteger val)) | (VarE v := LitI val) <- values]
    Unknown values -> do -- FIXME Needs checking !
       debug ("\n***** Yices returned Unknown, and some results:\n" ++ show values)
       return . Just . Map.fromList $
                   [ (read v, Right val) | (VarE v := LitB val) <- values] ++
                   [ (read v, Left (P.fromInteger val)) | (VarE v := LitI val) <- values]
    _ -> return Nothing

type instance Co (YicesSource id) v = (Ord v, Show v)
instance Circuit (YicesSource id) where
  true  = YicesSource $ return $ LitB True
  false = YicesSource $ return $ LitB False
  input v = YicesSource $ do
              modify $ \y -> y{variables = Set.insert (v, VarT "bool") (variables y)}
              return (VarE $ show v)
  not   = liftYices NOT
  and   = liftYices2 f where
     f (LitB False) _ = LitB False
     f (LitB True)  y = y
     f x (LitB True)  = x
     f _ (LitB False) = LitB False
     f x y = AND [x, y]

  or    = liftYices2 f where
     f (LitB False) y = y
     f (LitB True)  _ = LitB True
     f _ (LitB True)  = LitB True
     f x (LitB False) = x
     f x y = OR [x, y]

  andL [] = true
  andL [x] = x
  andL xx = YicesSource . fmap AND . sequence . map unYicesSource $ xx
  orL [] = false
  orL [x] = x
  orL xx = YicesSource . fmap OR . sequence . map unYicesSource $ xx

instance ECircuit (YicesSource id) where
  xor  = liftYices2 $ \a b -> AND [ OR [a, b]
                                  , OR [NOT a, NOT b]]
  iff  = liftYices2 f where
     f (LitB False) (LitB True) = LitB False
     f (LitB False) (LitB False) = LitB True
     f (LitB False) y = NOT y
     f (LitB True)  y = y
     f x y = x := y

  onlyif = liftYices2 f where
     f (LitB False) _ = LitB True
     f (LitB True) y = y
     f y (LitB True)  = LitB True
     f y (LitB False) = NOT y
     f x y = x :=> y

  ite  = liftYices3 f where
     f b (LitB False) f = AND [NOT b, f]
     f b (LitB True)  f = OR [b, f]
     f b t (LitB False) = AND [b, t]
     f b t (LitB True)  = OR [NOT b,t]
     f b t f = ITE b t f

instance NatCircuit (YicesSource id) where
  nat (Natural v) = YicesSource $ do
              modify $ \y -> y{variables = Set.insert (v, VarT "nat") (variables y)}
              return (VarE $ show v)

  gt = liftYices2 (:>)
  eq = liftYices2 (:=)
  lt = liftYices2 (:<)

  (+#) = liftYices2 (:+:)
  (-#) = liftYices2 (:-:)
  (*#) = liftYices2 (:*:)
  fromInteger = YicesSource . return . LitI

  iteNat = ite

instance OneCircuit (YicesSource id) where
--  one = oneExist

instance MaxCircuit (YicesSource id) where
  max x y = iteNat (gt x y) x y

instance ExistCircuit (YicesSource id) where
  existsBool f = YicesSource $ do
              v   <- freshV "existBool"
              exp <- unYicesSource $ f (YicesSource . return . VarE . show $ v)
              return $ EXISTS [(show v, VarT "bool")] exp
  existsNat  f = YicesSource $ do
              v   <- freshV "existsNat"
              exp <- unYicesSource $ f (YicesSource . return . VarE . show $ v)
              return $ EXISTS [(show v, VarT "nat")] exp

instance CastCircuit (YicesSource id) (YicesSource id) where
  type CastCo (YicesSource id) (YicesSource id) v = ()
  castCircuit = id

instance AssertCircuit (YicesSource id) where
  assertCircuit this then_ = YicesSource $ do
      exp <- unYicesSource this
      modify $ \env -> env{ assertions = exp <| assertions env }
      unYicesSource then_

{-# INLINE liftYices #-}
{-# INLINE liftYices2 #-}
{-# INLINE liftYices3 #-}
{-# INLINE freshV #-}

liftYices  f a   = YicesSource $ do {h <- unYicesSource a; return $ f h}
liftYices2 f a b = YicesSource $ do
  va <- unYicesSource a
  vb <- unYicesSource b
  return $ f va vb
liftYices3 f a b c = YicesSource $ do
  va <- unYicesSource a
  vb <- unYicesSource b
  vc <- unYicesSource c
  return $ f va vb vc

freshV msg = do
  YV v _ : vv <- gets internal
  modify $ \y -> y{internal = vv}
--  debug(show v ++ ": " ++ msg)
  return (YV v msg)

-- ----------------
-- RPO circuit
-- ----------------

newtype RPOCircuit id v = RPOCircuit { unRPO :: YicesSource id v } deriving Observable

type instance Family.Id    (RPOCircuit id) = id
type instance Family.TermF (RPOCircuit id) = TermF id
type instance Family.Var   (RPOCircuit id var) = var

type instance Co (RPOCircuit id) v = Co (YicesSource id) v
deriving instance Circuit       (RPOCircuit id)
deriving instance ECircuit      (RPOCircuit id)
deriving instance NatCircuit    (RPOCircuit id)
deriving instance AssertCircuit (RPOCircuit id)
deriving instance ExistCircuit  (RPOCircuit id)
deriving instance OneCircuit    (RPOCircuit id)
deriving instance MaxCircuit    (RPOCircuit id)

type instance CoTerm_ (RPOCircuit id) (TermF id) tv v = (tv ~ Narradar.Var)

instance ( Hashable id, Ord id, Pretty id, IsSimple id
         , HasFiltering id, HasLexMul id, HasPrecedence id, HasStatus id
         , TermExtCircuit (RPOCircuit id) id
         ) =>
   TermCircuit (RPOCircuit id) where

 termGt s t = RPOCircuit $ YicesSource $ do
      env <- get
      case HashMap.lookup (s,t) (termGtMap $ varmaps env) of
         Just (v,_)  -> return (VarE (show v))
         Nothing -> do
           meConstraint <- unYicesSource $ unRPO $ RPO.termGt_ s t
           meVar        <- freshV "termGt"
           modify $ updateGtMap $ HashMap.insert (s,t) (meVar, meConstraint)
           return (VarE (show meVar))
 termEq s t = RPOCircuit $ YicesSource $ do
      env <- get
      case HashMap.lookup (s,t) (termEqMap $ varmaps env) of
         Just (v,_)  -> return (VarE (show v))
         Nothing -> do
           meConstraint <- unYicesSource $ unRPO $ RPO.termEq_ s t
           meVar        <- freshV "termEq"
           modify $ updateEqMap $ HashMap.insert (s,t) (meVar, meConstraint)
           return (VarE (show meVar))


-- ----
-- WPO
-- ----
newtype WPOCircuit id v = WPOCircuit { unWPO :: YicesSource id v } deriving Observable

type instance Family.Id    (WPOCircuit id) = id
type instance Family.TermF (WPOCircuit id) = TermF id
type instance Family.Var   (WPOCircuit id var) = var

type instance Co (WPOCircuit id) v = Co (YicesSource id) v
deriving instance Circuit       (WPOCircuit id)
deriving instance ECircuit      (WPOCircuit id)
deriving instance NatCircuit    (WPOCircuit id)
deriving instance AssertCircuit (WPOCircuit id)
deriving instance ExistCircuit  (WPOCircuit id)
deriving instance OneCircuit    (WPOCircuit id)
deriving instance MaxCircuit    (WPOCircuit id)

type instance CoTerm_ (WPOCircuit id) (TermF id) tv v = (tv ~ Narradar.Var)

instance ( Hashable id, Pretty id, Ord id
         , WPO.WPOAlgebra (WPOCircuit id)
         , TermExtCircuit (WPOCircuit id) id
         , WPO.WPOSymbol id
         ) =>
    TermCircuit (WPOCircuit id) where

 termGt s t = WPOCircuit $ YicesSource $ do
      env <- get
      case HashMap.lookup (s,t) (termGtMap $ varmaps env) of
         Just (v,_)  -> return (VarE (show v))
         Nothing -> do
           meConstraint <- unYicesSource $ unWPO $ WPO.termGt_ s t
           meVar        <- freshV "termGt"
           modify $ updateGtMap $ HashMap.insert (s,t) (meVar, meConstraint)
           return (VarE (show meVar))
 termGe s t = WPOCircuit $ YicesSource $ do
      env <- get
      case HashMap.lookup (s,t) (termGeMap $ varmaps env) of
         Just (v,_)  -> return (VarE (show v))
         Nothing -> do
           meConstraint <- unYicesSource $ unWPO $ WPO.termGe_ s t
           meVar        <- freshV "termGe"
           modify $ updateGeMap $ HashMap.insert (s,t) (meVar, meConstraint)
           return (VarE (show meVar))

instance (WPO.WPOAlgebra (WPOCircuit id)
         ) => WPO.WPOCircuit (WPOCircuit id) where
  w0 = WPOCircuit $ YicesSource $ do
       v <- gets w0
       unYicesSource $ unWPO $ nat (fromMaybe (error "w0") v)

instance ( WPO.WPOAlgebra (WPOCircuit id)
         , HasFiltering id, HasPrecedence id, HasStatus id, Eq id
          ) => TermExtCircuit (WPOCircuit id) id where
  exGt = lexpgt
  exEq = lexpeq

-- ----------------------------
-- MonadSAT implementation
-- ----------------------------

data StY id v = StY { poolY :: [Int]
                    , mkV   :: Maybe String -> Int -> v
                    , cmdY  :: [CmdY]
                    , stY   :: YState id v
                    }

newtype SMTY (repr :: * -> * -> *) id v a = SMTY {unSMTY :: State (StY id v) a}
                                       deriving (Functor, Applicative, Monad, MonadState (StY id v))



newtype RPOM id v a = RPOM { unRPOM :: SMTY RPOCircuit id v a } deriving (Applicative, Functor, Monad)
instance MonadReader (EnvRPO (RPOCircuit id) v) (RPOM id v) where ask = return EnvRPO

newtype WPOM id v a = WPOM {unWPOM :: ReaderT (EnvWPO (WPOCircuit id) v) (SMTY WPOCircuit id v) a}
                    deriving (Functor, Applicative, Monad, MonadReader (EnvWPO (WPOCircuit id) v))

class    SMTCircuit repr       where run :: repr id v -> SMTY repr id v ExpY
instance SMTCircuit RPOCircuit where run  = runCircuit . unRPO
instance SMTCircuit WPOCircuit where run  = runCircuit . unWPO

runCircuit :: YicesSource id v -> SMTY repr id v ExpY
runCircuit m = SMTY $ do
  st <- gets stY
  let (res, st') = runYices' st m
  modify $ \y -> y{stY = st'}
  return res

instance (Hashable v, Ord v, Show v
         ,Co (repr id) v
         , OneCircuit (repr id), ECircuit (repr id), NatCircuit (repr id)
         , MaxCircuit (repr id)
         , SMTCircuit repr
         ) => MonadSAT (repr id) v (SMTY repr id v) where
  boolean_ "" = do {st@StY{poolY = h:t, mkV} <- get; put st{poolY=t}; return (mkV Nothing h)}
  boolean_ s = do {st@StY{poolY = h:t, mkV} <- get; put st{poolY=t}; return (mkV (Just s) h)}
  natural_ s = do {b <- boolean_ s; return (Natural b)}
  assert_ _ [] = return ()
  assert_ msg a = do
      st <- gets stY
      me <- run $ orL a
      modify $ \st -> st{cmdY = ASSERT me : cmdY st}

  assertW w a = do
      st <- gets stY
      me <- run $ orL a
      modify $ \st -> st{cmdY = ASSERT_P me (Just $ fromIntegral w) : cmdY st}


deriving instance (Hashable v, Ord v, Show v, Taggable v) =>  MonadSAT (RPOCircuit id) v (RPOM id v)

instance (Hashable v, Ord v, Show v, Taggable v
         ) => MonadSAT (WPOCircuit id) v (WPOM id v) where
  boolean_ i   = WPOM $ lift $ boolean_ i
  natural_ i   = WPOM $ lift $ natural_ i
  assert_  i x = WPOM $ lift $ assert_  i x


solve_ :: (Hashable id, Ord id, Show id, Pretty id, Enum v, Ord v, Read v, Show v) =>
             Int -> (Maybe String -> Int -> v) -> SMTY repr id v (EvalM v a) -> IO (Maybe a)
solve_ start mkVar  (SMTY my) = do
  let (me, StY{..}) = runState my (StY [start ..] mkVar [] emptyYState)
--  let symbols = getAllSymbols $ mconcat [ Set.fromList [t, u] | ((t,u),_) <- HashMap.toList (termGtMap stY) ++ HashMap.toList (termEqMap stY)]
  bienv <- solveDeclarations Nothing (generateDeclarations stY ++ cmdY)
--  debug (unlines $ map show $ Set.toList symbols)
--  debug (show . vcat . map (uncurry printGt.second fst) . HashMap.toList . termGtMap $ stY)
--  debug (show . vcat . map (uncurry printEq.second fst) . HashMap.toList . termEqMap $ stY)
  return ( (`runEvalM` me) <$> bienv )
 where
  printEq (t,u) v = v <> colon <+> t <+> text "=" <+> u
  printGt (t,u) v = v <> colon <+> t <+> text ">" <+> u

solveRPO :: (Enum v, Ord v, Read v, Show v, Hashable v, NFData v, Observable v
            ,Ord id, Show id, Pretty id, Hashable id
            ) => Observer -> Int -> _ -> RPOM id v (EvalM v a) -> IO (Maybe a)
solveRPO obs start mkV (RPOM circuit) = solve_ start mkV $ circuit

-- | Initialize the WPO environment and call solve
solveWPO obs start mkV (WPOM circuit) = solve_ start mkV $ do
  w0 <- natural_ "w0"
  SMTY $ modify $ \st -> st{stY = (stY st){w0 = Just w0}}
  runReaderT circuit (EnvWPO w0)

instance Observable1 (RPOM id v) where
  observer1 fn cxt =
        do res <- fn
           send "<RPOM>" (return return << res) cxt

instance Observable1 (WPOM id v) where
  observer1 fn cxt =
        do res <- fn
           send "<WPOM>" (return return << res) cxt

instance Observable a => Observable (WPOM id v a) where
  observers = observers1
  observer = observer1
instance Observable a => Observable (RPOM id v a) where
  observers = observers1
  observer = observer1
