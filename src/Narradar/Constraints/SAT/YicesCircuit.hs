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

module Narradar.Constraints.SAT.YicesCircuit
   (YicesSource(..), YMaps(..)
   ,module Math.SMT.Yices.Syntax
   ,solveYices, runYices, runYices', emptyYMaps --YicesCircuitProblem(..)
   ,generateDeclarations, solveDeclarations
   ) where

import           Control.Exception as CE             (catch, SomeException)
import           Control.Monad.Reader
import           Control.Monad.State.Lazy            hiding ((>=>), forM_)
import           Data.Foldable                       (toList)
import           Data.List                           (sortBy)
import           Data.Hashable
import           Data.Monoid
import           Data.Sequence                       ( Seq, (<|) )
import           Data.Set                            ( Set )
import           Math.SMT.Yices.Syntax
import           Math.SMT.Yices.Pipe
import           Narradar.Types.Term
import           Narradar.Utils                      (on,debug,debug',withTempFile)
import           Text.PrettyPrint.HughesPJClass
import           System.IO
import Prelude hiding( not, and, or, (>) )

import qualified Data.HashMap                        as HashMap
import qualified Data.Set                            as Set
import qualified Data.Map                            as Map
import qualified Narradar.Types                      as Narradar
import qualified Data.Term.Family                    as Family

import           Funsat.ECircuit                     (Circuit(..), CastCircuit(..), ECircuit(..), NatCircuit(..), ExistCircuit(..), BIEnv)

import           Funsat.RPOCircuit                   ( RPOCircuit(..), RPOExtCircuit(..), OneCircuit(..), AssertCircuit(..)
                                                     , termGt_, termGe_, termEq_)

deriving instance Eq  ExpY
deriving instance Ord ExpY
deriving instance Eq  TypY
deriving instance Ord TypY

type k :->: v = HashMap.HashMap k v

newtype YicesSource id var = YicesSource { unYicesSource :: State (YMaps id var) ExpY}

type instance Family.TermF (YicesSource id) = TermF id
type instance Family.Id (YicesSource id)    = id
type instance Family.Var (YicesSource id)   = Narradar.Var

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

data YMaps id var = YMaps
    { internal  :: !([YVar])
    , variables :: !(Set (var, TypY))
    , assertions :: !(Seq ExpY)
    , termGtMap :: !((TermN id, TermN id) :->: (YVar, ExpY))
    , termGeMap :: !((TermN id, TermN id) :->: (YVar, ExpY))
    , termEqMap :: !((TermN id, TermN id) :->: (YVar, ExpY))
    }
  deriving Show

emptyYMaps = YMaps [YV 2 "" ..] mempty mempty mempty mempty mempty

solveYices :: (Hashable id, Ord id, Read var, Ord var, Show var) => YicesSource id var -> IO (Maybe (BIEnv var))
solveYices = solveDeclarations Nothing . runYices

runYices :: (Hashable id, Ord id, Ord var, Show var) => YicesSource id var -> [CmdY]
runYices y = let (me,stY) = runYices' emptyYMaps y
             in generateDeclarations stY ++
                [ ASSERT x | x <- me : toList(assertions stY)]


runYices' stY (YicesSource y) = runState y stY

generateDeclarations :: (Hashable id, Ord var, Show var) => YMaps id var -> [CmdY]
generateDeclarations YMaps{..} =
   [DEFINE (show v, typ) Nothing | (v,typ) <- Set.toList variables] ++
   [DEFINE (show v, VarT "bool")  (Just c)
        | (v, c) <- sortBy (compare `on` fst) (HashMap.elems termEqMap ++ HashMap.elems termGtMap ++ HashMap.elems termGeMap)]

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
                   [ (read v, Left (fromInteger val)) | (VarE v := LitI val) <- values]
    Unknown values -> do -- FIXME Needs checking !
       debug ("\n***** Yices returned Unknown, and some results:\n" ++ show values)
       return . Just . Map.fromList $
                   [ (read v, Right val) | (VarE v := LitB val) <- values] ++
                   [ (read v, Left (fromInteger val)) | (VarE v := LitI val) <- values]
    _ -> return Nothing

instance Circuit (YicesSource id) where
  type Co (YicesSource id) v = (Ord v, Show v)
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
     f x y = x :=> y

  ite  = liftYices3 f where
     f b (LitB False) f = AND [NOT b, f]
     f b (LitB True)  f = OR [b, f]
     f b t (LitB False) = AND [b, t]
     f b t (LitB True)  = OR [NOT b,t]
     f b t f = ITE b t f

instance NatCircuit (YicesSource id) where
  nat v = YicesSource $ do
              modify $ \y -> y{variables = Set.insert (v, VarT "nat") (variables y)}
              return (VarE $ show v)

  gt = liftYices2 (:>)
  eq = liftYices2 (:=)
  lt = liftYices2 (:<)

instance OneCircuit (YicesSource id) where
--  one = oneExist

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

instance (Hashable id, Ord id, Pretty id, RPOExtCircuit (YicesSource id) id) =>
   RPOCircuit (YicesSource id) where
 type CoRPO_ (YicesSource id) (TermF id) tv v = (tv ~ Narradar.Var)

 termGt s t = YicesSource $ do
      env <- get
      case HashMap.lookup (s,t) (termGtMap env) of
         Just (v,_)  -> return (VarE (show v))
         Nothing -> do
           meConstraint <- unYicesSource $ termGt_ s t
           meVar        <- freshV "termGt"
           modify $ \env -> env{termGtMap = HashMap.insert (s,t) (meVar, meConstraint) (termGtMap env)}
           return (VarE (show meVar))
 termEq s t = YicesSource $ do
      env <- get
      case HashMap.lookup (s,t) (termEqMap env) of
         Just (v,_)  -> return (VarE (show v))
         Nothing -> do
           meConstraint <- unYicesSource $ termEq_ s t
           meVar        <- freshV "termEq"
           modify $ \env -> env{termEqMap = HashMap.insert (s,t) (meVar, meConstraint) (termEqMap env)}
           return (VarE (show meVar))
{-
 termGe s t = YicesSource $ do
      env <- get
      case HashMap.lookup (s,t) (termGeMap env) of
         Just (v,_)  -> return (VarE (show v))
         Nothing -> do
           meConstraint <- unYicesSource $ termGe_ s t
           meVar        <- freshV "termGe"
           modify $ \env -> env{termGeMap = HashMap.insert (s,t) (meVar, meConstraint) (termGeMap env)}
           return (VarE (show meVar))
-}

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
