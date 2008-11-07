{-# LANGUAGE UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE TypeOperators, PatternSignatures #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE PatternGuards, RecordWildCards #-}
{-# LANGUAGE GADTs, MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances #-}
module Types (module TRS, module Types) where

import Data.Foldable (Foldable)
import Data.HashTable (hashString)
import Data.Int
import Data.List ((\\))
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import Data.Traversable
import Unsafe.Coerce
import TRS hiding (match)
import TRS.Types (match) -- for Data.AlaCarte match

import Utils
import Prelude as P

type BasicId = Var :+: T Identifier
instance HashConsed BasicId
instance HashConsed (T Identifier)

type  DP a = Rule a


mkTRS :: [Rule Basic] -> TRS Identifier BasicId
mkTRS rr = TRS rules' (getSignature rules') where rules' = fmap2 (foldTerm mkTIdF) rr

class (Functor f, Functor g) => MkTId f g where mkTIdF :: f (Term g) -> Term g
instance (T Identifier :<: g, HashConsed g) => MkTId (T String) g where mkTIdF (T f tt) = term (IdFunction f) tt
instance (MkTId f1 g, MkTId f2 g) => MkTId (f1 :+: f2) g where
    mkTIdF (Inl x) = mkTIdF x
    mkTIdF (Inr x) = mkTIdF x
instance (a :<: g, HashConsed g) => MkTId a g where mkTIdF t = inject(fmap reinject t)

{-
mkTRS rules = TRS rules' (getSignature rules') where
  rules' = fmap2 (foldTerm f) rules
--  f :: (T String :<: tstring, HashConsed tident, T Identifier :<: tident) => tstring (Term tident) -> Term tident
  f t
     | Just(T f tt) <- prj t = term (IdFunction f) tt
     | otherwise = fmap reinject t -- (unsafeCoerce t :: tident(Term tident))
-}

markDPSymbol (IdFunction f) = IdDP f
markDPSymbol f = f
unmarkDPSymbol (IdDP n) = IdFunction n
unmarkDPSymbol n = n

markDP, unmarkDP :: (HashConsed f, T Identifier :<: f) => Term f -> Term f
markDP t | Just (T (n::Identifier) tt) <- match t = term (markDPSymbol n) tt
         | otherwise                = t
unmarkDP t | Just (T (n::Identifier) tt) <- match t = term (unmarkDPSymbol n) tt
           | otherwise                = t

unmarkDPRule, markDPRule :: (HashConsed f,T Identifier :<: f) => Rule f -> Rule f
markDPRule   = fmap   markDP
unmarkDPRule = fmap unmarkDP

data Identifier = IdFunction String | IdDP String  deriving (Eq, Ord)

instance Show Identifier where
    show (IdFunction f) = f
    show (IdDP n) = n ++ "#"

hashId :: Identifier -> Int32
hashId = hashString . show

instance HashTerm (T Identifier) where hashF (T id tt) = 14 * sum tt * hashId id

isGround :: TRSC f => Term f -> Bool
isGround = null . vars

class (Var :<: f) => ExtraVars t f | t -> f where extraVars :: t -> [Var (Term f)]
instance (Var :<: f) => ExtraVars (TRS id f) f where extraVars trs@TRS{} = concat [vars r \\ vars l | l :-> r <- rules trs]
instance (Var :<: f, Foldable f) => ExtraVars (Rule f) f where extraVars (l:->r) = vars r \\ vars l

---------------------------
-- DP Problems
---------------------------

data Problem_ a = Problem  ProblemType a a
     deriving (Eq,Show)

type Problem f = Problem_ (TRS Identifier f)

data ProblemType = Rewriting | Narrowing
     deriving (Eq, Show)
