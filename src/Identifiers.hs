{-# LANGUAGE TypeOperators, ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module Identifiers where

import Data.HashTable (hashString)
import Data.Int
import qualified Data.Set as Set

import TRS.Utils
import TRS

type BasicId = Var :+: T Identifier :+: Hole
instance HashConsed BasicId
instance HashConsed (T Identifier)

data Identifier = IdFunction String | IdDP String | AnyIdentifier deriving (Ord)
instance Eq Identifier where
    IdFunction f1 == IdFunction f2 = f1 == f2
    IdDP f1       == IdDP f2       = f1 == f2
    AnyIdentifier == _             = True
    _             == AnyIdentifier = True
    _             == _             = False

instance Show Identifier where
    show (IdFunction f) = f
    show (IdDP n) = n ++ "#"

mkTRS :: [Rule Basic] -> TRS Identifier BasicId
mkTRS rr = TRS (Set.fromList rules') (getSignature rules') where rules' = fmap2 (foldTerm mkTIdF) rr

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
markDP t | Just (T (n::Identifier) tt) <- open t = term (markDPSymbol n) tt
         | otherwise                = t
unmarkDP t | Just (T (n::Identifier) tt) <- open t = term (unmarkDPSymbol n) tt
           | otherwise              = t

unmarkDPRule, markDPRule :: (HashConsed f,T Identifier :<: f) => Rule f -> Rule f
markDPRule   = fmap   markDP
unmarkDPRule = fmap unmarkDP

hashId :: Identifier -> Int32
hashId = hashString . show

instance HashTerm (T Identifier) where hashF (T id tt) = 14 * sum tt * hashId id
