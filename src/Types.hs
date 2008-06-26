{-# LANGUAGE UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE TypeOperators, PatternSignatures #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE PatternGuards, RecordWildCards #-}
{-# LANGUAGE GADTs, MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances #-}
module Types (module TRS, module Types) where

import Data.AlaCarte
import Data.Foldable (Foldable)
import Data.List ((\\))
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import Data.Traversable
import Unsafe.Coerce
import TRS

import Utils
import Prelude as P

class (T Identifier :<: f, Var :<: f, Traversable f, MatchShapeable f, Unifyable f, Eq (f(Expr f))) => TRSC f
instance (T Identifier :<: f, Var :<: f, Traversable f, MatchShapeable f, Unifyable f, Eq (f(Expr f))) => TRSC f

data TRS f where TRS :: TRSC f => [Rule f] -> Signature -> TRS f

type  DP a = Rule a

instance Ppr f => Show (TRS f) where show trs = show $ rules trs

instance TRSC f => Monoid (TRS f) where
    mempty = TRS mempty mempty
    mappend (TRS r1 _) (TRS r2 _) = let rr = (r1 `mappend` r2) in TRS rr (getSignature rr)

tRS rules = TRS rules (getSignature rules)
rules (TRS r _) = r; sig   (TRS _ s) = s

mkTRS :: [Rule (T String :+: Var) ] -> TRS (T Identifier :+: Var)
mkTRS rules = TRS rules' (getSignature rules') where
  rules' = fmap2 (foldTerm f) rules
  f :: (T String :<: tstring, T Identifier :<: tident) => tstring (Term tident) -> Term tident
  f t
     | Just(T f tt) <- prj t = term (IdFunction f) tt
     | otherwise = inject (unsafeCoerce t :: tident(Term tident))


rootSymbol :: (T Identifier :<: f) => Term f -> Maybe Identifier
rootSymbol t | Just (T root _) <- match t = Just root
             | otherwise = Nothing

markDPSymbol (IdFunction f) = IdDP f
markDPSymbol f = f
unmarkDPSymbol (IdDP n) = IdFunction n
unmarkDPSymbol n = n

markDP, unmarkDP :: (T Identifier :<: f) => Term f -> Term f
markDP t | Just (T (n::Identifier) tt) <- match t = term (markDPSymbol n) tt
         | otherwise                = t
unmarkDP t | Just (T (n::Identifier) tt) <- match t = term (unmarkDPSymbol n) tt
           | otherwise                = t

unmarkDPRule, markDPRule :: (T Identifier :<: f) => Rule f -> Rule f
markDPRule   = fmap   markDP
unmarkDPRule = fmap unmarkDP

data Identifier = IdFunction String | IdDP String  deriving (Eq, Ord)

instance Show Identifier where
    show (IdFunction f) = f
    show (IdDP n) = n ++ "#"

isGround :: TRSC f => Term f -> Bool
isGround = null . vars

class (Var :<: f) => ExtraVars t f | t -> f where extraVars :: t -> [Var (Term f)]
instance (Var :<: f) => ExtraVars (TRS f) f where extraVars trs@TRS{} = concat [vars r \\ vars l | l :-> r <- rules trs]
instance (Var :<: f, Foldable f) => ExtraVars (Rule f) f where extraVars (l:->r) = vars r \\ vars l

-------------------------
-- Signatures
-------------------------

data Signature = Sig { constructorSymbols :: [Identifier]
                     , definedSymbols :: [Identifier]
                     , arity :: Map.Map Identifier Int}
                 deriving (Show, Eq)

instance Monoid Signature where
    mempty  = Sig mempty mempty mempty
    mappend (Sig c1 s1 a1) (Sig c2 s2 a2) = Sig (snub $ mappend c1 c2) (snub $ mappend s1 s2) (mappend a1 a2)

class SignatureC a where getSignature :: a -> Signature
instance (TRSC f) => SignatureC [Rule f] where
  getSignature rules =
      Sig{arity= Map.fromList [(f,length tt) | l :-> r <- rules, t <- [l,r]
                                             , Just (T (f::Identifier) tt) <- map match (subterms t)]
         , definedSymbols     = dd
         , constructorSymbols = snub [ root | l :-> r <- rules, t <- subterms r ++ properSubterms l, Just root <- [rootSymbol t]] \\ dd}
    where dd = snub [ root | l :-> _ <- rules, let Just root = rootSymbol l]

instance SignatureC (TRS f) where getSignature trs@TRS{} = sig trs

instance SignatureC (Problem f) where getSignature (Problem _ trs@TRS{} dps@TRS{}) = sig trs `mappend` sig dps -- getSignature (trs `mappend` dps)

getArity :: Signature -> Identifier -> Int
getArity Sig{..} f = fromMaybe (error $ "getArity: symbol " ++ show f ++ " not in signature")
                               (Map.lookup f arity)

---------------------------
-- DP Problems
---------------------------

data Problem_ a = Problem  ProblemType a a
     deriving (Eq,Show)

type Problem f = Problem_ (TRS f)

data ProblemType = Rewriting | Narrowing
     deriving (Eq, Show)
