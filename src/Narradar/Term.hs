{-# LANGUAGE PackageImports #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Narradar.Term (TermF(..), TermN, RuleN, constant, term, term1, termId, mapTermId, mapTermIdF, Size(..), fromSimple) where

import Control.Monad
import Data.Char
import Data.Foldable as F (Foldable(..),sum,msum)
import Data.Traversable
import Data.Term
import qualified Data.Term.Simple as Simple
import Data.Term.Rules
import Data.Term.Ppr
import Text.PrettyPrint

data TermF id f = Term id [f] deriving (Eq,Ord,Show)
type TermN id = Free (TermF id)
type RuleN id v = Rule (TermF id) v

term :: id -> [TermN id a] -> TermN id a
term f = Impure . Term f

term1 f t = Impure (Term f [t])

constant :: id -> TermN id a
constant f = term f []

termId :: MonadPlus m => TermN id a -> m id
termId = foldTerm (const mzero) f where
    f (Term f tt) = return f `mplus` F.msum tt

mapTermId :: (id -> id') -> TermN id a -> TermN id' a
mapTermId f = mapTerm (mapTermIdF f)

mapTermIdF :: (id -> id') -> TermF id a -> TermF id' a
mapTermIdF f (Term id tt) = Term (f id) tt

fromSimple (Simple.Term id tt) = Term id tt

-- Specific instance for TermF, only for efficiency
instance Eq id => Unify (TermF id) where
  {-# SPECIALIZE instance Unify (TermF String) #-}
  unifyM = unifyF where
   unifyF t s = do
    t' <- find' t
    s' <- find' s
    case (t', s') of
      (Pure vt, Pure vs) -> if vt /= vs then varBind vt s' else return ()
      (Pure vt, _)  -> {-if vt `Set.member` Set.fromList (vars s') then fail "occurs" else-} varBind vt s'
      (_, Pure vs)  -> {-if vs `Set.member` Set.fromList (vars t') then fail "occurs" else-} varBind vs t'
      (Impure t, Impure s) -> zipTermM_ unifyF t s
   zipTermM_ f (Term f1 tt1) (Term f2 tt2) | f1 == f2 = zipWithM_ f tt1 tt2
                                           | otherwise = fail "structure mismatch"

instance HasId (TermF id) id where getId (Term id _) = Just id
instance MapId TermF where mapId f (Term id tt) = Term (f id) tt

-- -----
-- Size
-- -----
class Size t where size :: t -> Int
instance (Functor f, Foldable f) => Size (Term f v) where
  size = foldTerm (const 1) (\f -> 1 + F.sum f)
instance Size t  => Size [t] where size = F.sum . fmap size
instance (Functor f, Foldable f) => Size (Rule f v) where size = F.sum . fmap size

-- Functor boilerplate
-- --------------------
instance Functor (TermF id) where
    fmap     f (Term a tt) = Term a (fmap f tt)
instance Foldable (TermF id) where
    foldMap  f (Term _ tt) = foldMap f tt
instance Traversable (TermF id) where
    traverse f (Term a tt) = Term a `fmap` traverse f tt

-- Ppr
-- ---
instance (Ppr id, Ppr v) => Ppr (TermN id v) where
 ppr (Pure a)   = ppr a
 ppr (Impure t) = pprT t
  where
    pprT (Term n []) = ppr n
    pprT (Term n [x,y]) | not (any isAlpha $ show $ ppr n) = ppr x <+> ppr n <+> ppr y
    pprT (Term n tt) = ppr n <> parens (hcat$ punctuate comma$ map ppr tt)


instance (Ppr a, Ppr id) => Ppr (TermF id a) where
    ppr (Term n []) = ppr n
    ppr (Term n [x,y]) | not (any isAlpha $ show $ ppr n) = ppr x <+> ppr n <+> ppr y
    ppr (Term n tt) = ppr n <> parens (hcat$ punctuate comma$ map ppr tt)

instance Ppr a => Ppr (TermF String a) where
    ppr (Term n []) = text n
    ppr (Term n [x,y]) | not (any isAlpha n) = ppr x <+> text n <+> ppr y
    ppr (Term n tt) = text n <> parens (hcat$ punctuate comma $ map ppr tt)
