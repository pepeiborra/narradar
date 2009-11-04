{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE PatternGuards #-}

module Narradar.Constraints.RPO where

import Prelude hiding ((>))
import qualified Prelude

import Control.Monad
import Data.Foldable (Foldable)
import Data.List
import Data.Typeable
import Narradar.Framework.Ppr
import Narradar.Types.Term
import Narradar.Utils


class HasPrecedence a where precedence :: a -> Int
class HasStatus     a where status     :: a -> Status


data Status   = Mul | Lex (Maybe [Int]) deriving (Eq, Ord, Show)
mkStatus mul perm
 | mul       = Mul
 | otherwise = Lex (Just [head ([i | (i,True) <- zip [1..] perm_i] ++ [-1])
                             | perm_i <- perm])

instance Pretty Status where pPrint = text.show

data RPO m a = RPO {(>), (>~), (~~) :: a -> a -> m Bool}

symbolRPO :: (id ~ TermId t, HasId t, Pretty id, HasPrecedence id, HasStatus id, Foldable t, Eq v, Eq(t(Term t v))
             ,Monad m) => RPO m (Term t v)
symbolRPO = RPO{..} where

  infixr 4 >
  infixr 4 >~
  infixr 4 ~~

  s >~ t = s > t <|> s ~~ t

  s ~~ t
   | Just id_s <- rootSymbol t, tt_s <- directSubterms t
   , Just id_t <- rootSymbol t, tt_t <- directSubterms t

   = precedence id_s == precedence id_t &> exeq id_s id_t tt_s tt_t

   | otherwise = return (s == t)

  s > t
   | s == t = return False
   | Just id_t <- rootSymbol t, tt_t <- directSubterms t
   , Just id_s <- rootSymbol s, tt_s <- directSubterms s
   = anyM (>~ t) tt_s <|>
     (allM (s >) tt_t
      <&> (precedence id_s Prelude.> precedence id_t
           |>
          (precedence id_s == precedence id_t
           &> exgt id_s id_t tt_s tt_t)))

   | Just id_s <- rootSymbol s, tt_s <- directSubterms s
   = anyM (>~ t) tt_s

   | otherwise = return False


  exgt id_s id_t
       | Mul    <- status id_s, Mul    <- status id_t = mulD (>) (~~)
       | Lex ps <- status id_s, Lex pt <- status id_t = lexsD (>) (~~) (removeFiltered ps) (removeFiltered pt)
       | otherwise = \_ _ -> return False

  exeq id_s id_t
       | Mul    <- status id_s, Mul    <- status id_t = muleqD (~~)
       | Lex ps <- status id_s, Lex pt <- status id_t = lexseqD (~~) (removeFiltered ps) (removeFiltered pt)
       | otherwise = \_ _ -> return False

  removeFiltered = fmap ( filter (/= (-1)))

  lexD (>) (~~) []     _      = return False
  lexD (>) (~~) _      []     = return True
  lexD (>) (~~) (f:ff) (g:gg) =    (f > g)
                                <|> (f ~~ g <&> lexD (>) (~~) ff gg)

  lexeqD (~~) []     []     = return True
  lexeqD (~~) _      []     = return False
  lexeqD (~~) []     _      = return False
  lexeqD (~~) (f:ff) (g:gg) = (f ~~ g <&> lexeqD (~~) ff gg)

  lexsD (>) (~~) f_perm g_perm ff gg = lexD (>) (~~) (maybe ff ((`select` ff) . map pred) f_perm)
                                                     (maybe gg ((`select` gg) . map pred) g_perm)
  lexseqD   (~~) f_perm g_perm ff gg = lexeqD (~~) (maybe ff ((`select` ff) . map pred) f_perm)
                                                   (maybe gg ((`select` gg) . map pred) g_perm)

  mulD (>) (~~) m1 m2 = muleqD (~~) m1 m2
                         <&>
                        (exists m1' $ \x -> exists m2' $ \y -> x > y)
   where
        m1' = m1 \\ m2
        m2' = m2 \\ m1

  muleqD (~~) m1 m2 = forall m2' $ \y-> exists m1' $ \x -> x ~~ y
     where
        m1' = m1 \\ m2
        m2' = m2 \\ m1


  infixr 3 <&>
  infixr 3  &>
  infixr 3 <&
  infixr 2 <|>
  infixr 2  |>
  infixr 2 <|

  (<|>) = liftM2 (||)
  (<&>) = liftM2 (&&)

  x |> y = (x ||) <$> y
  x &> y = (x &&) <$> y

  x <| y = (|| y) <$> x
  x <& y = (&& y) <$> x

  forall = flip allM
  exists = flip anyM

  (<$>)  = liftM

allM  f xx = and `liftM` mapM f xx
anyM  f xx = or  `liftM` mapM f xx

