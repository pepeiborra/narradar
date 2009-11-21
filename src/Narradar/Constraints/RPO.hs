{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE PatternGuards #-}

module Narradar.Constraints.RPO where

import Prelude hiding ((>))
import qualified Prelude

import Control.Exception(assert)
import Control.Monad
import Data.Foldable (Foldable)
import Data.List
import Data.Typeable
import Narradar.Framework.Ppr
import Narradar.Types.Term
import Narradar.Utils


class HasPrecedence a where precedence :: a -> Int
class HasStatus     a where status     :: a -> Status
class HasFiltering  a where filtering  :: a -> Either Int [Int]

data Status   = Mul | Lex (Maybe [Int]) deriving (Eq, Ord, Show)
mkStatus mul perm
 | mul       = Mul
 | otherwise = assert (if all oneOrNone perm then True else pprTrace perm False) $
               assert (all oneOrNone (transpose perm)) $
               Lex (Just [ head ([i | (i,True) <- zip [1..] perm_i] ++ [-1])
                          | perm_i <- perm])

  where
    oneOrNone []         = True
    oneOrNone (False:xx) = oneOrNone xx
    oneOrNone (True:xx)  = not $ or xx

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
   | s == t = return True

   | Just id_s <- rootSymbol s, tt_s <- directSubterms s
   , Just id_t <- rootSymbol t, tt_t <- directSubterms t

   = precedence id_s == precedence id_t &> exeq id_s id_t tt_s tt_t

   | otherwise = return False

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


  lexsD (>) (~~) f_perm g_perm ff gg = lexD (>) (~~) (maybe ff (permute ff) f_perm)
                                                     (maybe gg (permute gg) g_perm)
  lexseqD   (~~) f_perm g_perm ff gg = lexeqD (~~)   (maybe ff (permute ff) f_perm)
                                                     (maybe gg (permute gg) g_perm)

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

  sel = selectSafe "Narradar.Constraints.RPO"


symbolRPOAF :: (id ~ TermId t, HasId t, Pretty id, HasPrecedence id, HasStatus id, HasFiltering id, Foldable t, Eq v, Eq(t(Term t v))
             ,Monad m) => RPO m (Term t v)
symbolRPOAF = RPO{..} where

  infixr 4 >
  infixr 4 >~
  infixr 4 ~~

  s >~ t = s > t <|> s ~~ t

  s ~~ t
   | s == t = return True

   | Just id_s <- rootSymbol s, tt_s <- directSubterms s
   , Left i <- filtering id_s
   = tt_s !! pred i ~~ t

   | Just id_t <- rootSymbol t, tt_t <- directSubterms t
   , Left j <- filtering id_t
   = tt_t !! pred j ~~ s

   | Just id_s <- rootSymbol s, tt_s <- directSubterms s
   , Just id_t <- rootSymbol t, tt_t <- directSubterms t
   , Right _  <- filtering id_s
   , Right _  <- filtering id_t
   = precedence id_s == precedence id_t &> exeq id_s id_t tt_s tt_t

   | otherwise = return False

  s > t

   | Just id_t <- rootSymbol t, tt_t <- directSubterms t
   , Just id_s <- rootSymbol s, tt_s <- directSubterms s
   , Right ii  <- filtering id_s
   , Left  j   <- filtering id_t
   = s > tt_t !! pred j

   | Just id_t <- rootSymbol t, tt_t <- directSubterms t
   , Just id_s <- rootSymbol s, tt_s <- directSubterms s
   , Right ii  <- filtering id_s
   , Right jj  <- filtering id_t
   = anyM (>~ t) (sel 3 ii tt_s) <|>
     (allM (s >) (sel 4 jj tt_t)
      <&> (precedence id_s Prelude.> precedence id_t
           |>
          (precedence id_s == precedence id_t
           &> exgt id_s id_t tt_s tt_t)))

   | Just id_s <- rootSymbol s, tt_s <- directSubterms s
   , Right ii <- filtering id_s
   = anyM (>~ t) (sel 5 ii tt_s)

   | Just id_s <- rootSymbol s, tt_s <- directSubterms s
   , Left i <- filtering id_s
   = tt_s !! pred i > t

   | otherwise = return False

  exgt id_s id_t tt_s tt_t
       | Mul    <- status id_s, Mul    <- status id_t = mulD  (>) (~~) (sel 11 ii tt_s) (sel 12 jj tt_t)
       | Lex ps <- status id_s, Lex pt <- status id_t = lexsD (>) (~~) id_s id_t tt_s tt_t
       | otherwise = return False
    where
      Right ii = filtering id_s
      Right jj = filtering id_t

  exeq id_s id_t tt_s tt_t
       | Mul    <- status id_s, Mul    <- status id_t = muleqD  (~~) (sel 1 ii tt_s) (sel 2 jj tt_t)
       | Lex ps <- status id_s, Lex pt <- status id_t = lexseqD (~~) id_s id_t tt_s tt_t
       | otherwise = return False
    where
      Right ii = filtering id_s
      Right jj = filtering id_t


  lexD (>) (~~) []     _      = return False
  lexD (>) (~~) _      []     = return True
  lexD (>) (~~) (f:ff) (g:gg) =     (f > g)
                                <|> (f ~~ g <&> lexD (>) (~~) ff gg)

  lexeqD (~~) []     []     = return True
  lexeqD (~~) _      []     = return False
  lexeqD (~~) []     _      = return False
  lexeqD (~~) (f:ff) (g:gg) = (f ~~ g <&> lexeqD (~~) ff gg)

  lexsD (>) (~~) id_f id_g ff gg = lexD (>) (~~) (selectLexArgs id_f ff)
                                                 (selectLexArgs id_g gg)

  lexseqD   (~~) id_f id_g ff gg = lexeqD   (~~) (selectLexArgs id_f ff)
                                                 (selectLexArgs id_g gg)
  selectLexArgs id tt
    | Lex (Just p) <- status id = permute tt p
    | Right ii  <- filtering id = sel 13 ii tt


  mulD (>) (~~) m1 m2 = muleqD (\s t -> s > t <|> s ~~ t) m1' m2'
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

  sel n ii = selectSafe ("Narradar.Constraints.RPO.symbolRPOAF - " ++ show n) (map pred ii)
  sel6 = sel 6
  sel7 = sel 7
  sel8 = sel 8
  sel9 = sel 9

allM  f xx = and `liftM` mapM f xx
anyM  f xx = or  `liftM` mapM f xx

permute ff ii = map fst $ dropWhile ( (<0) . snd) $ sortBy (compare `on` snd) (zip ff ii)
