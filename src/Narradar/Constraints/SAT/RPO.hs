{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, UndecidableInstances, TypeSynonymInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}

module Narradar.Constraints.SAT.RPO where

import Control.Applicative
import qualified Control.Exception as CE
import Control.Monad
import Data.Foldable (Foldable, toList)
import Data.List (transpose)
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

import Narradar.Constraints.SAT.Common
import Narradar.Types hiding (symbol, constant)
import Narradar.Utils
import Narradar.Framework.Ppr

import qualified Prelude
import Prelude hiding (lex, not, and, or, (>))

lpoDP  = rpoGen lpoSymbol
mpoDP  = rpoGen mpoSymbol
lposDP = rpoGen lpopSymbol
rpoDP  = rpoGen symbol

rpoGen inn p = isSAT $ do
  let sig        = getSignature p
  let ids = Set.toList $ getAllSymbols sig
  symbols <- mapM (inn sig) ids
  let dict       = Map.fromList (zip ids symbols)
      symb_rules = mapTermSymbols (\f -> fromJust $ Map.lookup f dict) <$$> rules (getR p)
      symb_pairs = mapTermSymbols (\f -> fromJust $ Map.lookup f dict) <$$> rules (getP p)

  decreasing_dps <- replicateM (length symb_pairs) boolean
  assertAll [andM [ l >~ r | l:->r <- symb_rules]
            ,andM [ l >~ r | l:->r <- symb_pairs]
            ,andM [(l > r) <<==>> return dec | (l:->r, dec) <- zip symb_pairs decreasing_dps]
           , or decreasing_dps]

  return $ do syms  <- mapM decode symbols
              dec_bools <- decode decreasing_dps
              let non_dec_pairs = [ r | (r,False) <- zip [0..] dec_bools]
              return (non_dec_pairs, syms)

-- ----------------------------------------------------------------
-- The Recursive Path Ordering, parametric w.r.t the extension
-- ----------------------------------------------------------------

instance (Eq v, Eq (Term f v), Foldable f,
          HasId f, SATOrd (TermId f), Ppr (TermId f), Extend (TermId f)) =>
    SATOrd (Term f v) where
  s ~~ t | s == t = constant True
  s ~~ t = fromMaybe (constant False) $ do
             id_s <- rootSymbol s
             id_t <- rootSymbol t
             return $ andM [ id_s ~~ id_t
                           , exeq id_s id_t (directSubterms s) (directSubterms t)]

  s > t
   | Just id_t <- rootSymbol t, tt_t <- directSubterms t
   , Just id_s <- rootSymbol s, tt_s <- directSubterms s
   = orM [ anyM (>~ t) tt_s
         , if id_s == id_t
              then andM [allM (s >) tt_t, exgt id_s id_t tt_s tt_t]
              else traceGt id_s id_t $
                   andM [allM (s >) tt_t, id_s > id_t]

         ]
   | Just id_s <- rootSymbol s, tt_s <- directSubterms s
   = anyM (>~ t) tt_s

   | otherwise = constant False


-- -------------------------------------------------
-- The symbol datatype encoding all the constraints
-- -------------------------------------------------
data Symbol a = Symbol { the_symbol   :: a
                       , encodePrec   :: Number
                       , encodePerm   :: [[Boolean]]
                       , encodeUseMset:: Boolean
                       , decodeSymbol :: Decoder (SymbolRes a)}

data SymbolRes a = SymbolRes { the_symbolR :: a
                             , precedence  :: Int
                             , status      :: Status }

  deriving (Eq, Ord)


instance Show a => Show (Symbol a) where
    show Symbol{the_symbol} = show the_symbol

instance Ppr a => Ppr (Symbol a) where
    ppr Symbol{the_symbol} = ppr the_symbol

instance Ppr a => Ppr (SymbolRes a) where
    ppr SymbolRes{the_symbolR} = ppr the_symbolR

instance Eq   a => Eq   (Symbol a) where
    a@Symbol{} == b@Symbol{} = the_symbol a == the_symbol b

instance Ord a => Ord (Symbol a) where
   compare a b = the_symbol a `compare` the_symbol b

instance Decode (Symbol a) (SymbolRes a) where
    decode x@Symbol{} = decodeSymbol x


symbol sig x = do
  n <- number (length $ takeWhile (Prelude.>0) $ iterate (`div` 2) $ Set.size (getDefinedSymbols sig))
  let ar = getArity sig x
  perm <- replicateM ar (replicateM ar boolean)
  mset <- boolean

  -- Permutation invariants
  assertAll [ oneM (return <$> perm_i) | perm_i <- perm]
  assertAll [ oneM (return <$> perm_k) | perm_k <- transpose perm]

  return $ Symbol
             { the_symbol = x
             , encodePrec = n
             , encodePerm = perm
             , encodeUseMset = mset
             , decodeSymbol = do
                 n          <- fromInteger `liftM` decode n
                 multiset   <- decode mset
                 perm_bools <- decode perm
                 return (SymbolRes x n (mkStatus multiset perm_bools))
             }

instance Eq a => SATOrd (Symbol a) where
    a ~~ b = encodePrec a `eq` encodePrec b
    a >  b = encodePrec a `gt` encodePrec b


-- ------------
-- LPO and MPO
-- ------------

newtype LPOSymbol a = LPO{unLPO::Symbol a} deriving (Eq, Ord, Show, Ppr, SATOrd)
newtype MPOSymbol a = MPO{unMPO::Symbol a} deriving (Eq, Ord, Show, Ppr, SATOrd)

instance Decode (LPOSymbol a) (SymbolRes a) where decode = decode . unLPO
instance Decode (MPOSymbol a) (SymbolRes a) where decode = decode . unMPO

lpoSymbol sig = liftM LPO . symbol sig
mpoSymbol sig = liftM MPO . symbol sig

instance Eq a => Extend (LPOSymbol a) where
    exgt _ _ = lexgt
    exeq _ _ = lexeq

instance Eq a => Extend (MPOSymbol a) where
    exgt _ _ = mulgt
    exeq _ _ = muleq


lexgt, lexeq, lexge :: (SATOrd a, Eq a) => [a] -> [a] -> SAT Boolean

lexgt []     _      = constant False
lexgt _      []     = constant True
lexgt (f:ff) (g:gg) = orM [ f > g
                            , andM [f ~~ g, lexgt ff gg]
                            ]
lexeq []      []    = constant True
lexeq (f:ff) (g:gg) = andM [ f ~~ g, lexeq ff gg]
lexeq _      _      = constant False

lexge ff gg     = orM [lexeq ff gg, lexgt ff gg]


muleq, mulge, mulgt :: (SATOrd a, Eq a) => [a] -> [a] -> SAT Boolean

mulge ff gg = mulgen (i, j) $ mulgeF ff gg
 where
  (i, j) = (length ff, length gg)


mulgt ff gg = mulgen (i, j) $ \epsilons gammas ->
                     andM [notM $ and epsilons, mulgeF ff gg epsilons gammas]
 where
  (i, j) = (length ff, length gg)


muleq ff gg = mulgen (i, j) $ \epsilons gammas ->
                    andM [mulgeF ff gg epsilons gammas, and epsilons]
 where
  (i, j) = (length ff, length gg)

mulgeF ff gg epsilons gammasM =
    andM [ gamma ==> ifM' epsilon (f_i ~~ g_j) (f_i > g_j)
           | (epsilon, gammasR, f_i) <- CE.assert (length epsilons == length ff) $
                                        zip3 epsilons gammasM ff
           , (gamma, g_j) <- zip gammasR gg]

mulgen (i, j) k = do
    epsilons <- replicateM i boolean
    gammasM  <- replicateM i (replicateM j boolean)

    andM [andM [ oneM (return <$> gammasC) | gammasC <- transpose gammasM ]
         ,andM [ ep ==> oneM (return <$> gammasR)
                     | (ep, gammasR) <- zip epsilons gammasM]
         ,k epsilons gammasM]

-- ---------------------
-- LPO with permutation
-- ---------------------
newtype LPOPSymbol a = LPOP{unLPOP::Symbol a} deriving (Eq, Ord, Show, Ppr, SATOrd)

instance Decode (LPOPSymbol a) (SymbolRes a) where decode = decode . unLPOP

lpopSymbol sig = liftM LPOP . symbol sig

instance Eq a => Extend (LPOPSymbol a) where
  exeq s t = lexpeq (encodePerm $ unLPOP s) (encodePerm $ unLPOP t)
  exgt s t = lexpgt (encodePerm $ unLPOP s) (encodePerm $ unLPOP t)

lexpeq ff gg ss tt
      | n /= m = constant False
      | otherwise
      = andM [ and [f_ik, g_jk] ==>> s_i ~~ t_j
             | (s_i, f_i) <- zip ss ff
             , (t_j, g_j) <- zip tt gg
             , (f_ik, g_jk) <- zip f_i g_j]
     where (n,m) = (length ss, length tt)

lexpgt ff gg ss tt = exgt_k (transpose ff) (transpose gg)
     where
       n = length ss
       m = length tt
       exgt_k [] _ = constant False
       exgt_k _ [] = constant True
       exgt_k (f_k:ff) (g_k:gg)
         = orM [andM [ return f_ik
                     , andM [ g_jk ==>
                               orM [ s_i > t_j
                                    , andM [ s_i ~~ t_j
                                           , exgt_k ff gg]]
                            | (g_jk, t_j) <- zip g_k tt]]
                | (f_ik, s_i) <- zip f_k ss]

-- ------------
-- All together
-- ------------

instance Eq a => Extend (Symbol a) where
  exeq s t ss tt =
      orM [andM [return (encodeUseMset s), return (encodeUseMset t), muleq ss tt]
          ,andM [return (not$ encodeUseMset s), return (not$ encodeUseMset t),
                       lexpeq (encodePerm s) (encodePerm t) ss tt]
          ]
  exgt s t ss tt =
      orM [andM [return (encodeUseMset s), return (encodeUseMset t), mulgt ss tt]
          ,andM [return (not$ encodeUseMset s), return (not$ encodeUseMset t),
                       lexpgt (encodePerm s) (encodePerm t) ss tt]
          ]

-- test
-- -----
{-
check_lpo solver trs = do
  mb_prec <- solver (lpo trs)
  case mb_prec of
       Nothing -> return True
       Just prec -> do
         let dict       = Map.fromList prec
         let symb_rules = mapTermSymbols (\f -> fromJust $ Map.lookup f dict) <$$> rules trs
         return $ Prelude.and [l `clpo` r | l:->r <- symb_rules]

clpo s t
   | Just id_t <- rootSymbol t, tt_t <- directSubterms t
   =    all (clpo s) tt_t
     && (id_s Prelude.> id_t || (id_s == id_t && lexD clpo tt_s tt_t))

   | otherwise = any (\x -> x == t || clpo x t) tt_s

     where Just id_s   = rootSymbol s
           tt_s        = directSubterms s
-}