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
import Narradar.Constraints.SAT.Examples hiding (gt, div)
import Narradar.Types hiding (symbol, constant)
import Narradar.Utils
import Narradar.Utils.Ppr

import qualified Prelude
import Prelude hiding (lex, not, and, or, (>))

-- ----------------------------------------------------------------
-- The Recursive Path Ordering, parametric w.r.t the extension
-- ----------------------------------------------------------------

instance (Eq v, Eq (Term f v), Foldable f,
          HasId f id, Eq id, SATOrd id, Ppr id, Extend id) =>
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


-- -----------
-- RPO impls.
-- -----------
lpo  = rpoGen lpoSymbol unLPO
mpo  = rpoGen mpoSymbol unMPO
lpop = rpoGen lpopSymbol unLPOP
rpo  = rpoGen symbol id

rpoGen inn out trs = isSAT $ do
  let sig        = getSignature trs
  symbols <- mapM (inn sig) (Set.toList $ getAllSymbols sig)
  let dict       = Map.fromList [(the_symbol $ out s, s) | s <- symbols]
      symb_rules = mapTermSymbols (\f -> fromJust $ Map.lookup f dict) <$$> rules trs
  (assert . (:[])) =<< andM [ l > r | l:->r <- symb_rules]
  return $ mapM (secondM decode) (Map.toList dict)

-- -------------------------------------------------
-- The symbol datatype encoding all the constraints
-- -------------------------------------------------
data Symbol a = Constant a
              | Symbol { the_symbol   :: a
                       , encodePrec   :: Number
                       , encodePerm   :: [[Boolean]]
                       , encodeUseMset:: Boolean
                       , decodeSymbol :: Decoder Integer}

instance Show a => Show (Symbol a) where
    show Symbol{the_symbol} = show the_symbol
    show (Constant x)       = show x

instance Ppr a => Ppr (Symbol a) where
    ppr Symbol{the_symbol} = ppr the_symbol
    ppr (Constant x)       = ppr x

instance Eq   a => Eq   (Symbol a) where
    a@Symbol{} == b@Symbol{} = the_symbol a == the_symbol b
    Constant a == Constant b = a == b
    _          == _          = False

instance Decode (Symbol a) Integer where
    decode Constant{} = error "Constants cannot be decoded"
    decode x@Symbol{} = decodeSymbol x


symbol sig x = do
  n <- number (length $ takeWhile (Prelude.>0) $ iterate (`div` 2) $ Set.size (getDefinedSymbols sig))
  let ar = getArity sig x
  perm <- replicateM ar (replicateM ar boolean)
  mset <- boolean

  -- Permutation invariants
  assertAll [ oneM perm_i | perm_i <- perm]
  assertAll [ oneM perm_k | perm_k <- transpose perm]

  return $ Symbol
             { the_symbol = x
             , encodePrec = n
             , encodePerm = perm
             , encodeUseMset = mset
             , decodeSymbol = decode n
             }

instance Eq a => SATOrd (Symbol a) where
    a ~~ b = encodePrec a `eq` encodePrec b
    a >  b = encodePrec a `gt` encodePrec b


-- ------------
-- LPO and MPO
-- ------------

newtype LPOSymbol a = LPO{unLPO::Symbol a} deriving (Eq, Show, Ppr, SATOrd)
newtype MPOSymbol a = MPO{unMPO::Symbol a} deriving (Eq, Show, Ppr, SATOrd)

instance Decode (LPOSymbol a) Integer where decode = decode . unLPO
instance Decode (MPOSymbol a) Integer where decode = decode . unMPO

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

    andM [andM [ oneM gammasC | gammasC <- transpose gammasM ]
         ,andM [ ep ==> oneM gammasR
                     | (ep, gammasR) <- zip epsilons gammasM]
         ,k epsilons gammasM]

-- ---------------------
-- LPO with permutation
-- ---------------------
newtype LPOPSymbol a = LPOP{unLPOP::Symbol a} deriving (Eq, Show, Ppr, SATOrd)

instance Decode (LPOPSymbol a) Integer where decode = decode . unLPOP

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
