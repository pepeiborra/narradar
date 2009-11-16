{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, UndecidableInstances, TypeSynonymInstances #-}
{-# LANGUAGE RecordWildCards, NamedFieldPuns, DisambiguateRecordFields #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Narradar.Constraints.SAT.RPO where

import Control.Applicative ((<$>))
import qualified Control.Exception as CE
import Control.Monad.Identity
import Control.Monad.List
import Control.Monad.State
import Data.Foldable (Foldable, toList)
import Data.List (transpose,(\\))
import Data.Maybe
import Data.Typeable
import qualified Data.Map as Map
import qualified Data.Set as Set

import qualified Narradar.Constraints.RPO as RPO (RPO(..), symbolRPO)
import Narradar.Constraints.SAT.Common
import Narradar.Types hiding (symbol, constant)
import Narradar.Utils
import Narradar.Framework.Ppr

import qualified Prelude as P
import Prelude hiding (catch, lex, not, and, or, (>))

lpoDP  = rpoGen lpoSymbol
mpoDP  = rpoGen mpoSymbol
lposDP = rpoGen lpopSymbol
rpoDP  = rpoGen symbol

rpoGen inn p = runSAT $ do
  let sig  = getSignature p
      ids  = getArities sig
      bits = calcBitWidth $ Map.size ids

  symbols <- mapM (inn bits) (Map.toList ids)
  let dict       = Map.fromList (zip (Map.keys ids) symbols)
      symb_rules = mapTermSymbols (\f -> fromJust $ Map.lookup f dict) <$$> rules (getR p)
      symb_pairs = mapTermSymbols (\f -> fromJust $ Map.lookup f dict) <$$> rules (getP p)

  decreasing_dps <- replicateM (length symb_pairs) boolean
  problem <- andM
            ( or decreasing_dps :
              [ (l >~ r)  | l:->r <- symb_rules] ++
              [ (l >~ r) | l:->r <- symb_pairs] ++
              [(l > r) <==> return dec | (l:->r, dec) <- zip symb_pairs decreasing_dps])

  assert [problem]

  return $ do syms  <- mapM decode symbols
              dec_bools <- decode decreasing_dps
              let non_dec_pairs = [ r | (r,False) <- zip [0..] dec_bools]
              return (non_dec_pairs, syms)

rpoTestGen inn rr = runSAT $ do
  let sig  = getSignature rr
      ids  = getArities sig
      bits = calcBitWidth $ Map.size ids
  symbols <- mapM (inn bits) (Map.toList ids)
  let dict       = Map.fromList (zip (Map.keys ids) symbols)
      symb_rules = mapTermSymbols (\f -> fromJust $ Map.lookup f dict) <$$> rules rr

  sequence_ $ do
    (l :-> r) <- symb_rules
    return (l>r >>= \it -> assert [it])

  return $ mapM decode symbols

-- ----------------------------------------------------------------
-- The Recursive Path Ordering, parametric w.r.t the extension
-- ----------------------------------------------------------------

instance (id ~ TermId f, id ~ symbol a
         ,Eq v, Ord (Term f v), Foldable f, Pretty (Term f v)
         ,HasId f, SATOrd (SAT a (Term f v)) id, Pretty id, Extend id) =>
    SATOrd (SAT a (Term f v)) (Term f v) where
  s ~~ t | s == t = constant True
  s ~~ t =  memoTerm (s :~~ t) $
            fromMaybe (constant False) $ do
             id_s <- rootSymbol s
             id_t <- rootSymbol t
             return $ andM [ id_s ~~ id_t
                           , exeq id_s id_t (directSubterms s) (directSubterms t)]

  s > t
   | s == t = constant False
   | Just id_t <- rootSymbol t, tt_t <- directSubterms t
   , Just id_s <- rootSymbol s, tt_s <- directSubterms s
   = memoTerm (s :> t) $
     orM [ anyM (>~ t) tt_s
         , andM [allM (s >) tt_t
                ,orM [id_s > id_t
                     ,andM [id_s ~~ id_t, exgt id_s id_t tt_s tt_t]
                     ]
                ]
         ]

   | Just id_s <- rootSymbol s, tt_s <- directSubterms s
   = memoTerm (s :> t) $
     anyM (>~ t) tt_s

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

  deriving (Eq, Ord, Show, Typeable)


instance Show a => Show (Symbol a) where
    show Symbol{the_symbol} = show the_symbol

instance Pretty a => Pretty (Symbol a) where
    pPrint Symbol{the_symbol} = pPrint the_symbol

instance Pretty a => Pretty (SymbolRes a) where
    pPrint SymbolRes{the_symbolR} = pPrint the_symbolR

instance Eq   a => Eq   (Symbol a) where
    a@Symbol{} == b@Symbol{} = the_symbol a == the_symbol b

instance Ord a => Ord (Symbol a) where
   compare a b = the_symbol a `compare` the_symbol b

instance Decode (Symbol a) (SymbolRes a) where
    decode x@Symbol{} = decodeSymbol x

instance HasPrecedence (SymbolRes a) where precedence = Narradar.Constraints.SAT.RPO.precedence
instance HasStatus (SymbolRes a) where status = Narradar.Constraints.SAT.RPO.status


symbol bits (x,ar) = do
  n <- number bits
  perm <- replicateM ar (replicateM ar boolean)
  mset <- boolean

  -- Permutation invariants
  assertAll $ map oneM perm
  assertAll $ map oneM (transpose perm)

  let s = Symbol
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
  return s

instance Ord id => SATOrd (SAT id t) (Symbol id) where
    a ~~ b
        | a == b    = constant True
        | otherwise = memoSym (the_symbol a :~~ the_symbol b)
                      (encodePrec a `eq` encodePrec b)

    a >  b
        | a == b    = constant False
        | otherwise = memoSym (the_symbol a :> the_symbol b)
                      (encodePrec a `gt` encodePrec b)


-- ------------
-- LPO and MPO
-- ------------

newtype LPOSymbol a = LPO{unLPO::Symbol a} deriving (Eq, Ord, Show, Pretty, SATOrd (SAT a t))
newtype MPOSymbol a = MPO{unMPO::Symbol a} deriving (Eq, Ord, Show, Pretty, SATOrd (SAT a t))

instance Decode (LPOSymbol a) (SymbolRes a) where decode = liftM removePerm . decode . unLPO
instance Decode (MPOSymbol a) (SymbolRes a) where decode = decode . unMPO

removePerm symbolRes@SymbolRes{status=Lex _} = symbolRes{Narradar.Constraints.SAT.RPO.status = Lex Nothing}
removePerm symbolRes = symbolRes

lpoSymbol bits x = do
  s <- symbol bits x
  assert [not $ encodeUseMset s]
  return (LPO s)

mpoSymbol bits x = do
  s <- symbol bits x
  assert [encodeUseMset s]
  return (MPO s)

instance Eq a => Extend (LPOSymbol a) where
    exgt _ _ = lexgt
    exeq _ _ = lexeq

instance Eq a => Extend (MPOSymbol a) where
    exgt _ _ = mulgt
    exeq _ _ = muleq


--lexgt, lexeq :: (SATOrd m a, Eq a) => [a] -> [a] -> m Boolean

lexgt []     _      = constant False
lexgt _      []     = constant True
lexgt (f:ff) (g:gg) = orM [ f > g
                          , andM [f ~~ g, lexgt ff gg]
                          ]
lexeq []      []    = constant True
lexeq (f:ff) (g:gg) = andM [ f ~~ g, lexeq ff gg]
lexeq _      _      = constant False

--muleq, mulge, mulgt :: (SATOrd m a, Eq a) => [a] -> [a] -> m Boolean

mulge ff gg = mulgen (i, j) $ mulgeF ff gg
 where
  (i, j) = (length ff, length gg)


mulgt ff gg = mulgen (i, j) $ \epsilons gammas ->
                     andM [mulgeF ff gg epsilons gammas, notM $ and epsilons]
 where
  (i, j) = (length ff, length gg)


muleq ff gg = mulgen (i, j) $ \epsilons gammas ->
                    andM [mulgeF ff gg epsilons gammas, and epsilons]
 where
  (i, j) = (length ff, length gg)

mulgeF ff gg epsilons gammasM =
    andM [ gamma_ij ==> ifM' ep_i (f_i ~~ g_j) (f_i > g_j)
           | (ep_i, gamma_i, f_i) <- CE.assert (length epsilons == length ff) $
                                        zip3 epsilons gammasM ff
           , (gamma_ij, g_j) <- zip gamma_i gg]

mulgen (i, j) k = do
    epsilons <- replicateM i boolean
    gammasM  <- replicateM i (replicateM j boolean)

    assertAll [ oneM gammasC | gammasC <- transpose gammasM ]
    assertAll [ ep_i ==> oneM gamma_i
                     | (ep_i, gamma_i) <- zip epsilons gammasM]
    k epsilons gammasM

-- ---------------------
-- LPO with permutation
-- ---------------------
newtype LPOPSymbol a = LPOP{unLPOP::Symbol a} deriving (Eq, Ord, Show, Pretty, SATOrd (SAT a t))

instance Decode (LPOPSymbol a) (SymbolRes a) where decode = decode . unLPOP

lpopSymbol bits = liftM LPOP . symbol bits

instance Eq a => Extend (LPOPSymbol a) where
   exeq s t = lexpeq (encodePerm $ unLPOP s) (encodePerm $ unLPOP t)
   exgt s t = lexpgt (encodePerm $ unLPOP s) (encodePerm $ unLPOP t)

lexpeq ff gg ss tt
      | n /= m = constant False
      | otherwise
      = andM [ [f_ik, g_jk] *==> s_i ~~ t_j
                 | (s_i, f_i) <- zip ss ff
                 , (t_j, g_j) <- zip tt gg
                 , (f_ik, g_jk) <- zip f_i g_j]
     where (n,m) = (length ss, length tt)

lexpgt enc_f enc_g ss tt = exgt_k (transpose enc_f) (transpose enc_g)
     where
       n = length ss
       m = length tt
       exgt_k [] _ = constant False
       exgt_k _ [] = constant True
       exgt_k (f_k:ff) (g_k:gg)
         = orM [andMemo [f_ik] $
                withFalse ((f_k \\ [f_ik]) ++ (f_i \\ [f_ik])) False $
                      andM [ [g_jk] *==>
                               orM [ s_i > t_j
                                  , andM [ s_i ~~ t_j
                                         , exgt_k ff gg]]
                            | (g_jk, t_j) <- zip g_k tt]
                | (f_i,f_ik, s_i) <- zip3 enc_f f_k ss]

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

-}

-- Verification
-- ------------

verifyRPO :: forall typ trs t v a k.
          (trs ~ NTRS (SymbolRes a)
          ,MkDPProblem typ trs
          ,Ord a, Pretty a
          ,HasSignature (Problem typ trs), SignatureId (Problem typ trs) ~ SymbolRes a
          ,NUsableRules (SymbolRes a) (typ, trs, trs)
          ) => Problem typ (NTRS a) -> [SymbolRes a] -> [Int] -> VerifyRPOAF (RuleN (SymbolRes a))

verifyRPO p0 symbols nondec_pairs = runIdentity $ do

  falseDecreasingPairs <- runListT $ do
    s:->t <- li the_dps
    guard =<< lift(liftM P.not(s > t))
    return (s:->t)
  falseWeaklyDecreasingRules <- runListT $ do
    s:->t <- li $ rules(getR p)
    guard =<< lift(liftM P.not(s >~ t))
    return (s:->t)
  let missingUsableRules = []
      excessUsableRules  = []

  return VerifyRPOAF{..}
 where

  RPO.RPO{..} = RPO.symbolRPO

  p             = fmap (mapNarradarTRS (mapTermSymbols convertSymbol)) p0
  convertSymbol = fromJust . (`Map.lookup` Map.fromList [(the_symbolR s, s) | s <- symbols])

  all_dps = rules (getP p)
  the_dps = select ([0..length all_dps - 1] \\ nondec_pairs) all_dps

  li = ListT . return