{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances, TypeSynonymInstances #-}
{-# LANGUAGE RecordWildCards, NamedFieldPuns, DisambiguateRecordFields #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternGuards, ViewPatterns #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Narradar.Constraints.SAT.RPOAF where

import Control.Applicative
import qualified Control.Exception as CE
import Control.Monad
import Control.Monad.Identity
import Control.Monad.List
import qualified Control.RMonad as R
import qualified Data.Array as A
import Data.Foldable (Foldable, foldMap, toList)
import Data.List ((\\), transpose, inits, zip4)
import Data.Maybe
import Data.Monoid
import Data.Typeable
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Traversable (Traversable)
import Narradar.Framework.Ppr as Ppr

import qualified Satchmo.Boolean as Satchmo
import Narradar.Constraints.SAT.Common
import qualified Narradar.Constraints.RPO as RPO
import Narradar.Types hiding (symbol, constant)
import Narradar.Types.Problem.InitialGoal
import Narradar.Utils
import qualified Narradar.Types.ArgumentFiltering as AF

import qualified Prelude as P
import Prelude hiding (catch, lex, not, and, or, quot, (>))


-- | RPO + AF

rpoAF rpo allowCol trs = runRPOAF rpo allowCol (getSignature trs) $ \dict -> do
  let symb_rules = mapTermSymbols (\f -> fromJust $ Map.lookup f dict) <$$> rules trs
  problem <- andM [ l > r | l:->r <- symb_rules]
  assert [problem]
  return (return ())


-- | RPO + AF + Usable Rules
rpoAF_DP col ex p = rpoAF_DP' col ex p

rposAF_DP col p = rpoAF_DP' col rpos p
lposAF_DP col p = rpoAF_DP' col lpos p
lpoAF_DP col p = rpoAF_DP' col (lpo) p
mpoAF_DP col p = rpoAF_DP' col (mpo) p


-- | Returns the indexes of non decreasing pairs and the symbols used
rpoAF_DP' allowCol con p
  | _ <- isNarradarTRS1 (getR p)
  = runRPOAF con allowCol (getSignature p) $ \dict -> do
  let convert = mapTermSymbols (\f -> fromJust $ Map.lookup f dict)
      trs' = mapNarradarTRS convert (getR p)
      dps' = mapNarradarTRS convert (getP p)
      p'   = mkDPProblem (getProblemType p) trs' dps'
  decreasing_dps <- replicateM (length $ rules dps') boolean

  assertAll [omega p']
  assertAll [ l >~ r | l:->r <- rules dps']
  assertAll [(l > r) <<==>> return dec | (l:->r, dec) <- zip (rules dps') decreasing_dps]
  assertAll [or decreasing_dps]

  return $ do
    decreasing <- decode decreasing_dps
    let the_non_decreasing_pairs = [ r | (r,False) <- zip [0..] decreasing]
    return the_non_decreasing_pairs


rpoAF_IGDP :: (Ord id, Ord sid, Pretty sid, AFSymbol sid, UsableSymbol sid, Extend sid, SATOrd (SAT id (TermN sid)) sid
              ,sid ~ symbol id
              ,Traversable (Problem base), Pretty base
              ,MkDPProblem base (NTRS sid)
              ,Decode sid (SymbolRes id)
              ,HasSignature (Problem base (NTRS id)),  id  ~ SignatureId (Problem base (NTRS id))
              ,HasSignature (Problem base (NTRS sid)), sid ~ SignatureId (Problem base (NTRS sid))
              ,NUsableRules sid (base, NTRS sid, NTRS sid)
              ,NCap sid (base, NTRS sid)
              ,Omega (InitialGoal (TermF sid) base) (TermF sid)
              ,DPSymbol id, Pretty id
              ) => Bool -> (Int -> (id,Int) -> SAT id (TermN (symbol id)) (symbol id))
                -> NProblem (InitialGoal (TermF id) base) id
                -> Satchmo.SAT (Decoder ([Int],[SymbolRes id]))

rpoAF_IGDP allowCol con p@InitialGoalProblem{..}
  | _ <- isTheRightKind (getProblemType p)
  , _ <- isNarradarTRS1 (getR p)
  , _ <- mkTRS[head goals :-> head goals] `asTypeOf` getR p
  = runRPOAF con allowCol (getSignature p `mappend` getSignature (A.elems $ pairs dgraph)) $ \dict -> do
  let convert = mapTermSymbols (\f -> fromJust $ Map.lookup f dict)
      trs' = mapNarradarTRS convert (getR p)
      dps' = mapNarradarTRS convert (getP p)
      typ' = InitialGoal (map convert goals)
                         (Just $ R.fmap (fmap convert) dgraph)
                         (getProblemType baseProblem)
      p'   = mkDPProblem typ' trs' dps'
  decreasing_dps    <- replicateM (length $ rules dps') boolean
  assert decreasing_dps
  assertAll (omega  p' :
             [ l >~ r | l:->r <- rules dps'] ++
             [(l > r) <=^=> return v | (l:->r, v) <- zip (rules dps') decreasing_dps]
            )

  return $ do
    decreasing <- decode decreasing_dps
    return [ r | (r,False) <- zip [0..] decreasing]

 where isTheRightKind :: InitialGoal (f id) base -> InitialGoal (f id) base
       isTheRightKind = id

rpoAF_NDP allowCol con p
  | _ <- isNarradarTRS1 (getR p)
  = runRPOAF con allowCol (getSignature p) $ \dict -> do
  let convert = mapTermSymbols (\f -> fromJust $ Map.lookup f dict)
      trs' = mapNarradarTRS convert (getR p)
      dps' = mapNarradarTRS convert (getP p)
      p'   = mkDPProblem (getProblemType p) trs' dps'
  decreasing_dps    <- replicateM (length $ rules dps') boolean
  af_ground_rhs_dps <- replicateM (length $ rules dps') boolean

  assertAll (or_ decreasing_dps :
             or_ af_ground_rhs_dps :
             omega  p' :
             [ l >~ r | l:->r <- rules dps'] ++
             [(l > r)       <=^=> return v | (l:->r, v) <- zip (rules dps') decreasing_dps] ++
             [afGroundRHS r <=^=> return v | (r, v)     <- zip (rules dps') af_ground_rhs_dps]
            )

  return $ do
    decreasing <- decode decreasing_dps
    af_ground  <- decode af_ground_rhs_dps
    return ([ r | (r,False) <- zip [0..] decreasing]
           ,[ r | (r,False) <- zip [0..] af_ground])

runRPOAF con allowCol sig f = runSAT' $ do
  let ids  = getArities sig
      bits = calcBitWidth $ Map.size ids

  symbols <- mapM (con bits) (Map.toList ids)
  if allowCol
    then assertAll [[listAF s] ^!==> oneM [inAF i s | i <- [1..a]]
                    | (s,a) <- zip symbols (Map.elems ids)]
    else mapM_ (assertMemo . listAF) symbols

  let dict       = Map.fromList (zip (Map.keys ids) symbols)
  res <- f dict
  return $ do res' <- res
              syms <- mapM decode (Map.elems dict)
              return (res',syms)

-- -------------------------------------------------
-- Encoding of RPO symbols with AF and usable rules
-- -------------------------------------------------

data SymbolRes a = SymbolRes { the_symbolR:: a
                             , precedence :: Int
                             , isUsable   :: Bool
                             , status     :: Status
                             , filtering  :: Either Int [Int] }
  deriving (Eq, Ord, Show, Typeable)

instance Functor SymbolRes where fmap f SymbolRes{..} = SymbolRes{the_symbolR = f the_symbolR, ..}

instance Pretty a => Pretty (SymbolRes a) where
    pPrint SymbolRes{the_symbolR} = pPrint the_symbolR

instance HasPrecedence (SymbolRes a) where precedence = Narradar.Constraints.SAT.RPOAF.precedence
instance HasStatus     (SymbolRes a) where status     = Narradar.Constraints.SAT.RPOAF.status

data Symbol a = Symbol { the_symbol   :: a
                       , encodePrec   :: Number
                       , encodeUsable :: Boolean
                       , encodeAFlist :: Boolean
                       , encodeAFpos  :: [Boolean]
                       , encodePerm   :: [[Boolean]]
                       , encodeUseMset:: Boolean
                       , decodeSymbol :: Decoder (SymbolRes a)}

instance Show a => Show (Symbol a) where
    show Symbol{the_symbol} = show the_symbol

instance Pretty a => Pretty (Symbol a) where
    pPrint Symbol{the_symbol} = pPrint the_symbol

instance Eq   a => Eq   (Symbol a) where
    a@Symbol{} == b@Symbol{} = the_symbol a == the_symbol b

instance Ord a => Ord (Symbol a) where
   compare a b = the_symbol a `compare` the_symbol b

instance Decode (Symbol a) (SymbolRes a) where decode = decodeSymbol

instance Functor Symbol where fmap f Symbol{..} = Symbol{the_symbol = f the_symbol, decodeSymbol = fmap2 f decodeSymbol, ..}
instance Foldable Symbol where foldMap f Symbol{..} = f the_symbol

instance GenSymbol a => GenSymbol (Symbol a) where
    genSymbol  = mkGenSymbol genSymbol
    goalSymbol = mkGenSymbol goalSymbol

mkGenSymbol a = Symbol{ the_symbol = a
                      , encodePrec = error "RPOAF.Symbol : genSymbol"
                      , encodeUsable = error "RPOAF.Symbol : genSymbol"
                      , encodeAFlist = error "RPOAF.Symbol : genSymbol"
                      , encodeAFpos  = error "RPOAF.Symbol : genSymbol"
                      , encodePerm   = []
                      , encodeUseMset= error "RPOAF.Symbol : genSymbol"
                      , decodeSymbol = return (SymbolRes genSymbol 0 False (Lex Nothing) (Right []))
                      }


rpos bits (x,ar) = do
  n_b      <- number bits
  perm_bb  <- replicateM ar (replicateM ar boolean)
  mset     <- boolean
  (list_b:pos_bb) <- case ar of
                       0 -> (:[]) `liftM` constant True
                       _ -> replicateM (ar + 1) boolean
  usable_b <- boolean

  -- Permutation invariants
  -- -----------------------
  -- There is one or zero arguments considered at the k'th perm position,
  assertAll [ or perm_k ==>> oneM perm_k
             | perm_k <- transpose perm_bb]
  -- Filtered arguments may not be used in the permutation
  assertAll [ not p ==> and (not <$> perm_i) | (p, perm_i) <- zip pos_bb perm_bb]
  -- Non filtered arguments are considered at exactly one position in the permutation
  assertAll [ p ==> oneM perm_i | (p, perm_i) <- zip pos_bb perm_bb]
  -- All non-filtered arguments are permuted 'to the left'
  assertAll [ or perm_k1 ==>> or perm_k
                  | (perm_k, perm_k1) <- zip (transpose perm_bb) (tail $transpose perm_bb)]

  return $ Symbol
             { the_symbol   = x
             , encodePrec   = n_b
             , encodeUsable = usable_b
             , encodeAFlist = list_b
             , encodeAFpos  = pos_bb
             , encodePerm = perm_bb
             , encodeUseMset = mset
             , decodeSymbol = do
                 n      <- fromInteger `liftM` decode n_b
                 isList <- decode list_b
                 pos    <- decode pos_bb
                 isUsable <- decode usable_b
                 status   <- decode mset
                 perm_bools <- decode perm_bb
                 let the_positions = [fromInteger i | (i,True) <- zip [1..] pos]
                     statusMsg   = mkStatus status perm_bools
                 return$
                  if P.not isList
                   then CE.assert (length the_positions == 1)
                        (SymbolRes x n isUsable statusMsg (Left $ head the_positions))
                   else (SymbolRes x n isUsable statusMsg (Right the_positions))
             }

class AFSymbol a where
    listAF :: a -> Boolean
    inAF   :: Int -> a -> Boolean

instance AFSymbol (Symbol a) where
   listAF     = encodeAFlist
   inAF j sym = encodeAFpos sym !! (j-1)

class UsableSymbol a where usable :: a -> SAT id t Boolean
instance UsableSymbol (Symbol a) where usable = return . encodeUsable

instance Ord a => SATOrd (SAT a t) (Symbol a) where
  a > b  | a == b    = constant False
         | otherwise = memoSym (the_symbol a :> the_symbol b)
                       (encodePrec a `gt` encodePrec b)
  a ~~ b | a == b    = constant True
         | otherwise = memoSym (the_symbol a :~~ the_symbol b)
                       (encodePrec a `eq` encodePrec b)

instance Ord a => Extend (Symbol a) where
  exeq s t ss tt =
      orM [andM [return (encodeUseMset s), return (encodeUseMset t), muleq s t ss tt]
           ,andM [return (not$ encodeUseMset s), return (not$ encodeUseMset t),
                        lexpeq s t ss tt]
          ]
  exgt s t ss tt =
      orM [andM [return (encodeUseMset s), return(encodeUseMset t), mulgt s t ss tt]
           ,andM [return (not$ encodeUseMset s), return (not$ encodeUseMset t),
                       lexpgt s t ss tt]
          ]

-- --------
-- Variants
-- --------

-- LPO with status

newtype LPOSsymbol a = LPOS{unLPOS::Symbol a} deriving (Eq, Ord, Show, SATOrd (SAT a t), AFSymbol, UsableSymbol, GenSymbol, Functor, Foldable)
instance Decode (LPOSsymbol a) (SymbolRes a) where decode = decode . unLPOS

lpos sig = liftM LPOS . rpos sig

instance Eq a => Extend (LPOSsymbol a) where
  exeq s t = lexpeq (unLPOS s) (unLPOS t)
  exgt s t = lexpgt (unLPOS s) (unLPOS t)

instance Pretty a => Pretty (LPOSsymbol a) where
    pPrint = pPrint . unLPOS


newtype LPOsymbol a = LPO{unLPO::Symbol a} deriving (Eq, Ord, Show, SATOrd (SAT a t), AFSymbol, UsableSymbol, GenSymbol, Functor, Foldable)
instance Decode (LPOsymbol a) (SymbolRes a) where decode = liftM removePerm . decode . unLPO

removePerm symbolRes@SymbolRes{status=Lex _} = symbolRes{Narradar.Constraints.SAT.RPOAF.status = Lex Nothing}
removePerm symbolRes = symbolRes

lpo sig x = do
  s <- rpos sig x
  return (LPO s)

instance Eq a => Extend (LPOsymbol a) where
  exeq s t = lexeq (unLPO s) (unLPO t)
  exgt s t = lexgt (unLPO s) (unLPO t)

instance Pretty a => Pretty (LPOsymbol a) where pPrint = pPrint . unLPO

-- MPO
newtype MPOsymbol a = MPO{unMPO::Symbol a} deriving (Eq, Ord, Show, SATOrd (SAT a t), AFSymbol, UsableSymbol, GenSymbol, Functor, Foldable)
instance Decode (MPOsymbol a) (SymbolRes a) where decode = decode . unMPO

instance Pretty a => Pretty (MPOsymbol a) where
    pPrint = pPrint . unMPO

mpo sig x = do
  s <- rpos sig x
  assert [encodeUseMset s]
  return (MPO s)

instance Eq a => Extend (MPOsymbol a) where
  exeq s t = muleq (unMPO s) (unMPO t)
  exgt s t = mulgt (unMPO s) (unMPO t)

-- -----------
-- RPO with AF
-- -----------
instance ( id ~ TermId f
         , id ~ symbol a
         , Eq v, Ord (Term f v), Foldable f, HasId f, Eq id
         , SATOrd (SAT a (Term f v)) id, AFSymbol id, Extend id) =>
    SATOrd (SAT a (Term f v)) (Term f v) where
 s > t
   | s == t = constant False
   | Just id_t <- rootSymbol t, tt_t <- directSubterms t
   , Just id_s <- rootSymbol s, tt_s <- directSubterms s
   = memoTerm (s:>t) $
     orM [cond1 id_s id_t tt_s tt_t,  cond2 id_s tt_s]

   | Just id_s <- rootSymbol s, tt_s <- directSubterms s
   = memoTerm (s:>t) $
     cond2 id_s tt_s

   | otherwise = constant False

     where
       cond1 id_s id_t tt_s tt_t
         = andM[ allM (\(t_j, j) -> [inAF j id_t] *==> s > t_j)
                      (zip tt_t [1..])
               , [listAF id_t] *==> andMemo [listAF id_s]
                                            (orM[ id_s > id_t
                                                , andM[ id_s ~~ id_t
                                                      , exgt id_s id_t tt_s tt_t]
                                                ])
               ]

       cond2 id_s tt_s =
          anyM (\(s_i,i) ->
                 andMemo [inAF i id_s] $
                          orM[ s_i > t
                             , andMemo[listAF id_s] (s_i ~~ t)
                             ]
               )
               (zip tt_s [1..])

 Pure s ~~ Pure t = constant(s == t)
 s ~~ t
   | s == t  = constant True
   | isVar s = memoTerm (s :~~ t) $
               andMemoNeg [listAF id_t] $
                           allM (\(t_j,j) -> [inAF j id_t] *==>
                                             (s ~~ t_j)
                                )
                                (zip tt [1..])
   | isVar t = memoTerm (s :~~ t) $
               andMemoNeg [listAF id_s] $
                          allM (\(s_i,i) -> [inAF i id_s] *==>
                                            (s_i ~~ t)
                               ) (zip ss [1..])
   | id_s == id_t
   = memoTerm (s :~~ t) $
     andM[ [listAF id_s]   !==> allM (\(s_i,i) -> [inAF i id_s] *==> s_i ~~ t) (zip ss [1..])
         , [listAF id_s]   *==> andM[ id_s ~~ id_t, exeq id_s id_t ss tt]
         ]

   | otherwise
   = memoTerm (s :~~ t) $
     andM[ [listAF id_s]                  !==> allM (\(s_i,i) -> [inAF i id_s] *==> s_i ~~ t) (zip ss [1..])
         , ([listAF id_s],[listAF id_t]) *!==> allM (\(t_j,j) -> [inAF j id_t] *==> t_j ~~ s) (zip tt [1..])
         , [listAF id_s,listAF id_t]      *==> andM[ id_s ~~ id_t, exeq id_s id_t ss tt]
         ]
   where
        ss = directSubterms s
        tt = directSubterms t
        ~(Just id_s) = rootSymbol s
        ~(Just id_t) = rootSymbol t

-- -------------------------
-- Narrowing related stuff
-- -------------------------
afGroundRHS (_ :-> t) = andM [ or [ not(inAF i f)
                                    | prefix <- tail $ inits pos
                                    , let Just f = rootSymbol (t ! init prefix)
                                    , let      i = last prefix]
                               | pos <- [noteV v | v <- vars(annotateWithPos t)]]

-- -----------------------------------
-- Lexicographic extension with AF
-- -----------------------------------

lexgt id_f id_g ff gg = go (zip ff [1..]) (zip gg [1..]) where
  go []     []     = constant False
  go []     _      = constant False
  go _      []     = constant True
  go ((f,i):ff) ((g,j):gg)
    =  ifMemo(inAF i id_f)
             (ifMemo (inAF j id_g)
                     (orM[f > g, andM[f ~~ g, go ff gg]])
                     (go ((f,i):ff) gg))
             (go ff ((g,j):gg))

lexeq id_f id_g ff gg = go (zip ff [1..]) (zip gg [1..]) where
  go []         []         = constant True
  go ((f,i):ff) ((g,j):gg)
    = ifMemo (inAF i id_f)
             (ifMemo (inAF j id_g)
                     (andM [f ~~ g, go ff gg])
                     (go ((f,i):ff) gg))
             (go ff ((g,j):gg))
  go _          _  = constant False

lexpeq id_f id_g ss tt =
  andM [ eqArity
       , andM [ [f_ik, g_jk] *==> s_i ~~ t_j
              | (s_i, f_i) <- zip ss ff
              , (t_j, g_j) <- zip tt gg
              , (f_ik, g_jk) <- zip f_i g_j]]
    where
       (ff,gg) = (encodePerm id_f, encodePerm id_g)
       eqArity = andM (take m $ zipWith (<==>) (map or (transpose ff) ++ repeat (constant False))
                                                 (map or (transpose gg) ++ repeat (constant False))
                      )
       m   = max (length ff) (length gg)

lexpgt id_f id_g ss tt = exgt_k (transpose $ enc_f) (transpose $ enc_g)
     where
       enc_f = encodePerm id_f
       enc_g = encodePerm id_g
       n = length ss
       m = length tt
       exgt_k [] _ = constant False
       exgt_k ff [] = allM or ff
       exgt_k (f_k:ff) (g_k:gg)
         = orM [andMemo[f_ik] $
                withFalse ((f_k \\ [f_ik]) ++ (f_i \\ [f_ik])) False $
                       andM [ [g_jk] *==>
                               orM [ s_i > t_j
                                    , andM [ s_i ~~ t_j
                                           , exgt_k ff gg]]
                            | (g_jk, t_j) <- zip g_k tt]
                | (f_i,f_ik, s_i) <- zip3 enc_f f_k ss]

-- ---------------------------
-- Multiset extension with AF
-- ---------------------------

-- We avoid memoizing constraints derived from multiset extensions,
-- There is nothing to win since the involved gammas and epsilons are fresh for
-- every multiset comparison and do not carry over to the rest of the problem

mulgt id_f id_g [] _ = constant False
mulgt id_f id_g ff gg =
    mulgen id_f id_g ff gg (\epsilons ->
                                notM $ andM [inAF i id_f ^==> return ep_i
                                              | (i, ep_i) <- zip [1..] epsilons])
muleq id_f id_g [] [] = constant True
muleq id_f id_g ff gg = do
    mulgen id_f id_g ff gg (\epsilons ->
                                andM_ [inAF i id_f ^==> return ep_i
                                      | (i, ep_i) <- zip [1..] epsilons])

{-
mulgen id_f id_g ff gg k = do
    let (i,j) = (length ff, length gg)
    epsilons <- replicateM i boolean
    gammasM  <- replicateM i (replicateM j boolean)

    andM_(k epsilons :
          [ inAF j id_g ^==> oneM gammas_j
            | (j, gammas_j) <- zip [1..] (transpose gammasM) ] ++
          [ not(inAF i id_f) ^==> and_ (not <$> gammas_i)
            | (i, gammas_i) <- zip [1..] gammasM] ++
          [ not(inAF j id_g) ^==> and_ (not <$> gammas_j)
            | (j, gammas_j) <- zip [1..] (transpose gammasM)] ++
          [ ep_i ^==> oneM gamma_i
                | (ep_i, gamma_i) <- zip epsilons  gammasM] ++
          [ gamma_ij ^==>
                  ifM_' ep_i (f_i ~~ g_j)
                             (f_i > g_j)
                  | (ep_i, gamma_i, f_i) <- zip3 epsilons gammasM ff
                  , (gamma_ij, g_j)      <- zip  gamma_i gg]
         )
-}

mulgen id_f id_g ff gg k = do
    let (i,j) = (length ff, length gg)
    epsilons <- replicateM i boolean
    gammasM  <- replicateM j (replicateM i boolean)

    let gammasM_t = transpose gammasM

        oneCoverForNonFilteredSubterm =
          [ inAF j id_g ^==> oneM gammas_j
            | (j, gammas_j) <- zip [1..] gammasM ]

        filteredSubtermsCannotCover =
          [ not(inAF i id_f) ^==> and_ (not <$> gammas_i)
            | (i, gammas_i) <- zip [1..] gammasM_t]

        noCoverForFilteredSubterms =
          [ not(inAF j id_g) ^==> and_ (not <$> gammas_j)
            | (j, gammas_j) <- zip [1..] gammasM]

        subtermUsedForEqualityCanOnlyCoverOnce =
          [ ep_i ^==> oneM gamma_i
            | (ep_i, gamma_i) <- zip epsilons gammasM_t]

        greaterOrEqualMultisetExtension =
          [ gamma_ij ^==>
                 (ifM_' ep_i (f_i ~~ g_j)
                             (f_i >  g_j))
                  | (ep_i, gamma_i, f_i) <- zip3 epsilons gammasM_t ff
                  , (gamma_ij, g_j)      <- zip  gamma_i gg]

    andM_ (  k epsilons
          :  oneCoverForNonFilteredSubterm
          ++ filteredSubtermsCannotCover
          ++ noCoverForFilteredSubterms
          ++ subtermUsedForEqualityCanOnlyCoverOnce
          ++ greaterOrEqualMultisetExtension
          )


-- ------------------------
-- Usable Rules with AF
-- ------------------------
class Omega typ t where omega :: (TermId t ~ somesymbol id) => Problem typ (NarradarTRS t Var) -> SAT id (Term t Var) Boolean

instance (p  ~ Problem typ
         ,IsDPProblem typ
         ,HasSignature (p trs)
         ,id ~ TermId t, id ~ SignatureId (p trs), id ~ symbol a
         ,v   ~ Var
         ,trs ~ NarradarTRS t v
         ,Traversable p
         ,Ord id, SATOrd (SAT a (Term t v)) id, Extend id, AFSymbol id, UsableSymbol id
         ,Foldable t, HasId t, Ord (Term t v), Pretty id
         ,IUsableRules t v (p trs)
         ) => Omega typ t
 where

  omega p = andM_ [andM_ [go r trs | _:->r <- dps]
                 ,andM_ [ usable f ^==>> andM [ l >~ r | l:->r <- rulesFor f trs]
                              | f <- Set.toList dd ]
                 ,andM_ [notM(usable f) | f <- Set.toList (getDefinedSymbols sig `Set.difference` dd)]
                 ]

   where
    (trs,dps) = (rules $ getR p, rules $ getP p)
    sig = getSignature (getR p)
    dd  = getDefinedSymbols (iUsableRules p (rhs <$> dps) :: p trs)

    go (Pure x) _ = andM $ map usable $ toList $ getDefinedSymbols (iUsableRulesVar (p:: p trs) x)

    go t trs
      | id_t `Set.notMember` dd
      = andM_ [ [inAF i id_t] ^*==> go t_i trs
               | (i, t_i) <- zip [1..] tt ]
      | otherwise
      = andM_ [ usable id_t
             , andM_ [ go r rest | _:->r <- rls ]
             , andM_ [ [inAF i id_t] *==> go t_i rest
                          | (i, t_i) <- zip [1..] tt ]
             ]
       where
         Just id_t = rootSymbol t
         tt        = directSubterms t
         rls       = rulesFor id_t trs
         rest      = trs \\ rls  :: [Rule t Var]

instance (p   ~ Problem (InitialGoal t typ)
         ,id  ~ TermId t, id ~ SignatureId (Problem typ trs), id ~ symbol a
         ,v   ~ Var
         ,trs ~ NarradarTRS t v
         ,MkDPProblem typ trs
         ,HasSignature (Problem typ trs)
         ,Traversable (Problem typ), Traversable t
         ,Ord id, Ord(t(Term t v)), SATOrd (SAT a (Term t v)) id, Extend id, AFSymbol id, UsableSymbol id
         ,Foldable t, HasId t, Pretty id
         ,IUsableRules t v (typ, trs, trs)
         ) => Omega (InitialGoal t typ) t
 where

  omega p = pprTrace (text "dd = " <> pPrint dd) $
             andM_ [andM_ [go l r trs | l:->r <- dps ++ reachablePairs p]
                   ,andM_ [ usable f ^==>> andM_ [ l >~ r | l:->r <- rulesFor f trs]
                               | f <- Set.toList dd ]
                   ,andM_ [notM(usable f) | f <- Set.toList (getDefinedSymbols sig `Set.difference` dd)]
                   ]

   where
    (trs,dps) = (rules $ getR p, rules $ getP p)
    sig = getSignature (getR p)
    dd  = getDefinedSymbols (reachableRules p)
    p'  = setR (reachableRules p) (baseProblem p)

    go l (Pure x) _ =
      -- If there is an extra variable, everything is usable ! (short of calling the police)
        everyM_ poss (\p ->
                      or [ not(inAF i f)
                          | n <- [0..length p - 1], let (pre, i:_) = splitAt n p
                          , let f = fromMaybe (error "omega: fromJust") (rootSymbol (l!pre))])
         ==>> andM_(map usable $ toList $ getDefinedSymbols (getR p))

     where
      poss = occurrences (Pure x) l

    go l t trs
      | id_t `Set.notMember` dd
      = andM_ [ [inAF i id_t] ^*==> go l t_i trs
               | (i, t_i) <- zip [1..] tt ]
      | otherwise
      = andM_ [ usable id_t
             , andM_ [ go l r rest | l:->r <- rls ]
             , andM_ [ [inAF i id_t] ^*==> go l t_i rest
                          | (i, t_i) <- zip [1..] tt ]
             ]
       where
         Just id_t = rootSymbol t
         tt        = directSubterms t
         rls       = rulesFor id_t trs
         rest      = trs \\ rls  :: [Rule t Var]

instance (p   ~ Problem typ
         ,typ ~ InitialGoal t (MkNarrowingGen base)
         ,id  ~ TermId t, id ~ SignatureId (Problem base trs), id ~ symbol a
         ,v   ~ Var
         ,trs ~ NarradarTRS t v
--         ,HasSignature (Problem (MkNarrowing base) trs)
         ,Traversable (Problem base), Traversable t
         ,Ord id, SATOrd (SAT a (Term t v)) id, Extend id, AFSymbol id, UsableSymbol id, GenSymbol id
         ,Foldable t, HasId t, Ord (t(Term t v)), Pretty id
         ,MkDPProblem (MkNarrowingGen base) trs
         ,MkDPProblem  base trs
         ,IUsableRules t v (MkNarrowingGen base, trs, trs)
         ,IUsableRules t v (base, trs, trs)
         ) => Omega (InitialGoal t (MkNarrowingGen base)) t
 where

  omega p = andM_ [andM_ [go l r trs | l:->r <- reachablePairs p]
                 ,andM_ [ usable f ^==>> andM_ [ l >~ r | l:->r <- rulesFor f trs]
                              | f <- Set.toList dd ]
                 ,andM_ [notM(usable f) | f <- Set.toList (getDefinedSymbols sig `Set.difference` dd)]
                  ]

   where
    (trs,dps) = (rules $ getR p, rules $ getP p)
    sig = getSignature (getR p)
    dd  = getDefinedSymbols (reachableRules p)
    genUsable = andM  [usable gen | gen <- toList(getDefinedSymbols (getR p))
                                  , gen == genSymbol]

    go l (Pure x) _ =
        everyM_ poss (\p ->
                           or_ [ not(inAF i f)
                                 | n <- [0..length p - 1], let (pre, i:_) = splitAt n p
                                 , let f = fromMaybe (error "omega: fromJust") (rootSymbol (l!pre))])
        ==>>  genUsable
     where
      poss = occurrences (Pure x) l

    go l t trs
      | id_t `Set.notMember` dd
      = andM_ [ [inAF i id_t] ^*==> go l t_i trs
                 | (i, t_i) <- zip [1..] tt ]
      | otherwise
      = andM_ [ usable id_t
             , andM_ [ go l r rest | l:->r <- rls ]
             , andM_ [ [inAF i id_t] ^*==> go l t_i rest
                          | (i, t_i) <- zip [1..] tt ]
             ]
       where
         Just id_t = rootSymbol t
         tt        = directSubterms t
         rls       = rulesFor id_t trs
         rest      = trs \\ rls  :: [Rule t Var]

rulesFor :: (HasId t, TermId t ~ id, Eq id) => id -> [Rule t v] -> [Rule t v]
rulesFor f trs = [ l:->r | l:-> r <- trs, rootSymbol l == Just f ]

-- --------
-- Testing
-- --------

verifyRPOAF :: forall typ trs t v a k.
          (Traversable (Problem typ)
          ,trs ~ NTRS (SymbolRes a)
          ,MkDPProblem typ trs
          ,Ord a, Pretty a
          ,AF.ApplyAF (Problem typ trs)
          ,HasSignature (Problem typ trs), SignatureId (Problem typ trs) ~ SymbolRes a
          ,NUsableRules (SymbolRes a) (typ, trs, trs)
          ) => Problem typ (NTRS a) -> [SymbolRes a] -> [Int] -> VerifyRPOAF (RuleN (SymbolRes a))

verifyRPOAF p0 symbols nondec_pairs = runIdentity $ do

  falseDecreasingPairs       <- runListT $ do
     s:->t <- li the_dps
     guard =<< lift (liftM P.not(AF.apply the_af s > AF.apply the_af t))
     return (s:->t)

  falseWeaklyDecreasingRules       <- runListT $ do
     s:->t <- li (toList the_usableRules)
     guard =<< lift (liftM P.not(AF.apply the_af s >~ AF.apply the_af t))
     return (s:->t)

  let missingUsableRules = toList (Set.difference expected_usableRules the_usableRules)
      excessUsableRules  = toList (Set.difference the_usableRules expected_usableRules)

  return VerifyRPOAF{..}

 where

  RPO.RPO{..} = RPO.symbolRPO

  p             = fmap (mapNarradarTRS (mapTermSymbols convertSymbol)) p0
  convertSymbol = fromJust . (`Map.lookup` Map.fromList [(the_symbolR s, s) | s <- symbols])

  the_af  = AF.fromList' [(s, filtering s) | s <- toList (getAllSymbols p)]
  all_dps = rules (getP p)
  the_dps = CE.assert (all (P.< length all_dps) nondec_pairs) $
            select ([0..length all_dps - 1] \\ nondec_pairs) all_dps
  the_usableRules      = Set.fromList [ l:->r | l:->r <- rules(getR p), let Just id = rootSymbol l, isUsable id]
  expected_usableRules = Set.fromList
                         [ rule
                          | let ur_af = Set.fromList(rules $ getR $ iUsableRules (AF.apply the_af p) (rhs <$> AF.apply the_af all_dps))
                          , rule <- rules(getR p)
                          , AF.apply the_af rule `Set.member` ur_af]

