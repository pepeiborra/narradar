{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances, TypeSynonymInstances #-}
{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternGuards #-}

module Narradar.Constraints.SAT.RPOAF where

import Control.Applicative
import qualified Control.Exception as CE
import Control.Monad
import Data.Foldable (Foldable, toList)
import Data.List ((\\), transpose, inits)
import Data.Maybe
import Data.Monoid
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Traversable (Traversable)
import Narradar.Framework.Ppr

import Narradar.Constraints.SAT.Common
import Narradar.Types hiding (symbol, constant)
import Narradar.Utils
import qualified Narradar.Types.ArgumentFiltering as AF

import qualified Prelude
import Prelude hiding (lex, not, and, or, quot, (>))


-- | RPO + AF

rpoAF allowCol trs = runRPOAF rpos allowCol (getSignature trs) $ \dict -> do
  let symb_rules = mapTermSymbols (\f -> fromJust $ Map.lookup f dict) <$$> rules trs
  assertAll [ l > r | l:->r <- symb_rules]
  return (return ())


-- | RPO + AF + Usable Rules
rpoAF_DP col ex p = rpoAF_DP' col ex p

rposAF_DP col p = rpoAF_DP' col rpos p
lposAF_DP col p = rpoAF_DP' col lpos p
lpoAF_DP col p = rpoAF_DP' col (lpo) p
mpoAF_DP col p = rpoAF_DP' col (mpo) p

{-
rpoAF_DP' :: (p  ~ DPProblem typ [Rule t v], HasSignature p
             ,p' ~ DPProblem typ [Rule t' v], HasSignature p'
             ,t  ~ f id, Ord id, Pretty id, MapId f, TermId t ~ id
             ,t' ~ f id', HasId t', Foldable t',  TermId t' ~ id'
             ,Ord id', SATOrd id', Extend id', UsableSymbol id', AFSymbol id', Decode id' (SymbolRes id)
             ,Ord (Term t' v)
             ,IsDPProblem typ, Traversable (DPProblem typ)
             ,Functor t, Enum v, Ord v
             ,IUsableRules t' v p'
             ) =>
             Bool
          -> (Signature id -> id -> SAT id')
          -> DPProblem typ [Rule (f id) v]
          -> (DPProblem typ [Rule (f id') v] -> [SAT Boolean])
          -> SAT (Decoder ([Int], [SymbolRes id]))
-}
-- | Returns the indexes of non decreasing pairs and the symbols used
rpoAF_DP' allowCol con p = runRPOAF con allowCol (getSignature p) $ \dict -> do
  let
      trs' = mapTermSymbols (\f -> fromJust $ Map.lookup f dict) <$$> rules(getR p)
      dps' = mapTermSymbols (\f -> fromJust $ Map.lookup f dict) <$$> rules(getP p)
      p'   = mkDPProblem (getProblemType p) trs' dps'
  decreasing_dps <- replicateM (length dps') boolean
  assertAll [omega  p'
            ,andM [ l >~ r | l:->r <- dps']
            ,andM [(l > r) <<==>> return dec | (l:->r, dec) <- zip dps' decreasing_dps]
            ,or decreasing_dps
            ]
  return $ do
    decreasing <- decode decreasing_dps
    return [ r | (r,False) <- zip [0..] decreasing]

-- | Returns the indexes of non decreasing pairs, the indexes of af-rhs-ground pairs, and the symbols used
rpoAF_NDP allowCol con p = runRPOAF con allowCol (getSignature p) $ \dict -> do
  let
      trs' = mapTermSymbols (\f -> fromJust $ Map.lookup f dict) <$$> rules(getR p)
      dps' = mapTermSymbols (\f -> fromJust $ Map.lookup f dict) <$$> rules(getP p)
      p'   = mkDPProblem (getProblemType p) trs' dps'
  decreasing_dps <- replicateM (length dps') boolean
  af_ground_rhs_dps <- replicateM (length dps') boolean

  assertAll [omega  p'
            ,andM [ l >~ r | l:->r <- dps']
            ,andM [(l > r) <<==>> return v | (l:->r, v) <- zip dps' decreasing_dps]
            ,andM [afGroundRHS r <<==>> return v | (r, v) <- zip dps' af_ground_rhs_dps]
            ,or decreasing_dps
            ,or af_ground_rhs_dps
            ]
  return $ do
    decreasing <- decode decreasing_dps
    af_ground  <- decode af_ground_rhs_dps
    return ([ r | (r,False) <- zip [0..] decreasing]
           ,[ r | (r,False) <- zip [0..] af_ground])

runRPOAF con allowCol sig f = do
  let ids = Set.toList $ getAllSymbols sig
  symbols <- mapM (con sig) ids
  if allowCol
    then assertAll [notM(listAF s) ==>> oneM [inAF i s | i <- [1..a]]
                    | (s,a) <- zip symbols (getArity sig <$> ids)]
    else mapM_ (listAF >=> assertOne) symbols

  let dict       = Map.fromList (zip ids symbols)
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
  deriving (Eq, Ord)

instance Pretty a => Pretty (SymbolRes a) where
    pPrint SymbolRes{the_symbolR} = pPrint the_symbolR

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

rpos sig x = do
  let ar = getArity sig x
  n_b <- number ( length
                $ takeWhile (Prelude.>0)
                $ iterate (`Prelude.div` 2)
                $ Set.size (getDefinedSymbols sig))
  perm_bb  <- replicateM ar (replicateM ar boolean)
  mset     <- boolean
  (list_b:pos_bb) <- replicateM (getArity sig x + 1) boolean
  usable_b <- boolean

  -- Permutation invariants
  -- -----------------------
  -- There is one or zero arguments considered at the k'th perm position,
  assertAll [ or perm_k ==>> oneM (return <$> perm_k)
             | perm_k <- transpose perm_bb]
  -- Filtered arguments may not be used in the permutation
  assertAll [ not p ==> notM (or perm_i) | (p, perm_i) <- zip pos_bb perm_bb]
  -- Non filtered arguments are considered at exactly one position in the permutation
  assertAll [ p ==> oneM (return <$> perm_i) | (p, perm_i) <- zip pos_bb perm_bb]
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
--               usable <- decode usable_b
                 isList <- decode list_b
                 pos    <- decode pos_bb
                 isUsable <- decode usable_b
                 status   <- decode mset
                 perm_bools <- decode perm_bb
                 let the_positions = [fromInteger i | (i,True) <- zip [1..] pos]
                     statusMsg   = mkStatus status perm_bools
                 return$
                  if Prelude.not isList
                   then CE.assert (length the_positions == 1)
                        (SymbolRes x n isUsable statusMsg (Left $ head the_positions))
                   else (SymbolRes x n isUsable statusMsg (Right the_positions))
             }

class AFSymbol a where
    listAF :: a -> SAT Boolean
    inAF, isAF :: Int -> a -> SAT Boolean
    isAF j sym = andM [inAF j sym, notM (listAF sym)]

instance AFSymbol (Symbol a) where
   listAF     = return . encodeAFlist
   inAF j sym = return (encodeAFpos sym !! (j-1))

class UsableSymbol a where usable :: a -> SAT Boolean
instance UsableSymbol (Symbol a) where usable = return . encodeUsable

instance SATOrd (Symbol a) where
  a > b  = encodePrec a `gt` encodePrec b
  a ~~ b = encodePrec a `eq` encodePrec b

instance Eq a => Extend (Symbol a) where
  exeq s t ss tt =
      orM [andM [return (encodeUseMset s), return (encodeUseMset t), muleq s t ss tt]
          ,andM [return (not$ encodeUseMset s), return (not$ encodeUseMset t),
                       lexpeq s t ss tt]
          ]
  exgt s t ss tt =
      orM [andM [and[encodeUseMset s, encodeUseMset t], mulgt s t ss tt]
          ,andM [notM$ or[encodeUseMset s, encodeUseMset t],
                       lexpgt s t ss tt]
          ]

-- --------
-- Variants
-- --------

-- LPO with status

newtype LPOSsymbol a = LPOS{unLPOS::Symbol a} deriving (Eq, Ord, Show, SATOrd, AFSymbol, UsableSymbol)
instance Decode (LPOSsymbol a) (SymbolRes a) where decode = decode . unLPOS

lpos sig = liftM LPOS . rpos sig

instance Eq a => Extend (LPOSsymbol a) where
  exeq s t = lexpeq (unLPOS s) (unLPOS t)
  exgt s t = exgt (unLPOS s) (unLPOS t)


newtype LPOsymbol a = LPO{unLPO::Symbol a} deriving (Eq, Ord, Show, SATOrd, AFSymbol, UsableSymbol)
instance Decode (LPOsymbol a) (SymbolRes a) where decode = liftM removePerm . decode . unLPO

removePerm symbolRes@SymbolRes{status=Lex _} = symbolRes{status = Lex Nothing}
removePerm symbolRes = symbolRes

lpo sig x = do
  s <- rpos sig x
  return (LPO s)

instance Eq a => Extend (LPOsymbol a) where
  exeq s t = lexeq (unLPO s) (unLPO t)
  exgt s t = exgt (unLPO s) (unLPO t)

-- MPO
newtype MPOsymbol a = MPO{unMPO::Symbol a} deriving (Eq, Ord, Show, SATOrd, AFSymbol, UsableSymbol)
instance Decode (MPOsymbol a) (SymbolRes a) where decode = decode . unMPO

mpo sig x = do
  s <- rpos sig x
  assertOne (encodeUseMset s)
  return (MPO s)

instance Eq a => Extend (MPOsymbol a) where
  exeq s t = lexpeq (unMPO s) (unMPO t)
  exgt s t = exgt (unMPO s) (unMPO t)

-- -----------
-- RPO with AF
-- -----------
instance (Eq v, Eq (Term f v), Foldable f, HasId f, TermId f ~ id
         ,SATOrd id, AFSymbol id, Extend id) =>
    SATOrd (Term f v) where
 s > t
   | Just id_t <- rootSymbol t, tt_t <- directSubterms t
   , Just id_s <- rootSymbol s, tt_s <- directSubterms s
   = orM [cond1 id_s id_t tt_s tt_t,  cond2 id_s tt_s]

   | Just id_s <- rootSymbol s, tt_s <- directSubterms s
   = cond2 id_s tt_s

   | otherwise = constant False

     where
       cond1 id_s id_t tt_s tt_t =
           andM[ allM (\(t_j, j) -> inAF j id_t ==>> s > t_j)
                      (zip tt_t [1..])
               , listAF id_t ==>> andM[ listAF id_s
                                      , orM[ id_s > id_t
                                           , andM[ id_s ~~ id_t
                                                 , exgt id_s id_t tt_s tt_t]
                                           ]
                                      ]
               ]

       cond2 id_s tt_s =
          anyM (\(s_i,i) ->
                 andM[ inAF i id_s
                     , orM[ s_i > t
                          , andM[ listAF id_s
                                , s_i ~~ t]
                          ]
                     ]
               )
               (zip tt_s [1..])

 Pure s ~~ Pure t = constant(s == t)
 s ~~ t
   | s == t  = constant True
   | isVar s = andM [notM$listAF id_t, allM (\(t_j,j) -> inAF j id_t ==>> s ~~ t_j) (zip tt [1..])]
   | isVar t = andM [notM$listAF id_s, allM (\(s_i,i) -> inAF i id_s ==>> s_i ~~ t) (zip ss [1..])]
   | otherwise
   = andM[ notM(listAF id_s) ==>> allM (\(s_i,i) -> inAF i id_s ==>> s_i ~~ t) (zip ss [1..])
         , andM[listAF id_s
               ,notM(listAF id_t)] ==>> allM (\(t_j,j) -> inAF j id_t ==>> t_j ~~ s) (zip tt [1..])
         , andM[listAF id_s
               ,listAF id_t] ==>> andM[ id_s ~~ id_t, exeq id_s id_t ss tt]
         ]
   where
        ss = directSubterms s
        tt = directSubterms t
        Just id_s = rootSymbol s
        Just id_t = rootSymbol t

-- -------------------------
-- Narrowing related stuff
-- -------------------------
afGroundRHS (_ :-> t) = andM [ orM [ notM(inAF i f)
                                    | prefix <- tail $ inits pos
                                    , let Just f = rootSymbol (t ! init prefix)
                                    , let      i = last prefix]
                               | pos <- [noteV v | v <- vars(annotateWithPos t)]]

-- -----------------------------------
-- Lexicographic extension with AF
-- -----------------------------------

lexgt id_f id_g ff gg = go (zip ff [1..]) (zip gg [1..]) where
  go []     _      = constant False
  go _      []     = constant True
  go ((f,i):ff) ((g,j):gg)
 -- If the symbols are the same, there is only one filtering to consider
    | id_f == id_g =
        orM [ andM [inAF i id_f, f > g]
            , andM [inAF i id_f ==>> f ~~ g, go ff gg]
            ]
-- otherwise, we must consider two different filterings!
    | otherwise
    =  ifM(inAF i id_f)
          (ifM (inAF j id_g)
                (orM[f >~ g, go ff gg])
                (go ((f,i):ff) gg))
          (go ff ((g,j):gg))

--    | otherwise = orM [ f `rpo` g
--                      , andM [eq f g, go ff gg]]

lexeq id_f id_g ff gg = go (zip ff [1..]) (zip gg [1..]) where
  go []         []         = constant True
  go ((f,i):ff) ((g,j):gg)
    | id_f == id_g = andM [inAF i id_f ==>> f ~~ g, go ff gg]
    | otherwise    = ifM (inAF i id_f)
                         (ifM (inAF j id_g)
                              (andM [f ~~ g, go ff gg])
                              (go ((f,i):ff) gg))
                         (go ff ((g,j):gg))
  go _          _  = constant False

lexpeq id_f id_g ss tt =
  andM [ eqArity
       , andM [ and [f_ik, g_jk] ==>> s_i ~~ t_j
              | (s_i, f_i) <- zip ss ff
              , (t_j, g_j) <- zip tt gg
              , (f_ik, g_jk) <- zip f_i g_j]]
 where (n,m)   = (length ss, length tt)
       (ff,gg) = (encodePerm id_f, encodePerm id_g)
       eqArity = andM [ or f_k <<==>> or g_k | (f_k, g_k) <- zip (transpose ff) (transpose gg)]

lexpgt id_f id_g ss tt = exgt_k (transpose $ encodePerm id_f) (transpose $ encodePerm id_g)
     where
       n = length ss
       m = length tt
       exgt_k [] _ = constant False
       exgt_k (f_k:_) [] = or f_k
       exgt_k (f_k:ff) (g_k:gg)
         = orM [andM [ return f_ik
                     , andM [ return g_jk ==>>
                               orM [ s_i > t_j
                                    , andM [ s_i ~~ t_j
                                           , exgt_k ff gg]]
                            | (g_jk, t_j) <- zip g_k tt]]
                | (f_ik, s_i) <- zip f_k ss]

-- ---------------------------
-- Multiset extension with AF
-- ---------------------------

--muleq, mulge, mulgt :: (SATOrd a, Eq a) => [a] -> [a] -> SAT Boolean

mulge id_f id_g ff gg = mulgen id_f id_g (i, j) $ mulgeF ff gg
 where
  (i, j) = (length ff, length gg)


mulgt id_f id_g ff gg = mulgen id_f id_g (i, j) $ \epsilons gammas ->
                     andM [mulgeF ff gg epsilons gammas
                          ,notM $ andM [inAF i id_f ==>> return ep
                                          | (i, ep) <- zip [1..] epsilons]]
 where
  (i, j) = (length ff, length gg)


muleq id_f id_g ff gg = mulgen id_f id_g (i, j) $ \epsilons gammas ->
                    andM [mulgeF ff gg epsilons gammas
                         ,andM [inAF i id_f ==>> return ep
                                    | (i, ep) <- zip [1..] epsilons]]
 where
  (i, j) = (length ff, length gg)

mulgeF ff gg epsilons gammasM =
    andM [ gamma ==> ifM' epsilon (f_i ~~ g_j) (f_i > g_j)
           | (epsilon, gammasR, f_i) <- CE.assert (length epsilons == length ff) $
                                        zip3 epsilons gammasM ff
           , (gamma, g_j) <- zip gammasR gg]

mulgen id_f id_g (i, j) k = do
    epsilons <- replicateM i boolean
    gammasM  <- replicateM i (replicateM j boolean)

    andM [andM [ inAF j id_g ==>> oneM (return <$> gammas_j)
                | (j, gammas_j) <- zip [1..] (transpose gammasM) ]
         ,andM [ notM(inAF i id_f) ==>> notM (or gammas_i)
                | (i, gammas_i) <- zip [1..] gammasM]
         ,andM [ notM(inAF j id_g) ==>> notM (or gammas_j)
                | (j, gammas_j) <- zip [1..] (transpose gammasM)]
         ,andM [ ep ==> oneM (return <$> gammasR)
                     | (ep, gammasR) <- zip epsilons gammasM]
         ,k epsilons gammasM]

-- ------------------------
-- Usable Rules with AF
-- ------------------------
class OmegaUsable thing where omega :: thing -> SAT Boolean

instance (p  ~ DPProblem IRewriting, HasSignature (p trs)
         ,id ~ TermId t, TermId t ~ SignatureId trs
         ,Traversable p
         ,IsTRS t v trs, GetVars v trs, HasSignature trs
         ,Ord v, Enum v
         ,Ord id, SATOrd id, Extend id, AFSymbol id, UsableSymbol id
         ,Foldable t, HasId t, Ord (Term t v)
         ,IUsableRules t v (p trs)
         ) =>
    OmegaUsable (DPProblem IRewriting trs)
 where
  omega p = omegaGen (constant True) p

instance (p  ~ DPProblem CNarrowing, HasSignature (p trs)
         ,id ~ TermId t, TermId t ~ SignatureId trs
         ,Traversable p
         ,IsTRS t v trs, GetVars v trs, HasSignature trs
         ,Ord v, Enum v
         ,Ord id, SATOrd id, Extend id, AFSymbol id, UsableSymbol id
         ,Foldable t, HasId t, Ord (Term t v)
         ,IUsableRules t v (p trs)
         ) =>
    OmegaUsable (DPProblem CNarrowing trs)
 where
  omega p = omegaGen (constant True) p

instance (p  ~ DPProblem Rewriting, HasSignature (p trs)
         ,id ~ TermId t, TermId t ~ SignatureId trs
         ,Traversable p
         ,IsTRS t v trs, GetVars v trs, HasSignature trs
         ,Ord v, Enum v
         ,Ord id, SATOrd id, Extend id, AFSymbol id, UsableSymbol id
         ,Foldable t, HasId t, Ord (Term t v)
         ,IUsableRules t v (p trs)
         ) =>
    OmegaUsable (DPProblem Rewriting trs)
 where
  omega p = omegaGen (andM $ map usable $ toList $ getDefinedSymbols p) p

instance (p  ~ DPProblem Narrowing, HasSignature (p trs)
         ,id ~ TermId t, TermId t ~ SignatureId trs
         ,Traversable p
         ,IsTRS t v trs, GetVars v trs, HasSignature trs
         ,Ord v, Enum v
         ,Ord id, SATOrd id, Extend id, AFSymbol id, UsableSymbol id
         ,Foldable t, HasId t, Ord (Term t v)
         ,IUsableRules t v (p trs)
         ) =>
    OmegaUsable (DPProblem Narrowing trs)
 where
  omega p = omegaGen (andM $ map usable $ toList $ getDefinedSymbols p) p

omegaGen ::  forall p typ trs id t v.
         (p  ~ DPProblem typ, HasSignature (p trs)
         ,id ~ TermId t, TermId t ~ SignatureId trs
         ,IsDPProblem typ, Traversable (DPProblem typ)
         ,IsTRS t v trs, GetVars v trs, HasSignature trs
         ,Ord v, Enum v
         ,Ord id, SATOrd id, Extend id, AFSymbol id, UsableSymbol id
         ,Foldable t, HasId t, Ord (Term t v)
         ,IUsableRules t v (p trs)
         ) => SAT Boolean -> p trs -> SAT Boolean

omegaGen varcase p =
      andM [andM [go r trs | _:->r <- dps]
           ,andM [ usable f ==>> andM [ l >~ r | l:->r <- rulesFor f trs]
                  | f <- Set.toList dd ]
           ]

   where
    (trs,dps) = (rules $ getR p, rules $ getP p)
    sig = getSignature (getR p)
    dd  = getDefinedSymbols (iUsableRules p (rhs <$> dps))

    go (Pure x) _ = varcase
    go t trs
      | id_t `Set.notMember` getDefinedSymbols sig
      = andM [ inAF i id_t ==>> go t_i trs
               | (i, t_i) <- zip [1..] tt ]
      | otherwise
      = andM [ usable id_t
             , andM [ go r trs' | let trs' = (trs \\ rls :: [Rule t v]), _:->r <- rls ]
             , andM [ inAF i id_t ==>> go t_i trs
                          | (i, t_i) <- zip [1..] tt ]
             ]
       where
         Just id_t = rootSymbol t
         tt        = directSubterms t
         rls       = rulesFor id_t trs

rulesFor :: (HasId t, TermId t ~ id, Eq id) => id -> [Rule t v] -> [Rule t v]
rulesFor f trs = [ l:->r | l:-> r <- trs, rootSymbol l == Just f ]
