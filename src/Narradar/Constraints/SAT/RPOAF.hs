{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances, TypeSynonymInstances #-}
{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}

module Narradar.Constraints.SAT.RPOAF where

import Control.Applicative
import qualified Control.Exception as CE
import Control.Monad
import Data.Foldable (Foldable, toList)
import Data.List ((\\), transpose)
import Data.Maybe
import Data.Monoid
import qualified Data.Map as Map
import qualified Data.Set as Set
import Narradar.Utils.Ppr

import Narradar.Constraints.SAT.Common
import Narradar.Constraints.SAT.Examples hiding (gt)
import Narradar.Types hiding (symbol, constant)
import Narradar.Utils
import qualified Narradar.Types.ArgumentFiltering as AF

import qualified Prelude
import Prelude hiding (lex, not, and, or, quot, (>))

-- | RPO + AF
rpoAF allowCol trs = runRPOAF symbol allowCol trs $ \dict -> do
  let symb_rules = mapTermSymbols (\f -> fromJust $ Map.lookup f dict) <$$> rules trs
  assertAll [ l > r | l:->r <- symb_rules]

-- | RPO + AF + Usable Rules
rpoAF_DP allowCol p@Problem{..} = runRPOAF symbol allowCol (dps `mappend` trs) $ \dict -> do
  let trs' = mapTermSymbols (\f -> fromJust $ Map.lookup f dict) <$$> rules trs
      dps' = mapTermSymbols (\f -> fromJust $ Map.lookup f dict) <$$> rules dps
      p'   = Problem{typ = AF.mapSymbols (\f -> fromJust $ Map.lookup f dict) <$> typ
                    ,trs = trs'
                    ,dps = dps'
                    }
  decreasing_dps <- replicateM (length $ rules dps) boolean
  assertAll [omega  p'
            ,andM [ l >~ r | l:->r <- rules dps']
            ,andM [(l > r) <<==>> return dec | (l:->r, dec) <- zip (rules dps') decreasing_dps]
            ,or decreasing_dps
            ]
  return decreasing_dps

runRPOAF symbol allowCol trs f = isSAT $ do
  let sig   = getSignature trs
  symbols <- mapM (symbol sig) (Set.toList $ getAllSymbols sig)
  if allowCol
    then assertAll [notM(listAF s) ==>> xor(encodeAFpos s) | s <- symbols]
    else mapM_ assertOne $ map encodeAFlist symbols

  let dict       = Map.fromList [(the_symbol s, s) | s <- symbols]
  res <- f dict
  return $ do res' <- decode res
              syms <- mapM (secondM decode) (Map.toList dict)
              return (res',syms)

-- -------------------------------------------------
-- Encoding of RPO symbols with AF and usable rules
-- -------------------------------------------------

data Symbol a = Symbol { the_symbol   :: a
                       , encodePrec   :: Number
                       , encodeUsable :: Boolean
                       , encodeAFlist :: Boolean
                       , encodeAFpos  :: [Boolean]
                       , encodePerm   :: [[Boolean]]
                       , encodeUseMset:: Boolean
                       , decodeSymbol :: Decoder (Integer, IsUsable, Status, Either Integer [Integer])}

instance Show a => Show (Symbol a) where
    show Symbol{the_symbol} = show the_symbol

instance Ppr a => Ppr (Symbol a) where
    ppr Symbol{the_symbol} = ppr the_symbol

instance Eq   a => Eq   (Symbol a) where
    a@Symbol{} == b@Symbol{} = the_symbol a == the_symbol b

instance Ord a => Ord (Symbol a) where
   compare a b = the_symbol a `compare` the_symbol b

instance Decode (Symbol a) (Integer, IsUsable, Status, Either Integer [Integer]) where decode = decodeSymbol

symbol sig x = do
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
  assertAll [ or perm_k ==>> oneM perm_k
             | perm_k <- transpose perm_bb]
  -- Filtered arguments may not be used in the permutation
  assertAll [ not p ==> notM (or perm_i) | (p, perm_i) <- zip pos_bb perm_bb]
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
                 n      <- decode n_b
--               usable <- decode usable_b
                 isList <- decode list_b
                 pos    <- decode pos_bb
                 isUsable <- decode usable_b
                 status   <- decode mset
                 perm_bools <- decode perm_bb
                 let the_positions = [i | (i,True) <- zip [1..] pos]
                     isUsableMsg = if isUsable then Usable else NotUsable
                     perm        = [ let poss =  [i | (i,True) <- zip [1..] perm_i]
                                            in CE.assert (length poss <= 1) (head (poss++[-1]))
                                                | perm_i <- perm_bools ]
                     statusMsg   = if status then Mul else Lex perm
                 return$
                  if Prelude.not isList
                   then CE.assert (length the_positions == 1)
                        (n, isUsableMsg, statusMsg, Left $ head the_positions)
                   else (n, isUsableMsg, statusMsg, Right the_positions)
             }

data IsUsable = Usable | NotUsable deriving (Eq, Show)
data Status   = Mul    | Lex [Int] deriving (Eq, Show)

listAF     = return . encodeAFlist
--inAF j sym | pprTrace (text "inAF" <+> ppr j <+> ppr sym) False = undefined
inAF j sym = return (encodeAFpos sym !! (j-1))
isAF j sym = andM [inAF j sym, notM (listAF sym)]

usable = return . encodeUsable

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


-- -----------
-- RPO with AF
-- -----------
instance (Eq v, Eq (Term f v), Foldable f, HasId f (Symbol a), Eq a, Ppr a) =>
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

    andM [andM [ inAF j id_g ==>> oneM gammas_j
                | (j, gammas_j) <- zip [1..] (transpose gammasM) ]
         ,andM [ notM(inAF i id_f) ==>> notM (or gammas_i)
                | (i, gammas_i) <- zip [1..] gammasM]
         ,andM [ notM(inAF j id_g) ==>> notM (or gammas_j)
                | (j, gammas_j) <- zip [1..] (transpose gammasM)]
         ,andM [ ep ==> oneM gammasR
                     | (ep, gammasR) <- zip epsilons gammasM]
         ,k epsilons gammasM]

-- ------------------------
-- Usable Rules with AF
-- ------------------------

omega p@Problem{dps, trs} =
      andM [ andM [go r (rules trs) | _:->r <- rules dps]
           , andM [ usable f ==>> andM [ l > r
                                      | l:->r <- rulesFor f (rules trs)]
                  | f <- Set.toList dd]
           ]
   where
    dd = getDefinedSymbols $
         iUsableRules p Nothing (rhs <$> rules dps)
    go (Pure x) _ = constant True
    go t trs
      | id_t `Set.notMember` getDefinedSymbols sig
      = andM [ inAF i id_t ==>> go t_i trs
               | (i, t_i) <- zip [1..] tt ]
      | otherwise
      = andM [ usable id_t
             , andM [ go r (trs \\ rls) | _:->r <- rls]
             , andM [ inAF i id_t ==>> go t_i trs
                          | (i, t_i) <- zip [1..] tt ]
             ]
       where
         Just id_t = rootSymbol t
         tt        = directSubterms t
         sig       = getSignature trs
         rls       = rulesFor id_t trs


rulesFor f trs = [ l:->r | l:-> r <- trs, rootSymbol l == Just f ]
