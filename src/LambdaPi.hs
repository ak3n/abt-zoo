{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}

module LambdaPi where

{- λP (LF)

 A ::= a | Πx:A. B                        types
 e ::= x | λx:A.e | e e                   terms

PI = Πx:A. B

-}

import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Except
import Control.Applicative
import Data.Vinyl

import Abt.Class
import Abt.Types
import Abt.Concrete.LocallyNameless

import Prelude hiding (succ, pi)
import Util

data Lang ns where
  LAM :: Lang '[Z, S Z]
  APP :: Lang '[Z, Z]
  PI :: Lang '[Z, S Z]
  UNIVERSE :: Lang '[Z]
  -- bools
  TRUE :: Lang '[]
  FALSE :: Lang '[]
  IF :: Lang '[Z, Z, Z]
  BOOL :: Lang '[]
  -- nats
  NAT :: Lang '[]
  ZERO :: Lang '[]
  SUCC :: Lang '[Z]
  NATELIM :: Lang '[Z, Z, Z, Z]
  -- vectors
  VEC :: Lang '[Z, Z]
  -- VNIL :: Lang '[Z]
  -- VCONS :: Lang '[Z, Z, Z, Z]

instance Show1 Lang where
  show1 = \case
    LAM -> "lam"
    APP -> "ap"
    PI -> "pi"
    UNIVERSE -> "type"
    -- bools
    TRUE -> "true"
    FALSE -> "false"
    IF -> "if"
    BOOL -> "bool"
    -- nats
    NAT -> "nat"
    ZERO -> "zero"
    SUCC -> "succ"
    NATELIM -> "natelim"
    -- vectors
    VEC -> "vec"

instance HEq1 Lang where
  heq1 LAM LAM = Just Refl
  heq1 APP APP = Just Refl
  heq1 PI PI = Just Refl
  heq1 UNIVERSE UNIVERSE = Just Refl
  -- bools
  heq1 TRUE TRUE = Just Refl
  heq1 FALSE FALSE = Just Refl
  heq1 IF IF = Just Refl
  heq1 BOOL BOOL = Just Refl
  -- nats
  heq1 NAT NAT = Just Refl
  heq1 ZERO ZERO = Just Refl
  heq1 SUCC SUCC = Just Refl
  heq1 NATELIM NATELIM = Just Refl
  -- vectors
  heq1 VEC VEC = Just Refl
  heq1 _ _ = Nothing

lam :: Tm0 Lang -> Tm Lang (S Z) -> Tm0 Lang
lam t e = LAM $$ t :& e :& RNil

app :: Tm0 Lang -> Tm0 Lang -> Tm0 Lang
app m n = APP $$ m :& n :& RNil

pi :: Tm0 Lang -> Tm Lang (S Z) -> Tm0 Lang
pi t e = PI $$ t :& e :& RNil

universe :: Tm0 Lang -> Tm0 Lang
universe level = UNIVERSE $$ level :& RNil

true :: Tm0 Lang
true = TRUE $$ RNil

false :: Tm0 Lang
false = FALSE $$ RNil

if_ :: Tm0 Lang -> Tm0 Lang -> Tm0 Lang -> Tm0 Lang
if_ c t1 t2 = IF $$ c :& t1 :& t2 :& RNil

bool :: Tm0 Lang
bool = BOOL $$ RNil

nat :: Tm0 Lang
nat = NAT $$ RNil

zero :: Tm0 Lang
zero = ZERO $$ RNil

succ :: Tm0 Lang -> Tm0 Lang
succ t = SUCC $$ t :& RNil

natelim :: Tm0 Lang -> Tm0 Lang -> Tm0 Lang -> Tm0 Lang -> Tm0 Lang
natelim m mz ms n = NATELIM $$ m :& mz :& ms :& n :& RNil

vec :: Tm0 Lang -> Tm0 Lang -> Tm0 Lang
vec t n = VEC $$ t :& n :& RNil

maxNat
  :: Tm0 Lang
  -> Tm0 Lang
  -> JudgeT M (Tm0 Lang)
maxNat a b =
  (,) <$> out a <*> out b >>= \case
    (ZERO :$ RNil, ZERO :$ RNil) -> return zero
    (ZERO :$ RNil, SUCC :$ k :& RNil) -> return $ succ k
    (SUCC :$ k :& RNil, ZERO :$ RNil) -> return $ succ k
    (SUCC :$ k1 :& RNil, SUCC :$ k2 :& RNil) -> do
      s <- maxNat k1 k2
      return $ succ s

step
  :: Tm0 Lang
  -> StepT M (Tm0 Lang)
step tm =
  out tm >>= \case
    APP :$ m :& n :& RNil ->
      out m >>= \case
        LAM :$ t :& xe :& RNil -> xe // n
        _ -> app <$> step m <*> pure n <|> app <$> pure m <*> step n
    IF :$ c :& t1 :& t2 :& RNil ->
      out c >>= \case
        TRUE :$ RNil -> return t1
        FALSE :$ RNil -> return t2
    SUCC :$ k :& RNil -> do
      m <- step k
      return $ succ m
    NATELIM :$ m :& mz :& ms :& n :& RNil -> do
      let mzVal = eval mz
          msVal = eval ms
          rec kVal =
            out kVal >>= \case
              ZERO :$ RNil -> return mzVal
              SUCC :$ k :& RNil -> do
                recK <- rec k
                return $ app (app msVal k) recK
        in rec (eval n)
    _ -> stepsExhausted

star
  :: Monad m
  => (a -> StepT m a)
  -> (a -> m a)
star f a =
  runMaybeT (runStepT $ f a) >>=
    return a `maybe` star f

type Ctx = [(Var, Tm0 Lang)]

checkTy
  :: Ctx
  -> Tm0 Lang
  -> Tm0 Lang
  -> JudgeT M ()
checkTy g tm ty = do
  ty' <- inferTy g tm
  if ty' === ty
    then return ()
    else raise "Type error"

inferUniverse
  :: Ctx
  -> Tm0 Lang
  -> JudgeT M (Tm0 Lang)
inferUniverse g t = do
  u <- inferTy g t
  out (eval u) >>= \case
    UNIVERSE :$ k :& RNil -> return k
    _ -> raise "Type expected"

inferPi
  :: Ctx
  -> Tm0 Lang
  -> JudgeT M (Tm0 Lang, Tm Lang (S Z))
inferPi g e = do
  t <- inferTy g e
  out (eval t) >>= \case
    PI :$ m :& n :& RNil -> return (m, n)
    _ -> raise "Function expected"

inferTy
  :: Ctx
  -> Tm0 Lang
  -> JudgeT M (Tm0 Lang)
inferTy g tm = do
  out tm >>= \case
    V v | Just (eval -> ty) <- lookup v g -> return ty
        | otherwise -> raise "Ill-scoped variable"
    LAM :$ t :& m :& RNil -> do
        _ <- inferUniverse g t
        v :\ e <- out m
        z <- clone v
        em <- m // var z
        ty <- inferTy ((z,t):g) em
        return $ pi t (z \\ ty)
    APP :$ e1 :& e2 :& RNil -> do
      (s, t) <- inferPi g e1
      te <- inferTy g e2
      if te === s
        then t // e2
        else raise "Types mismatch"
    PI :$ m :& n :& RNil -> do
      u1 <- inferUniverse g m
      v :\ e <- out n
      z <- clone v
      en <- n // var z
      u2 <- inferUniverse ((z, m):g) en
      u <- maxNat u1 u2
      return $ universe u
    UNIVERSE :$ k :& RNil -> return $ universe (succ k)
    IF :$ c :& t1 :& t2 :& RNil -> do
      cty <- inferTy g c
      t1ty <- inferTy g t1
      t2ty <- inferTy g t2
      case (cty === bool, t1ty === t2ty) of
        (True, True) -> return t1ty
        (False, _) -> raise "The condition must have type bool"
        (_, False) -> raise "Terms types mismatch"
    TRUE :$ RNil -> return bool
    FALSE :$ RNil -> return bool
    BOOL :$ RNil -> return $ universe zero
    ZERO :$ RNil -> return nat
    SUCC :$ t :& RNil -> do
      ty <- inferTy g t
      if ty === nat
        then return nat
        else raise "The argument is not a number"
    NAT :$ RNil -> return $ universe zero
    NATELIM :$ m :& mz :& ms :& n :& RNil -> do
      let mVal = eval m
      let nVal = eval n
      mzTy <- inferTy g mz
      msTy <- inferTy g ms
      nTy <- inferTy g n
      z <- fresh
      z' <- fresh
      let msCorrecTy = pi nat (z \\ (pi (eval $ app mVal (var z)) (z' \\ (eval $ app mVal (var z')))))
      case (mzTy === (eval $ app mVal zero), msTy === msCorrecTy, nTy === nat) of
        (True, True, True) ->return $ eval (app mVal nVal)
        (False, _, _) -> raise "The type of the nat eliminator for the base case is incorrect"
        (_, False, _) -> raise "The type of the nat eliminator for the step case is incorrect"
        (_, _, False) -> raise "The last argument is not a natural number"
    VEC :$ t :& n :& RNil -> do
      tt <- inferTy g t
      tn <- inferTy g n
      (,) <$> out tt <*> out tn >>= \case
        (UNIVERSE :$ k :& RNil, NAT :$ RNil) ->
          out k >>= \case
            ZERO :$ RNil -> return $ universe zero
            _ -> raise "The type of Vec should be in the universe 0"
        (UNIVERSE :$ _ :& RNil, _) -> raise "The second arg of Vec should be Nat"

eval :: Tm0 Lang -> Tm0 Lang
eval = runM . star step

judge :: JudgeT M a -> IO a
judge = either fail return . runM . runExceptT . runJudgeT
