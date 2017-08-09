{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}

module SystemF where

{- λ2 (System F -- polymorphic or second order, Typed Lambda Calculus)

 k ::= ∗                                          kinds
 A ::= a | p | A → B  | ∀a:k. A                   types
 e ::= x | λx:A.e | e e | Λa:k. e | e [A]         terms

TLAM = Λa:k. e
FORALL = ∀a:k. A
TAPP = e [A]

 -}

import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Except
import Control.Applicative
import Data.Vinyl

import Abt.Class
import Abt.Types
import Abt.Concrete.LocallyNameless

import Prelude hiding (succ)
import Util

data Lang ns where
  LAM :: Lang '[Z, S Z]
  APP :: Lang '[Z, Z]
  TLAM :: Lang '[S Z]
  TAPP :: Lang '[Z, Z]
  FORALL :: Lang '[S Z]
  TRUE :: Lang '[]
  FALSE :: Lang '[]
  IF :: Lang '[Z, Z, Z]
  BOOL :: Lang '[]
  ARROW :: Lang '[Z, Z]
  NAT :: Lang '[]
  ZERO :: Lang '[]
  SUCC :: Lang '[Z]
  KIND :: Lang '[]

instance Show1 Lang where
  show1 = \case
    LAM -> "lam"
    APP -> "ap"
    TLAM -> "tlam"
    TAPP -> "tapp"
    FORALL -> "forall"
    TRUE -> "true"
    FALSE -> "false"
    IF -> "if"
    BOOL -> "bool"
    ARROW -> "->"
    NAT -> "nat"
    ZERO -> "zero"
    SUCC -> "succ"
    KIND -> "*"

instance HEq1 Lang where
  heq1 LAM LAM = Just Refl
  heq1 APP APP = Just Refl
  heq1 TLAM TLAM = Just Refl
  heq1 TAPP TAPP = Just Refl  
  heq1 FORALL FORALL = Just Refl
  heq1 TRUE TRUE = Just Refl
  heq1 FALSE FALSE = Just Refl
  heq1 IF IF = Just Refl
  heq1 BOOL BOOL = Just Refl
  heq1 ARROW ARROW = Just Refl
  heq1 NAT NAT = Just Refl
  heq1 ZERO ZERO = Just Refl
  heq1 SUCC SUCC = Just Refl
  heq1 KIND KIND = Just Refl
  heq1 _ _ = Nothing

lam :: Tm0 Lang -> Tm Lang (S Z) -> Tm0 Lang
lam t e = LAM $$ t :& e :& RNil

app :: Tm0 Lang -> Tm0 Lang -> Tm0 Lang
app m n = APP $$ m :& n :& RNil

tlam :: Tm Lang (S Z) -> Tm0 Lang
tlam e = TLAM $$ e :& RNil

tapp :: Tm0 Lang -> Tm0 Lang -> Tm0 Lang
tapp m n = TAPP $$ m :& n :& RNil

forall :: Tm Lang (S Z) -> Tm0 Lang
forall e = FORALL $$ e :& RNil

true :: Tm0 Lang
true = TRUE $$ RNil

false :: Tm0 Lang
false = FALSE $$ RNil

if_ :: Tm0 Lang -> Tm0 Lang -> Tm0 Lang -> Tm0 Lang
if_ c t1 t2 = IF $$ c :& t1 :& t2 :& RNil

bool :: Tm0 Lang
bool = BOOL $$ RNil

arrow :: Tm0 Lang -> Tm0 Lang -> Tm0 Lang
arrow a b = ARROW $$ a :& b :& RNil

nat :: Tm0 Lang
nat = NAT $$ RNil

zero :: Tm0 Lang
zero = ZERO $$ RNil

succ :: Tm0 Lang -> Tm0 Lang
succ t = SUCC $$ t :& RNil

kind :: Tm0 Lang
kind = KIND $$ RNil

step
  :: Tm0 Lang
  -> StepT M (Tm0 Lang)
step tm =
  out tm >>= \case
    APP :$ m :& n :& RNil ->
      out m >>= \case
        LAM :$ t :& xe :& RNil -> xe // n
        _ -> app <$> step m <*> pure n <|> app <$> pure m <*> step n
    TAPP :$ m :& n :& RNil ->
      out m >>= \case
        TLAM :$ xe :& RNil -> xe // n
        _ -> tapp <$> step m <*> pure n <|> tapp <$> pure m <*> step n
    IF :$ c :& t1 :& t2 :& RNil ->
      out c >>= \case
        TRUE :$ RNil -> return t1
        FALSE :$ RNil -> return t2
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

inferTy
  :: Ctx
  -> Tm0 Lang
  -> JudgeT M (Tm0 Lang)
inferTy g tm = do
  out tm >>= \case
    V v | Just (eval -> ty) <- lookup v g -> return ty
        | otherwise -> raise "Ill-scoped variable"
    LAM :$ t :& m :& RNil -> do
        z <- fresh
        em <- m // var z
        ty <- inferTy ((z,t):g) em
        return $ arrow t ty
    APP :$ t1 :& t2 :& RNil -> do
      t1Ty <- inferTy g t1
      t2Ty <- inferTy g t2
      out t1Ty >>= \case
        ARROW :$ t1Ty1 :& t1Ty2 :& RNil ->
          if t1Ty1 === t2Ty
            then return t1Ty2
            else raise "Parameter type mismatch"
        _ -> raise "Arrow type expected"
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
    ZERO :$ RNil -> return nat
    SUCC :$ t :& RNil -> do
      ty <- inferTy g t
      if ty === nat
        then return nat
        else raise "The argument is not a number"
    NAT :$ RNil -> return kind
    BOOL :$ RNil -> return kind
    ARROW :$ _ :& _ :& RNil -> return kind
    FORALL :$ m :& RNil -> do
      z <- fresh
      em <- m // var z
      ty <- inferTy ((z,kind):g) em
      return kind
    TLAM :$ m :& RNil -> do
      v :\ e <- out m
      z <- clone v
      em <- m // var z
      ty <- inferTy ((z,kind):g) em
      return $ forall (z \\ ty)
    TAPP :$ t1 :& t2 :& RNil -> do
      t1Ty <- inferTy g t1
      t2Ty <- inferTy g t2
      out t1Ty >>= \case
        FORALL :$ tTy :& RNil ->
          if t2Ty === kind
            then eval <$> tTy // t2
            else raise "The argument should be a type"
        _ -> raise "Forall type expected"
    _ -> raise "Failure"

eval :: Tm0 Lang -> Tm0 Lang
eval = runM . star step

judge :: JudgeT M a -> IO a
judge = either fail return . runM . runExceptT . runJudgeT
