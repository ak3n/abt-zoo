{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}

module Main where

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
  TRUE :: Lang '[]
  FALSE :: Lang '[]
  IF :: Lang '[Z, Z, Z]
  BOOL :: Lang '[]
  ARROW :: Lang '[Z, Z]
  NAT :: Lang '[]
  ZERO :: Lang '[]
  SUCC :: Lang '[Z]

instance Show1 Lang where
  show1 = \case
    LAM -> "lam"
    APP -> "ap"
    TRUE -> "true"
    FALSE -> "false"
    IF -> "if"
    BOOL -> "bool"
    ARROW -> "->"
    NAT -> "nat"
    ZERO -> "zero"
    SUCC -> "succ"

instance HEq1 Lang where
  heq1 LAM LAM = Just Refl
  heq1 APP APP = Just Refl
  heq1 TRUE TRUE = Just Refl
  heq1 FALSE FALSE = Just Refl
  heq1 IF IF = Just Refl
  heq1 BOOL BOOL = Just Refl
  heq1 ARROW ARROW = Just Refl
  heq1 NAT NAT = Just Refl
  heq1 ZERO ZERO = Just Refl
  heq1 SUCC SUCC = Just Refl  
  heq1 _ _ = Nothing

lam :: Tm0 Lang -> Tm Lang (S Z) -> Tm0 Lang
lam t e = LAM $$ t :& e :& RNil

app :: Tm0 Lang -> Tm0 Lang -> Tm0 Lang
app m n = APP $$ m :& n :& RNil

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
    _ -> raise "Failure"

eval :: Tm0 Lang -> Tm0 Lang
eval = runM . star step

judge :: JudgeT M String -> IO ()
judge = either fail putStrLn . runM . runExceptT . runJudgeT

main :: IO ()
main = do
  judge $ do
    ty <- inferTy [] false
    tyS <- toString ty
    return tyS

  judge $ do
    x <- named "x"
    ty <- inferTy [] (lam bool (x \\ var x))
    tyS <- toString ty
    return tyS

  judge $ do
    x <- named "x"
    checkTy [] (lam bool (x \\ var x)) (arrow bool bool)
    return "Success"

  judge $ do
    checkTy [] false bool
    return "Success"

  judge $ do
    x <- named "x"
    let tm = (app (lam bool (x \\ var x)) true)
    tmT <- inferTy [] tm
    checkTy [] tm bool
    return "Success"

  judge $ do
    tmT <- inferTy [] (succ zero)
    tmS <- toString tmT
    return tmS

  print . runM $ do
    x <- named "x"
    let tm = (app (lam bool (x \\ false)) true)
    tmS <- toString $ eval tm
    return tmS

  print . runM $ do
    x <- named "x"
    let tm = if_ true false true
    tmS <- toString $ eval tm
    return tmS