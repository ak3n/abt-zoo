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

import Util

data Lang ns where
  LAM :: Lang '[S Z]
  APP :: Lang '[Z, Z]
  TRUE :: Lang '[]
  FALSE :: Lang '[]
  IF :: Lang '[Z, Z, Z]
  BOOL :: Lang '[]
  ARROW :: Lang '[Z, Z]

instance Show1 Lang where
  show1 = \case
    LAM -> "lam"
    APP -> "ap"
    TRUE -> "true"
    FALSE -> "false"
    IF -> "if"
    BOOL -> "bool"
    ARROW -> "->"

instance HEq1 Lang where
  heq1 LAM LAM = Just Refl
  heq1 APP APP = Just Refl
  heq1 TRUE TRUE = Just Refl
  heq1 FALSE FALSE = Just Refl
  heq1 IF IF = Just Refl
  heq1 BOOL BOOL = Just Refl
  heq1 ARROW ARROW = Just Refl
  heq1 _ _ = Nothing

lam :: Tm Lang (S Z) -> Tm0 Lang
lam e = LAM $$ e :& RNil

app :: Tm0 Lang -> Tm0 Lang -> Tm0 Lang
app m n = APP $$ m :& n :& RNil

true :: Tm0 Lang
true = TRUE $$ RNil

false :: Tm0 Lang
false = FALSE $$ RNil

if_then_else :: Tm0 Lang -> Tm0 Lang -> Tm0 Lang -> Tm0 Lang
if_then_else c t1 t2 = IF $$ c :& t1 :& t2 :& RNil

bool :: Tm0 Lang
bool = BOOL $$ RNil

arrow :: Tm0 Lang -> Tm0 Lang -> Tm0 Lang
arrow a b = ARROW $$ a :& b :& RNil

step
  :: Tm0 Lang
  -> StepT M (Tm0 Lang)
step tm =
  out tm >>= \case
    APP :$ m :& n :& RNil ->
      out m >>= \case
        LAM :$ xe :& RNil -> xe // n
        _ -> app <$> step m <*> pure n <|> app <$> pure m <*> step n
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
  let ntm = eval tm
      nty = eval ty
  (,) <$> out ntm <*> out nty >>= \case
    -- (LAM :$ xe :& RNil, ARROW :$ a :& y :& RNil) -> do
    --   z <- fresh
    --   ez <- xe // var z
    --   bz <- y // var z
    --   checkTy ((z,a):g) ez bz
    (IF :$ c :& t1 :& t2 :& RNil, _) -> do
      cty <- inferTy g c
      t1ty <- inferTy g t1
      t2ty <- inferTy g t2
      case (cty === bool, t1ty === t2ty && t1ty === ty) of
        (True, True) -> return ()
        (False, _) -> raise "The condition must have type bool"
        (_, False) -> raise "Terms types mismatch"
    _ -> do
      ty' <- inferTy g tm
      if ty' === nty
        then return ()
        else raise "Type error"

inferTy
  :: Ctx
  -> Tm0 Lang
  -> JudgeT M (Tm0 Lang)
inferTy g tm = do
  out (eval tm) >>= \case
    V v | Just (eval -> ty) <- lookup v g -> return ty
        | otherwise -> raise "Ill-scoped variable"
    APP :$ m :& n :& RNil -> do
      mTy <- inferTy g m
      nTy <- inferTy g n
      return $ arrow mTy nTy
    TRUE :$ RNil -> return bool
    FALSE :$ RNil -> return bool
    _ -> raise "Failure"

eval :: Tm0 Lang -> Tm0 Lang
eval = runM . star step

main :: IO ()
main = do
  either fail print . runM . runExceptT . runJudgeT $ do
    ty <- inferTy [] false
    tyS <- toString ty
    return tyS

  print "Hello"
