{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

module Untyped where

{- Untyped lambda calculus

 e ::= x | λx:A.e | e e   terms

-}

import Control.Monad.Trans.Maybe
import Control.Applicative
import Data.Vinyl

import Abt.Class
import Abt.Types
import Abt.Concrete.LocallyNameless

import Util

data Lang ns where
  LAM :: Lang '[S Z]
  APP :: Lang '[Z, Z]

instance Show1 Lang where
  show1 = \case
    LAM -> "lam"
    APP -> "ap"

instance HEq1 Lang where
  heq1 LAM LAM = Just Refl
  heq1 APP APP = Just Refl
  heq1 _ _ = Nothing

lam :: Tm Lang (S Z) -> Tm0 Lang
lam e = LAM $$ e :& RNil

app :: Tm0 Lang -> Tm0 Lang -> Tm0 Lang
app m n = APP $$ m :& n :& RNil

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

eval :: Tm0 Lang -> Tm0 Lang
eval = runM . star step

-- | @λx.x@
--
identityTm :: M (Tm0 Lang)
identityTm = do
  x <- named "x"
  return $ lam (x \\ var x)

-- | @(λx.x)(λx.x)@
--
appTm :: M (Tm0 Lang)
appTm = do
  tm <- identityTm
  return $ app tm tm

-- | @(λx. x x)(λx. x x)
--
omegaTm :: M (Tm0 Lang)
omegaTm = do
  x <- named "x"
  let appxx = app (var x) (var x)
  let t = lam (x \\ appxx)
  return $ app t t
