{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Util where

import Control.Applicative
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Except

import Abt.Class
import Abt.Concrete.LocallyNameless

{-
  Some general stuff from the tutorial:

  https://github.com/jonsterling/hs-abt/blob/master/src/Abt/Tutorial.hs
-}

newtype M α
  = M
  { _M :: State Int α
  } deriving (Functor, Applicative, Monad)

runM :: M a -> a
runM (M m) = evalState m 0

instance MonadVar Var M where
  fresh = M $ do
    n <- get
    let n' = n + 1
    put n'
    return $ Var Nothing n'

  named a = do
    v <- fresh
    return $ v { _varName = Just a }

  clone v =
    case _varName v of
      Just s -> named s
      _ -> fresh

-- | A monad transformer for small step operational semantics.
--
newtype StepT m a
  = StepT
  { runStepT :: MaybeT m a
  } deriving (Monad, Functor, Applicative, Alternative)

-- | To indicate that a term is in normal form.
--
stepsExhausted
  :: Applicative m
  => StepT m α
stepsExhausted = StepT . MaybeT $ pure Nothing

instance MonadVar Var m => MonadVar Var (StepT m) where
  fresh = StepT . MaybeT $ Just <$> fresh
  named str = StepT . MaybeT $ Just <$> named str
  clone v = StepT . MaybeT $ Just <$> clone v

-- | A monad transformer for type checking.
--
newtype JudgeT m α
  = JudgeT
  { runJudgeT :: ExceptT String m α
  } deriving (Monad, Functor, Applicative, Alternative)

instance MonadVar Var m => MonadVar Var (JudgeT m) where
  fresh = JudgeT . ExceptT $ Right <$> fresh
  named str = JudgeT . ExceptT $ Right <$> named str
  clone v = JudgeT . ExceptT $ Right <$> clone v

raise :: Monad m => String -> JudgeT m a
raise = JudgeT . ExceptT . return . Left