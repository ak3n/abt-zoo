module LambdaPiTests where

import Test.Tasty
import Test.Tasty.HUnit

import Abt.Class
import Abt.Types
import Abt.Concrete.LocallyNameless

import Util
import LambdaPi
import Prelude hiding (pi)


lambdaPiTests = testGroup "Lambda Pi"
  [ testCase "false has the bool type" $ do
      judge $ checkTy [] false bool

  , testCase "bool identity has the type (bool -> bool)" $ do
      judge $ do
        x <- named "x"
        checkTy [] (lam bool (x \\ var x)) (pi bool (x \\ bool))

  , testCase "application is well typed" $ do
      judge $ do
        x <- named "x"
        let tm = (app (lam bool (x \\ var x)) true)
        checkTy [] tm bool

  , testCase "eval works fine" $ do
      let result = runM $ do
            x <- named "x"
            let tm = app (lam bool (x \\ false)) true
            return $ (eval tm) === false

      assertBool "" result

  , testCase "if_then_else works fine" $ do
      let result = runM $ do
            x <- named "x"
            let tm = if_ true false true
            return $ (eval tm) === false

      assertBool "" result
  ]
