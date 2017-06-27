module SystemFTests where

import Test.Tasty
import Test.Tasty.HUnit

import Abt.Class
import Abt.Types
import Abt.Concrete.LocallyNameless

import Util
import SystemF


systemFTests = testGroup "System F"
  [ testCase "false has the bool type" $ do
      judge $ checkTy [] false bool

  , testCase "bool identity has the type (bool -> bool)" $ do
      judge $ do
        x <- named "x"
        checkTy [] (lam bool (x \\ var x)) (arrow bool bool)

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

  , testCase "arrow type with variable" $ do
      judge $ do
        x <- named "x"
        a <- named "a"
        let tm = (lam (var a) (x \\ (var x)))
        checkTy [] tm (arrow (var a) (var a))

  , testCase "type application with forall works fine" $ do
      result <- judge $ do
        x <- named "x"
        a <- named "a"
        let tm = (tlam (a \\ (lam (var a) (x \\ (var x)))))
        checkTy [] tm (forall (a \\ arrow (var a) (var a)))
        let res = (eval $ tapp tm nat)
        ty <- inferTy [] res
        return $ ty === (arrow nat nat) && res === (lam nat (x \\ (var x)))

      assertBool "" result
  ]