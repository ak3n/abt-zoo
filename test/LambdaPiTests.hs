module LambdaPiTests where

import Test.Tasty
import Test.Tasty.HUnit

import Abt.Class
import Abt.Types
import Abt.Concrete.LocallyNameless

import Util
import LambdaPi
import Prelude hiding (pi, succ)


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

  , testCase "polymorphic identity" $ do
      judge $ do
        a <- named "a"
        x <- named "x"
        let identity = lam (universe zero) (x \\ var x)
        ty <- inferTy [] identity
        checkTy [] identity (pi (universe zero) (x \\ universe zero))

  , testCase "vectors" $ do
      judge $ do
        let natVec = vec nat (succ zero)
        checkTy [] natVec (universe zero)

  , testCase "one plus two" $ do
      result <- judge $ do
        z <- fresh
        z' <- fresh
        n <- named "n"
        k <- named "k"
        rec <- named "rec"
        let natToNat = pi nat (z' \\ nat)
        let plus = natelim (lam nat (z \\ natToNat))
                           (lam nat (n \\ (var n)))
                           (lam nat (k \\ (lam natToNat (rec \\ (lam nat (n \\ (succ (app (var rec) (var n)))))))))
        let one = succ zero
        let two = succ (succ zero)
        let three = eval (app (plus one) two)
        checkTy [] (plus one) (natToNat)
        return $ three === succ (succ (succ zero))

      assertBool "" result
  ]
