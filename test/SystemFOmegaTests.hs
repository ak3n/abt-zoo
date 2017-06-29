module SystemFOmegaTests where

import Test.Tasty
import Test.Tasty.HUnit

import Abt.Class
import Abt.Types
import Abt.Concrete.LocallyNameless

import Util
import SystemFOmega


systemFOmegaTests = testGroup "System F Omega"
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

  , testCase "type application works fine" $ do
      result <- judge $ do
        x <- named "x"
        let tm1 = (tlam kind (x \\ bool))
        let tm2 = (tapp tm1 nat)
        checkTy [] tm2 kind
        return $ (eval tm2) === bool

      assertBool "" result

  , testCase "type application with forall works fine" $ do
      result <- judge $ do
        x <- named "x"
        a <- named "a"
        let tm = (plam (a \\ (lam (var a) (x \\ (var x)))))
        checkTy [] tm (forall (a \\ arrow (var a) (var a)))
        let res = (eval $ ttapp tm nat)
        ty <- inferTy [] res
        return $ ty === (arrow nat nat) && res === (lam nat (x \\ (var x)))

      assertBool "" result

  , testCase "pairs typecheck fine" $ do
      judge $ do
        x <- named "x"
        y <- named "y"
        a <- named "A"
        b <- named "B"
        c <- named "C"
        k <- named "k"
        p <- named "p"

        -- λA::*.λB::*.∀C::*.(A -> B -> C) -> C;
        let pairTy = tlam kind (a \\ tlam kind (b \\ forall (c \\ arrow (arrow (var a) (arrow (var b) (var c))) (var c))))
        -- check that the type is * -> * -> *
        checkTy [] pairTy (karrow kind (karrow kind kind))

        -- ΛA::*.ΛB::*.λx:A.λy:B.ΛC::*.λk:(A -> B -> C).k x y;
        let aTobToC = (arrow (var a) (arrow (var b) (var c))) -- A -> B -> C as (A -> (B -> C))
        let kxy = (app (app (var k) (var x)) (var y)) -- k x y as (k x) y
        let pair = plam (a \\ (plam (b \\ lam (var a) (x \\ lam (var b) (y \\ plam (c \\ lam aTobToC (k \\ kxy)))))))
        -- check that the type is ∀A.∀B.A → B → (∀C.(A→B→C) → C)
        checkTy [] pair (forall (a \\ (forall (b \\ (arrow (var a) (arrow (var b) (forall (c \\ arrow aTobToC (var c)))))))))

        -- ΛA::*.ΛB::*.λp:Pair A B.p [A] (λx:A.λy:B.x);
        let pairAB = tapp (tapp pairTy (var a)) (var b)
        let fstTm = lam (var a) (x \\ lam (var b) (y \\ (var x)))
        let fst = plam (a \\ (plam (b \\ (lam pairAB (p \\ (app (ttapp (var p) (var a)) fstTm))))))
        -- check that the type is ∀A.∀B.Pair A B → A
        checkTy [] fst (forall (a \\ (forall (b \\ (arrow pairAB (var a))))))

        -- ΛA::*.ΛB::*.λp:Pair A B.p [B] (λx:A.λy:B.b);
        let sndTm = lam (var a) (x \\ lam (var b) (y \\ (var y)))
        let snd = plam (a \\ (plam (b \\ (lam pairAB (p \\ (app (ttapp (var p) (var b)) sndTm))))))
        -- check that the type is ∀A.∀B.Pair A B → B
        checkTy [] snd (forall (a \\ (forall (b \\ (arrow pairAB (var b))))))
  ]