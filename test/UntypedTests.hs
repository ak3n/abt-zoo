module UntypedTests where

import Test.Tasty
import Test.Tasty.HUnit

import Abt.Class
import Abt.Types
import Abt.Concrete.LocallyNameless

import Util
import Untyped


untypedTests = testGroup "Untyped"
  [ testCase "Identity is lam[x.x]" $ do
      let result = runM $ do
            im <- identityTm
            imStr <- toString im
            return imStr

      assertBool "" (result == "lam[x.x]")

  , testCase "Eval (λx.x)(λx.x) -> identity" $ do
      let result = runM $ do
            im <- identityTm
            mm <- appTm
            result <- toString $ eval mm
            im <- toString im
            return $ im == result

      assertBool "" result
  ]