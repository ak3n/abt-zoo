module Main where

import Test.Tasty
import Test.Tasty.HUnit

import UntypedTests

main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [untypedTests]
