module Main where

import Test.Tasty
import Test.Tasty.HUnit

import UntypedTests
import STLCTests
import STLCHKTTests
import SystemFTests

main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [untypedTests, stlcTests, stlchktTests, systemFTests]
