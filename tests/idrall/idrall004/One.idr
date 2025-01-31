module Main

import Idrall.TestHelper

import Idrall.Error
import Idrall.IOEither
import Idrall.APIv1

import System.Directory
import Data.List
import Data.Strings

dirTreeOne : DirTree String
dirTreeOne = MkDirTree "../../../dhall-lang/tests/type-inference/success/simple" [] ["toMapEmptyNormalizeAnnotation"]

testGood : IO (Result)
testGood = runTestsCheck dirTreeOne

main : IO ()
main = do res <- testGood
          printLn res
