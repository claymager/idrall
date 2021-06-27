module Main

import Idrall.TestHelper

import Idrall.Expr
import Idrall.Error
import Idrall.API.V2
import Idrall.IOEither
import Idrall.Derive

import System.Path
-- import System.Directory
-- import Data.List
-- import Data.Strings
import Language.Reflection

%language ElabReflection

record Package where
  constructor MkPackage
  package : String
  sourceDir : Maybe String
  depends : Maybe (List String)
  modules : List String

Show Package where
  show (MkPackage package sourceDir depends modules) =
    "MkPackage \{show package} \{show sourceDir} \{show depends} \{show modules}"

%runElab (deriveFromDhall Record `{{ Package }})

main : IO ()
main = do
  package <- liftIOEither $ deriveFromDhallString {ty=Package} "./package.dhall"
  putStrLn $ show package
