module Idrall.API.V2

import Idrall.Value
import Idrall.Expr
import Idrall.Error
import Idrall.Derive
import Idrall.IOEither
import Idrall.APIv1

import System.Path -- TODO make public export in System.Directory.Tree?
import System.Directory.Tree

liftMaybe : Maybe a -> IOEither Error a
liftMaybe Nothing = MkIOEither $ pure $ Left $ FromDhallError "failed to convert from dhall"
liftMaybe (Just x) = pure x

export
dhallValFromString : String -> IOEither Error Value

export
dhallExprFromString : String -> IOEither Error (Expr Void)

export
deriveFromDhallString : FromDhall a => String -> IOEither Error a
deriveFromDhallString x = do
  e <- roundTripCheckEvalQuote $ x
  liftMaybe $ fromDhall e

export
deriveFromDhallFile : FromDhall a => Path -> IOEither Error a
deriveFromDhallFile = deriveFromDhallString . show

showIOEitherError : Show a => IOEither Error a -> IO String
showIOEitherError (MkIOEither x) = do
  x' <- x
  pure $ show x'

doStuff : IO ()
doStuff =
  putStrLn !(showIOEitherError $ deriveFromDhallString {a=Bool} "3")
