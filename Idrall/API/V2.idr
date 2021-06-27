module Idrall.API.V2

import Idrall.Value
import public Idrall.Expr
import public Idrall.Error
import public Idrall.Derive
import public Idrall.IOEither
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
deriveFromDhallString : FromDhall ty => String -> IOEither Error ty
deriveFromDhallString x = do
  e <- roundTripCheckEvalQuote $ x
  liftMaybe $ fromDhall e

export
deriveFromDhallFile : FromDhall a => Path -> IOEither Error a
deriveFromDhallFile = deriveFromDhallString . show
