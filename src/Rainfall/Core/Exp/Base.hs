
module Rainfall.Core.Exp.Base where

type Name       = String
type Auth       = [Name]

data Bind
        = BindName Name
        | BindNone
        deriving Show