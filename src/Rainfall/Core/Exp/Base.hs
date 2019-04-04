
module Rainfall.Core.Exp.Base where
import Data.Set         (Set)

type Name       = String

data Bind
        = BindName Name
        | BindNone
        deriving (Show, Eq, Ord)


type Auth       = Set Name
