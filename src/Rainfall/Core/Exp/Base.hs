
module Rainfall.Core.Exp.Base where
import Data.Set         (Set)
import Data.String

type Name       = String

data Bind
        = BindName Name
        | BindNone
        deriving (Show, Eq, Ord)

instance IsString Bind where
 fromString s = BindName s

type Auth       = Set Name
