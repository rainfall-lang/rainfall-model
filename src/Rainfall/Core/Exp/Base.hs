
module Rainfall.Core.Exp.Base where
import Data.Set         (Set)
import Data.String

data Name
        = Name String
        deriving (Show, Eq, Ord)

instance IsString Name where
 fromString s = Name s

data Bind
        = BindName Name
        | BindNone
        deriving (Show, Eq, Ord)

data Bound
        = Bound Name
        deriving (Show, Eq, Ord)


instance IsString Bind where
 fromString s = BindName (Name s)

type Auth       = Set Name
