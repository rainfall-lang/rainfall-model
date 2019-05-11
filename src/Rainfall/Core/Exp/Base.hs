
module Rainfall.Core.Exp.Base
        ( Set, Map
        , Name (..), takeName
        , Bind (..)
        , Bound (..)
        , Auth, Rules
        , Weight)
where
import Data.Set         (Set)
import Data.Map         (Map)
import Data.String

data Name
        = Name String
        deriving (Show, Eq, Ord)

takeName :: Name -> String
takeName (Name n) = n

data Bind
        = BindName Name
        | BindNone
        deriving (Show, Eq, Ord)

data Bound
        = Bound Name
        deriving (Show, Eq, Ord)


instance IsString Name where
 fromString s = Name s

instance IsString Bind where
 fromString s = BindName (Name s)

instance IsString Bound where
 fromString s = Bound (Name s)

type Auth       = Set Name
type Rules      = Set Name
type Weight     = Integer
