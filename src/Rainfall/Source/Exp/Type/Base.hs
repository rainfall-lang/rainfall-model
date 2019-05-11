
module Rainfall.Source.Exp.Type.Base where
import Rainfall.Core.Exp.Base
import Data.String


-- | Annotated Type.
data Type a
        = TAnn a (Type a)                       -- ^ Annotated type.
        | TRef (TypeRef a)                      -- ^ Type reference.
        | TVar Bound                            -- ^ Type variable.
        | TAbs (TypeParam a) (Type a)           -- ^ Type abstraction.
        | TKey TypeKey [Type a]                 -- ^ Type keyword application.
        deriving (Show, Eq, Ord)


-- | Kinds are represented the same way as types.
type Kind a = Type a


-- | Type Reference.
data TypeRef a
        = TRPrm Name                    -- ^ Primitive type constructor.
        | TRCon Name                    -- ^ User defined type synonym or constructor.
        deriving (Show, Eq, Ord)


-- | Type Parameter.
data TypeParam a
        = TPAnn a (TypeParam a)
        | TPType (Bind, Type a)         -- ^ Type parameter.
        deriving (Show, Eq, Ord)


-- | Type Key.
data TypeKey
        = TKBot                         -- ^ Used as the element type of empty collections.
        | TKFun                         -- ^ Function type former.
        | TKRcd  [Name]                 -- ^ Record type former.
        | TKSet                         -- ^ Set type former.
        | TKSets                        -- ^ Multi-set type former.
        | TKFact                        -- ^ Fact type former.
        | TKFACT                        -- ^ Opaque fact type former.
        deriving (Show, Eq, Ord)


instance IsString (Type a) where
 fromString name = TVar (Bound (Name name))
