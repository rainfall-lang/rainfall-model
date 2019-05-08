
module Rainfall.Source.Exp.Type.Base where
import Rainfall.Core.Exp.Base
import Data.String
import Data.Map                 (Map)


-- | Annotated Type.
data Type a
        = TAnn a (Type a)                       -- ^ Annotated type.
        | TRef (TypeRef a)                      -- ^ Type reference.
        | TVar Bound                            -- ^ Type variable.
        | TAbs (TypeParam a) (Type a)           -- ^ Type abstraction.
        | TKey TypeKey [TypeArg a]              -- ^ Type keyword application.
        deriving (Show, Eq, Ord)


-- | Kinds are represented the same way as types.
type Kind a = Type a


-- | Type Reference.
data TypeRef a
        = TRPrm Name                            -- ^ Primitive type constructor.
        | TRCon Name                            -- ^ User defined type synonym or constructor.
        | TRClo (TypeClosure a)                 -- ^ Type closure.
        deriving (Show, Eq, Ord)


-- | Type Parameter.
data TypeParam a
        = TPAnn a (TypeParam a)
        | TPType (Bind, Type a)                 -- ^ Type parameter.
        deriving (Show, Eq, Ord)


-- | Type Arguments.
data TypeArg a
        = TGAnn a (TypeArg a)
        | TGType (Type a)                       -- ^ Type argument.
        deriving (Show, Eq, Ord)


-- | Type Key.
data TypeKey
        = TKHole                                -- ^ A missing type that needs to be inferred.
        | TKArr                                 -- ^ Kind arrow.
        | TKApp                                 -- ^ Type application.
        | TKFun                                 -- ^ Function type former.
        | TKForall                              -- ^ Forall type former.
        | TKExists                              -- ^ Exists type former.
        | TKRecord  [Name]                      -- ^ Record type former.
        | TKVariant [Name]                      -- ^ Variant type former.
        deriving (Show, Eq, Ord)


-- | Type Closure.
data TypeClosure a
        = TypeClosure (TypeEnv a) (TypeParam a) (Type a)
        deriving (Show, Eq, Ord)


-- | Environments captured in type closures.
data TypeEnv a
        = TypeEnv [TypeEnvBinds a]
        deriving (Show, Eq, Ord)


-- | Bindings in environments.
data TypeEnvBinds a
        = TypeEnvTypes (Map Name (Type a))
        deriving (Show, Eq, Ord)


instance IsString (Type a) where
 fromString name = TVar (Bound (Name name))
