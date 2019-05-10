
module Rainfall.Core.Exp.Term where
import Rainfall.Core.Exp.Base
import Data.String
import Data.Set                 (Set)
import Data.Map                 (Map)


---------------------------------------------------------------------------------------------------
-- | Type expression.
data Type a
        = TAnn a (Type a)
        | TUnit
        | TBool
        | TNat
        | TText
        | TSym
        | TParty
        | TSet  (Type a)
        | TFact (Type a)
        | TFoid
        | TRcd  [Name]   [Type a]
        | TFun  (Type a) (Type a)
        deriving (Show, Eq, Ord)


---------------------------------------------------------------------------------------------------
-- | Term expression.
data Term a
        = MAnn  a (Term a)                      -- ^ Annotation.

        | MVar  Name                            -- ^ Variable.
        | MAbs  [Bind] [Type a] (Term a)        -- ^ Function Abstraction.
        | MApp  (Term a) [Term a]               -- ^ Function Application.

        | MRef  (TermRef a)                     -- ^ Reference.

        | MKey  TermKey [Term a]                -- ^ Keyword application.
        deriving (Show, Eq, Ord)


-- | Term reference.
data TermRef a
        = MRVal Value                           -- ^ Embed a value.
        deriving (Show, Eq, Ord)


-- | Term keyword.
data TermKey
        = MKPrm Name                            -- ^ Primitive application.
        | MKRcd [Name]                          -- ^ Construct a record.
        | MKPrj Name                            -- ^ Project a field from a record.
        | MKSet                                 -- ^ Construct a set.
        | MKSay Name                            -- ^ Construct a factoid.
        deriving (Show, Eq, Ord)


instance IsString (Term a) where
 fromString s = MVar (Name s)


---------------------------------------------------------------------------------------------------
data Value
        = VLit  Lit                             -- ^ Literal value.
        | VClo  Env [Bind] [Type ()] (Term ())  -- ^ Function closure
        | VRcd  [Name] [Value]                  -- ^ Record value.
        | VSet  (Set Value)                     -- ^ Set value.
        | VMap  (Map Value Value)               -- ^ Map value.
        | VFact  Fact                           -- ^ Fact value.
        deriving (Show, Eq, Ord)

data Lit
        = LUnit
        | LBool  Bool
        | LNat   Integer
        | LText  String
        | LSym   Name
        | LParty Name
        deriving (Show, Eq, Ord)

data Clo = Clo Env [(Bind, Type ())] (Term ())
         deriving (Show, Eq, Ord)

data Env = Env [(Name, Value)]
         deriving (Show, Eq, Ord)


instance IsString Value where
 fromString s = VLit (LText s)


---------------------------------------------------------------------------------------------------
data Fact
        = Fact
        { factName      :: Name
        , factEnv       :: Env
        , factBy        :: Set Name
        , factObs       :: Set Name
        , factUse       :: Set Name }
        deriving (Show, Eq, Ord)

type Factoid    = (Fact, Weight)
type Factoids   = Map Fact Weight


