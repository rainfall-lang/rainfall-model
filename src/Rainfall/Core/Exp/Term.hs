
module Rainfall.Core.Exp.Term where
import Rainfall.Core.Exp.Base
import Data.List

---------------------------------------------------------------------------------------------------
data Type a
        = TAnn a (Type a)
        | TUnit
        | TBool
        | TSym
        | TNat
        | TText
        | TAuth
        deriving Show


---------------------------------------------------------------------------------------------------
data Term a
        = MAnn  a (Term a)                      -- ^ Annotation.

        | MVar  Name                            -- ^ Variable.
        | MAbs  [Bind] [Type a] (Term a)        -- ^ Abstraction.
        | MApp  (Term a) [Term a]               -- ^ Application.

        | MRef  (TermRef a)                     -- ^ Reference.

        | MRcd  [Name]   [Term a]               -- ^ Record former.
        | MPrj  (Term a) Name                   -- ^ Record projection.
        deriving Show


data TermRef a
        = MRVal (Value a)                       -- ^ Embed a value.
        deriving Show


---------------------------------------------------------------------------------------------------
data Value a
        = VLit  Lit                              -- ^ Literal value.
        | VPrm  Name                             -- ^ Primitive reference.
        | VClo  (Env a) [Bind] [Type a] (Term a) -- ^ Function closure
        | VRcd  [Name] [Value a]                 -- ^ Record value.
        | VFact (Fact a)                         -- ^ Fact value.
        deriving Show

data Lit
        = LUnit
        | LBool  Bool
        | LSym   Name
        | LNat   Integer
        | LText  String
        | LParty Name
        | LAuth  Auth
        | LRules [Name]
        deriving Show

data Clo a = Clo  (Env a) [(Bind, Type a)] (Term a)
type Env a = [(Name, Value a)]


---------------------------------------------------------------------------------------------------
data Fact a
        = Fact
        { factName      :: Name
        , factEnv       :: Env a
        , factBy        :: Auth
        , factObs       :: Auth
        , factRules     :: [Name] }
        deriving Show

type Weight = Int

data Store
        = Store [ (Fact (), Weight) ]
        deriving Show

