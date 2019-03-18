
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
        = MAnn  a (Term a)

        | MVar  Name
        | MApp  (Term a) [Term a]
        | MAbs  Name (Type a) (Term a)

        | MRef  (TermRef a)

        | MRcd  [(Name, Term a)]
        | MPrj  (Term a) Name
        deriving Show


data TermRef a
        = MRPrm Name
        | MRVal (Value a)
        deriving Show


---------------------------------------------------------------------------------------------------
data Value a
        = VLit  Lit
        | VClo  (Env  a) Name (Type a) (Term a)
        | VRcd  [(Name, Value a)]
        | VFact (Fact a)
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

data Clo a = Clo  (Env a) Name (Type a) (Term a)
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
data Store  = Store [ (Fact (), Weight) ]
