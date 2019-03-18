
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

pattern MPrm n          = MRef (MRPrm n)
pattern MVal v          = MRef (MRVal v)
pattern MLit l          = MRef (MRVal (VLit l))

pattern MUnit           = MLit (LUnit)
pattern MBool b         = MLit (LBool b)
pattern MTrue           = MLit (LBool True)
pattern MFalse          = MLit (LBool False)
pattern MSym  n         = MLit (LSym  n)
pattern MNat  n         = MLit (LNat  n)
pattern MText s         = MLit (LText s)
pattern MParty s        = MLit (LParty s)
pattern MAuth  ns       = MLit (LAuth ns)
pattern MRules ns       = MLit (LRules ns)


---------------------------------------------------------------------------------------------------
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

pattern VUnit           = VLit LUnit
pattern VBool b         = VLit (LBool b)
pattern VTrue           = VLit (LBool True)
pattern VFalse          = VLit (LBool False)
pattern VSym s          = VLit (LSym  s)
pattern VNat n          = VLit (LNat  n)
pattern VText s         = VLit (LText s)
pattern VParty s        = VLit (LParty s)
pattern VAuth ns        = VLit (LAuth ns)
pattern VRules ns       = VLit (LRules ns)

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




