
module Core.Exp.Term where
import Core.Exp.Base
import Data.List

-------------------------------------------------------------------------------
data Type
        = TUnit
        | TBool
        | TSym
        | TNat
        | TText
        | TAuth
        deriving Show


-------------------------------------------------------------------------------
data Term
        = MVar Name
        | MApp Term Term
        | MAbs Name Type Term
        | MLit Lit
        deriving Show


pattern MUnit   = MLit (LUnit)
pattern MBool b = MLit (LBool b)
pattern MTrue   = MLit (LBool True)
pattern MFalse  = MLit (LBool False)
pattern MSym  n = MLit (LSym  n)
pattern MNat  n = MLit (LNat  n)
pattern MText s = MLit (LText s)



-------------------------------------------------------------------------------
data Value
        = VLit  Lit
        | VClo  Env Name Type Term
        | VFact Fact
        deriving Show

pattern VUnit   = VLit LUnit
pattern VBool b = VLit (LBool b)
pattern VTrue   = VLit (LBool True)
pattern VFalse  = VLit (LBool False)
pattern VSym s  = VLit (LSym  s)
pattern VNat n  = VLit (LNat  n)
pattern VText s = VLit (LText s)

data Lit
        = LUnit
        | LBool Bool
        | LSym  Name
        | LNat  Integer
        | LText String
        deriving Show

data Clo  = Clo  Env  Name Type Term

data Fact
        = Fact
        { factName      :: Name
        , factEnv       :: Env
        , factBy        :: Auth
        , factObs       :: Auth
        , factFor       :: Auth
        , factUse       :: Term }
        deriving Show

type Env = [(Name, Value)]

sees  :: Auth -> Fact -> Bool
sees aHas (Fact n _env aBy aObs aFor aUse)
 = not $ null $ intersect aHas (union aBy aObs)

-- gains :: Auth -> Fact -> Maybe Auth
-- gains aHas (Fact n _env aBy aObs aFor mUse)
-- =


aBob    = ["Bob"]

fTok    = Fact "Tok" [("stamp", VSym "Dude")] aBob aBob [] mcFalse
mcFalse = MAbs "x" TAuth MFalse




