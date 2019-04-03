
module Rainfall.Core.Exp.Patterns where
import Rainfall.Core.Exp.Base
import Rainfall.Core.Exp.Rule
import Rainfall.Core.Exp.Term


------------------------------------------------------------------------------------------- Term --
pattern MVal v          = MRef (MRVal v)
pattern MPrm n          = MRef (MRVal (VPrm n))
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

pattern MSay n mD mM    = MKey MKSay [MSym n, mD, mM]

------------------------------------------------------------------------------------------ Value --
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

