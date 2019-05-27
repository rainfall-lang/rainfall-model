
module Rainfall.Core.Exp.Patterns where
import Rainfall.Core.Exp.Term


----------------------------------------------------------------------- Term --
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

pattern MPrm n ms       = MKey (MKPrm n) ms
pattern MRcd ns ms      = MKey (MKRcd ns) ms
pattern MPrj m n        = MKey (MKPrj n)  [m]

pattern MSay n mData mBy mObs mUse mNum
 = MKey (MKSay n) [mData, mBy, mObs, mUse, mNum]

pattern MSet ms         = MKey MKSet ms

---------------------------------------------------------------------- Value --
pattern VUnit           = VLit LUnit
pattern VBool b         = VLit (LBool b)
pattern VNat n          = VLit (LNat  n)
pattern VTrue           = VLit (LBool True)
pattern VFalse          = VLit (LBool False)
pattern VText s         = VLit (LText s)
pattern VSym s          = VLit (LSym  s)
pattern VParty s        = VLit (LParty s)

