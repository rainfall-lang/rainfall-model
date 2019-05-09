
module Rainfall.Source.Exp.Term.Patterns where
import Rainfall.Source.Exp.Term.Base

------------------------------------------------------------------------------------------- Term --
pattern MVal v                  = MRef  (MRVal v)
pattern MPrm n                  = MRef  (MRPrm n)
pattern MCon n                  = MRef  (MRCon n)

pattern MRecord ns ms           = MKey  (MKRecord ns)   [MGTerms ms]
pattern MSet ms                 = MKey  MKSet           [MGTerms ms]

------------------------------------------------------------------------------------------ Value --
pattern MSym n                  = MRef  (MRVal (VSym n))
pattern MParty n                = MRef  (MRVal (VParty n))
pattern MUnit                   = MRef  (MRVal VUnit)
pattern MBool b                 = MRef  (MRVal (VBool b))
pattern MTrue                   = MRef  (MRVal (VBool True))
pattern MFalse                  = MRef  (MRVal (VBool False))
pattern MNat i                  = MRef  (MRVal (VNat i))
pattern MInt i                  = MRef  (MRVal (VInt i))
pattern MText tx                = MRef  (MRVal (VText tx))


