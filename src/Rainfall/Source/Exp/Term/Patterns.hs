
module Rainfall.Source.Exp.Term.Patterns where
import Rainfall.Source.Exp.Term.Base

------------------------------------------------------------------------------------------- Term --
pattern MVal v                  = MRef  (MRVal v)

pattern MPrm n ms               = MKey  (MKPrm n) ms

pattern MAps mFun mgssArg       = MKey   MKApp  (MGTerm  mFun : mgssArg)
pattern MApp mFun mgsArg        = MKey   MKApp  [MGTerm  mFun, mgsArg]
pattern MApv mFun mArg          = MKey   MKApp  [MGTerm  mFun, MGTerm  mArg]
pattern MApm mFun msArg         = MKey   MKApp  [MGTerm  mFun, MGTerms msArg]
pattern MApt mFun tsArg         = MKey   MKApp  [MGTerm  mFun, MGTypes tsArg]

pattern MRecord ns ms           = MKey  (MKRecord ns)   [MGTerms ms]
pattern MProject m n            = MKey  (MKProject n)   [MGTerm m]
pattern MSet ms                 = MKey  MKSet           [MGTerms ms]

pattern MSay n mData msBy msObs msUse msNum
 = MKey (MKSay n) [MGTerm mData, MGTerms msBy, MGTerms msObs, MGTerms msUse, MGTerms msNum]

------------------------------------------------------------------------------------------ Value --
pattern MSym n                  = MRef  (MRVal (VSym n))
pattern MParty n                = MRef  (MRVal (VParty n))
pattern MUnit                   = MRef  (MRVal VUnit)
pattern MBool b                 = MRef  (MRVal (VBool b))
pattern MTrue                   = MRef  (MRVal (VBool True))
pattern MFalse                  = MRef  (MRVal (VBool False))
pattern MNat i                  = MRef  (MRVal (VNat i))
pattern MText tx                = MRef  (MRVal (VText tx))


