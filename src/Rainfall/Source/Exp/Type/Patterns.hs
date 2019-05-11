
module Rainfall.Source.Exp.Type.Patterns where
import Rainfall.Source.Exp.Type.Base


-- Type refs.
pattern TCon n          = TRef (TRCon n)
pattern TPrm n          = TRef (TRPrm n)


-- Type keywords.
pattern TBot            = TKey TKBot []
pattern TFun t1 t2      = TKey TKFun [t1, t2]
pattern TRcd ns ts      = TKey (TKRcd ns) ts
pattern TSet t          = TKey TKSet  [t]
pattern TSets t         = TKey TKSets [t]
pattern TFact t         = TKey TKFact [t]
pattern TFACT           = TKey TKFACT []


-- Primitive types.
pattern TUnit           = TPrm "Unit"
pattern TBool           = TPrm "Bool"
pattern TNat            = TPrm "Nat"
pattern TText           = TPrm "Text"
pattern TParty          = TPrm "Party"
pattern TSymbol         = TPrm "Symbol"
