
module Rainfall.Source.Exp.Type.Patterns where
import Rainfall.Source.Exp.Type.Base


-- Type refs.
pattern TPrm n          = TRef (TRPrm n)
pattern TCon n          = TRef (TRCon n)


-- Type keywords.
pattern TBot            = TKey TKBot []
pattern TTop            = TKey TKTop []
pattern TFun t1 t2      = TKey TKFun [t1, t2]
pattern TRcd ns ts      = TKey (TKRcd ns) ts
pattern TSet t          = TKey TKSet  [t]
pattern TSets t         = TKey TKSets [t]
pattern TFact t         = TKey TKFact [t]
pattern TFACT           = TKey TKFACT []


-- Primitive types.
pattern TUnit           = TCon "Unit"
pattern TBool           = TCon "Bool"
pattern TNat            = TCon "Nat"
pattern TText           = TCon "Text"
pattern TParty          = TCon "Party"
pattern TSymbol         = TCon "Symbol"
