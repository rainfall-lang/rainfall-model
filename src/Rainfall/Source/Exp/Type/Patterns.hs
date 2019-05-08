
module Rainfall.Source.Exp.Type.Patterns where
import Rainfall.Source.Exp.Type.Base

-- Type refs.
pattern TCon n          = TRef (TRCon n)
pattern TPrm n          = TRef (TRPrm n)

-- Type keywords.
pattern TArr    ks1 k2  = TKey TKArr [TGType ks1,  TGType k2]

-- Primitive types.
pattern TType           = TPrm "Type"
pattern TData           = TPrm "Data"
pattern TUnit           = TPrm "Unit"
pattern TBool           = TPrm "Bool"
pattern TNat            = TPrm "Nat"
pattern TInt            = TPrm "Int"
pattern TText           = TPrm "Text"
pattern TSymbol         = TPrm "Symbol"
