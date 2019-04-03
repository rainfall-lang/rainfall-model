
module Rainfall.Core.Exp.Compounds where
import Rainfall.Core.Exp.Patterns
import Rainfall.Core.Exp.Term
import Rainfall.Core.Exp.Base


-- | Bind a single value into an environment.
envBind :: Bind -> Value a -> Env a -> Env a
envBind BindNone _ env          = env
envBind (BindName n) v env      = (n, v) : env


-- | Take a natural number from a value, if this is one.
takeNatOfValue :: Value a -> Maybe Integer
takeNatOfValue vv
 = case vv of
        VNat n          -> Just n
        _               -> Nothing


-- | Take an authority set from a value, if this is one.
takeAuthOfValue :: Value a -> Maybe Auth
takeAuthOfValue vv
 = case vv of
        VAuth a         -> Just a
        _               -> Nothing


-- | Take a rules set from a value, if this is one.
takeRulesOfValue :: Value a -> Maybe [Name]
takeRulesOfValue vv
 = case vv of
        VRules ns       -> Just ns
        _               -> Nothing
