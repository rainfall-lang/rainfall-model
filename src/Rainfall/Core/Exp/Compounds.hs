
module Rainfall.Core.Exp.Compounds where
import Rainfall.Core.Exp.Patterns
import Rainfall.Core.Exp.Term
import Rainfall.Core.Exp.Base
import qualified Data.Set               as Set
import qualified Data.Map.Strict        as Map


-- | Bind a single value into an environment.
envBind :: Bind -> Value -> Env -> Env
envBind BindNone _ env           = env
envBind (BindName n) v (Env nvs) = Env ((n, v) : nvs)


-- | Take a natural number from a value, if this is one.
takeNatOfValue :: Value -> Maybe Integer
takeNatOfValue vv
 = case vv of
        VNat n   -> Just n
        _        -> Nothing


-- | Take a symbol name from a value.
takeSymOfValue :: Value -> Maybe Name
takeSymOfValue vv
 = case vv of
        VSym n   -> Just n
        _        -> Nothing


-- | Take the party name of a value, if this is one.
takePartyOfValue :: Value -> Maybe Name
takePartyOfValue vv
 = case vv of
        VParty n -> Just n
        _        -> Nothing


-- | Take the contents of a set value.
takeSetOfValue  :: Value -> Maybe (Set Value)
takeSetOfValue vv
 = case vv of
        VSet vs -> Just vs
        _       -> Nothing


-- | Take the contents of a map value.
takeMapOfValue :: Value -> Maybe (Map Value Value)
takeMapOfValue vv
 = case vv of
        VMap vs -> Just vs
        _       -> Nothing


-- | Take an authority set from a value, if this is one.
takeAuthOfValue :: Value -> Maybe (Set Name)
takeAuthOfValue vv
 = case vv of
        VSet vs -> fmap Set.fromList $ sequence $ map takePartyOfValue $ Set.toList vs
        _       -> Nothing


-- | Take a rules set from a value, if this is one.
takeRulesOfValue :: Value -> Maybe (Set Name)
takeRulesOfValue vv
 = case vv of
        VSet vs -> fmap Set.fromList $ sequence $ map takeSymOfValue $ Set.toList vs
        _       -> Nothing


-- | Take a fact from a value, if this is one.
takeFactOfValue :: Value -> Maybe Fact
takeFactOfValue vv
 = case vv of
        VFact f -> Just f
        _       -> Nothing

-- | Take a factoid map from a value.
takeFactoidsOfValue :: Value -> Maybe Factoids
takeFactoidsOfValue vv
 = case vv of
        VMap vs
          |  Just ds  <- sequence $ map takeFactoidOfPair $ Map.toList vs
          -> Just $ Map.fromList ds
        _ -> Nothing


-- | Take a factoid from a pair of fact and weight.
takeFactoidOfPair :: (Value, Value) -> Maybe Factoid
takeFactoidOfPair (vFact, vWeight)
 | Just fact    <- takeFactOfValue vFact
 , Just nWeight <- takeNatOfValue  vWeight
 = Just (fact, nWeight)

 | otherwise = Nothing


