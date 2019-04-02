
module Rainfall.Core.Eval.Term where
import Rainfall.Core.Exp
import qualified Data.List.Extra        as List


---------------------------------------------------------------------------------------------------
-- | Reduce a term to a value.
evalTerm :: Show a => Env a -> Term a -> Value a

evalTerm env (MAnn _ m')
 = evalTerm env m'

evalTerm env (MVar n)
 = case lookup n env of
        Just v  -> v
        Nothing -> error $ "evalTerm: unbound variable " ++ show n

evalTerm env (MAbs bs ts mBody)
 = VClo env bs ts mBody

evalTerm env (MApp mFun msArg)
 = case evalTerm env mFun of
        VClo env bs ts mBody
         -> let env'    = [ (n, v) | BindName n <- bs
                                   | v          <- map (evalTerm env) msArg ]
            in  evalTerm env' mBody

        VPrm name
         -> let vsArg   = map (evalTerm env) msArg
            in  evalPrim name vsArg

        vFun -> error $ unlines
                [ "evalTerm: invalid application"
                , "  vFun       = " ++ show vFun
                , "  msArg      = " ++ show msArg ]


evalTerm env (MRef mr)
 = case mr of
        MRVal v -> v

evalTerm env (MRcd ns ms)
 = VRcd ns (map (evalTerm env) ms)

evalTerm env (MPrj mRcd nField)
 = case evalTerm env mRcd of
        VRcd ns vs
         -> case lookup nField (zip ns vs) of
                Just v  -> v
                Nothing -> error $ "evalTerm: missing field " ++ show nField

        VFact fact
         -> case lookup nField (factEnv fact) of
                Just v  -> v
                Nothing -> error $ "evalTerm: missing field " ++ show nField

        v  -> error $ unlines
                [ "evalTerm: cannot project field from non-record"
                , "  value = " ++ show v
                , "  field = " ++ show nField ]


---------------------------------------------------------------------------------------------------
evalPrim :: Show a => Name -> [Value a] -> Value a

evalPrim "nat'add"      [VNat n1, VNat n2]      = VNat (n1 + n2)

evalPrim "symbol'eq"    [VSym s1, VSym s2]      = VBool (s1 == s2)

evalPrim "party'eq"     [VParty p1, VParty p2]  = VBool (p1 == p2)

evalPrim "auth'one"     [VParty p]              = VAuth [p]
evalPrim "auth'union"   [VAuth a1, VAuth a2]    = VAuth (List.nubOrd $ a1 ++ a2)

evalPrim name vsArg
 = error $ unlines
        [ "evalPrim: invalid primitive application"
        , "  name = " ++ show name
        , "  args = " ++ show vsArg ]
