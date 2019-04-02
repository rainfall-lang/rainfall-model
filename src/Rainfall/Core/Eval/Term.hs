
module Rainfall.Core.Eval.Term where
import Rainfall.Core.Exp


-- | Reduce a term to a value.
evalTerm :: Env a -> Term a -> Value a

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

        VPrm "add"
         | [VNat n1, VNat n2]   <- map (evalTerm env) msArg
         -> VNat (n1 + n2)

        _       -> error $ "evalTerm: invalid application"

evalTerm env (MRef mr)
 = case mr of
        MRVal v -> v

evalTerm env (MRcd ns ms)
 = VRcd ns (map (evalTerm env) ms)

evalTerm env (MPrj mRcd n)
 = case evalTerm env mRcd of
        VRcd ns vs
         -> case lookup n (zip ns vs) of
                Just v  -> v
                Nothing -> error $ "evalTerm: missing field " ++ show n

        _       -> error $ "evalTerm: cannot project field from non-record"