
module Rainfall.Core.Eval.Term where
import Rainfall.Core.Transform.MapAnnot
import Rainfall.Core.Exp

import Data.Maybe
import qualified Data.Set               as Set
import qualified Data.Map.Strict        as Map

---------------------------------------------------------------------------------------------------
-- | Evaluate a term.
evalTerm :: Show a => Env -> Term a -> Value

evalTerm env (MAnn _ m')
 = evalTerm env m'

evalTerm env (MVar n)
 | Env nvsEnv <- env
 = case lookup n nvsEnv of
        Just v  -> v
        Nothing -> error $ "execTerm: unbound variable " ++ show n

evalTerm env (MAbs bs ts mBody)
 = VClo env bs
        (map (mapAnnot (const ())) ts)
        (mapAnnot (const ()) mBody)

evalTerm env (MApp mFun msArg)
 = case evalTerm env mFun of
        VClo env' bs _ts mBody
         -> let vsArg   = map (evalTerm env') msArg
                env''   = Env [ (n, v) | BindName n <- bs | v <- vsArg]
            in  evalTerm env'' mBody

        vFun -> error $ unlines
                [ "evalTerm: invalid application"
                , "  vFun       = " ++ show vFun
                , "  msArg      = " ++ show msArg ]

evalTerm _env (MRef mr)
 = case mr of
        MRVal v -> v

evalTerm env (MRcd ns ms)
 = let  vs      = map (evalTerm env) ms
   in   VRcd ns vs

evalTerm env (MPrj mRcd nField)
 = case evalTerm env mRcd of
        VRcd ns vs
         -> case lookup nField (zip ns vs) of
                Just v  -> v
                Nothing -> error $ "evalTerm: missing field " ++ show nField

        VFact fact
         | Env nvsEnv <- factEnv fact
         -> case lookup nField nvsEnv of
                Just v  -> v
                Nothing -> error $ "evalTerm: missing field " ++ show nField

        v  -> error $ unlines
                [ "evalTerm: cannot project field from non-record"
                , "  value = " ++ show v
                , "  field = " ++ show nField ]

evalTerm env (MSay nFact mData mBy mObs mUse mNum)
 | VRcd nsData vsData   <- evalTerm env mData
 , nvsData              <- zip nsData vsData
 = let
        nsBy    = fromMaybe (error "evalTerm: by val is not an auth set")
                $ takeAuthOfValue  $ evalTerm env mBy

        nsObs   = fromMaybe (error "evalTerm: obs val is not an auth set")
                $ takeAuthOfValue  $ evalTerm env mObs

        nsUse   = fromMaybe (error "evalTerm: use val is not a rules set")
                $ takeRulesOfValue $ evalTerm env mUse

        nNum    = fromMaybe (error $ "evalTerm: num val is not a nat" ++ show mNum)
                $ takeNatOfValue   $ evalTerm env mNum

        fact    = Fact
                { factName      = nFact
                , factEnv       = Env nvsData
                , factBy        = nsBy
                , factObs       = nsObs
                , factUse       = nsUse }

   in   VMap $ Map.singleton
                (VFact fact)
                (VNat nNum)

 | otherwise
 = error $ "evalTerm: runtime type error in 'say'"

evalTerm env (MSet msElem)
 = let  vsElem  = map (evalTerm env) msElem
   in   VSet $ Set.fromList $ vsElem

evalTerm _ m@(MKey{})
 = error $ "evalTerm: malformed term"
        ++ show m


---------------------------------------------------------------------------------------------------
evalPrim :: Name -> [Value] -> Value

evalPrim "bool'eq"      [VBool b1, VBool b2]    = VBool (b1 == b2)

evalPrim "nat'add"      [VNat n1, VNat n2]      = VNat  (n1 + n2)
evalPrim "nat'sub"      [VNat n1, VNat n2]      = VNat  (n1 - n2)
evalPrim "nat'eq"       [VNat n1, VNat n2]      = VBool (n1 == n2)
evalPrim "nat'ge"       [VNat n1, VNat n2]      = VBool (n1 >= n2)
evalPrim "nat'le"       [VNat n1, VNat n2]      = VBool (n1 <= n2)

evalPrim "text'eq"      [VText t1, VText t2]    = VBool (t1 == t2)

evalPrim "symbol'eq"    [VSym s1, VSym s2]      = VBool (s1 == s2)

evalPrim "party'eq"     [VParty p1, VParty p2]  = VBool (p1 == p2)

evalPrim "set'one"      [v]                     = VSet (Set.singleton v)
evalPrim "set'union"    [VSet vs1, VSet vs2]    = VSet (Set.union vs1 vs2)

evalPrim name vsArg
 = error $ unlines
        [ "evalPrim: invalid primitive application"
        , "  name = " ++ show name
        , "  args = " ++ show vsArg ]
