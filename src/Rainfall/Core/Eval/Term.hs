
module Rainfall.Core.Eval.Term where
import Rainfall.Core.Eval.Store
import Rainfall.Core.Exp

import Data.Maybe
import qualified Data.List.Extra        as List
import qualified Data.Set               as Set


---------------------------------------------------------------------------------------------------
-- | Evaluate a term.
--
--   This is like `execTerm` except that we require the list of produced
--   factoids to be empty.
evalTerm :: Show a => Env a -> Term a -> Value a
evalTerm env mm
 = case execTerm env mm of
        (v, []) -> v
        _       -> error $ "evalTerm: term produced factoids."


---------------------------------------------------------------------------------------------------
-- | Execute a term, producing a value and set of created factoids.
execTerm :: Show a => Env a -> Term a -> (Value a, [Factoid a])

execTerm env (MAnn _ m')
 = execTerm env m'

execTerm env (MVar n)
 = case lookup n env of
        Just v  -> (v, [])
        Nothing -> error $ "execTerm: unbound variable " ++ show n

execTerm env (MAbs bs ts mBody)
 = (VClo env bs ts mBody, [])

execTerm env (MApp mFun msArg)
 = case execTerm env mFun of
        (VClo env bs ts mBody, fsFun)
         -> let (vsArg, fsArg)  = unzip $ map (execTerm env) msArg
                env'            = [ (n, v) | BindName n <- bs | v <- vsArg]
                (vBody, fsBody) = execTerm env' mBody
            in  (vBody, fsBody ++ concat fsArg ++ fsFun)

        (VPrm name, fsPrm)
         -> let (vsArg, fsArg)  = unzip $ map (execTerm env) msArg
            in  ( evalPrim name vsArg
                , concat fsArg ++ fsPrm)

        vFun -> error $ unlines
                [ "evalTerm: invalid application"
                , "  vFun       = " ++ show vFun
                , "  msArg      = " ++ show msArg ]

execTerm env (MRef mr)
 = case mr of
        MRVal v -> (v, [])

execTerm env (MRcd ns ms)
 = let  (vs, fss)       = unzip $ map (execTerm env) ms
   in   ( VRcd ns vs
        , concat fss)

execTerm env (MPrj mRcd nField)
 = case execTerm env mRcd of
        (VRcd ns vs, fsRcd)
         -> case lookup nField (zip ns vs) of
                Just v  -> (v, fsRcd)
                Nothing -> error $ "evalTerm: missing field " ++ show nField

        (VFact fact, fsRcd)
         -> case lookup nField (factEnv fact) of
                Just v  -> (v, fsRcd)
                Nothing -> error $ "evalTerm: missing field " ++ show nField

        v  -> error $ unlines
                [ "evalTerm: cannot project field from non-record"
                , "  value = " ++ show v
                , "  field = " ++ show nField ]

execTerm env (MSay nFact mData mMeta)
 | (VRcd nsData vsData, fsData) <- execTerm env mData
 , envData                      <- zip nsData vsData

 , (VRcd nsMeta vsMeta, fsMeta) <- execTerm env mMeta
 , envMeta                      <- zip nsMeta vsMeta
 = let
        vBy     = fromMaybe (VAuth Set.empty) $ lookup "by" envMeta
        aBy     = fromMaybe (error "execTerm: 'by' value in say statement is not an auth set")
                $ takeAuthOfValue vBy

        vObs    = fromMaybe (VAuth Set.empty) $ lookup "obs" envMeta
        aObs    = fromMaybe (error "execTerm: 'obs' value in say statement is not an auth set")
                $ takeAuthOfValue vObs

        vRules  = fromMaybe (VRules []) $ lookup "rules" envMeta
        nsRule  = fromMaybe (error "execTerm: 'rules' value in say statement is not a rules set")
                $ takeRulesOfValue vRules

        vWeight = fromMaybe (VNat 1) $ lookup "weight" envMeta
        nWeight = fromMaybe (error "execTerm: 'weight' value in say statement is not a nat.")
                $ takeNatOfValue vWeight

        fact    = Fact
                { factName      = nFact
                , factEnv       = envData
                , factBy        = aBy
                , factObs       = aObs
                , factRules     = nsRule }

        factoid = (fact, nWeight)

   in   ( VUnit
        , [factoid] ++ fsData ++ fsMeta)


---------------------------------------------------------------------------------------------------
evalPrim :: Show a => Name -> [Value a] -> Value a

evalPrim "nat'add"      [VNat n1, VNat n2]      = VNat (n1 + n2)

evalPrim "symbol'eq"    [VSym s1, VSym s2]      = VBool (s1 == s2)

evalPrim "party'eq"     [VParty p1, VParty p2]  = VBool (p1 == p2)

evalPrim "auth'one"     [VParty p]              = VAuth (Set.singleton p)
evalPrim "auth'union"   [VAuth a1, VAuth a2]    = VAuth (Set.union a1 a2)

evalPrim name vsArg
 = error $ unlines
        [ "evalPrim: invalid primitive application"
        , "  name = " ++ show name
        , "  args = " ++ show vsArg ]
