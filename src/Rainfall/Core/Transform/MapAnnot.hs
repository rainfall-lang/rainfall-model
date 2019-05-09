
module Rainfall.Core.Transform.MapAnnot where
import Rainfall.Core.Exp.Term
import qualified Data.Map.Strict        as Map


class MapAnnot c where
 mapAnnot :: (a -> b) -> c a -> c b


instance MapAnnot Type where
 mapAnnot f tt
  = case tt of
        TAnn a t        -> TAnn (f a) (mapAnnot f t)
        TUnit           -> TUnit
        TBool           -> TBool
        TNat            -> TNat
        TText           -> TText
        TSym            -> TSym
        TParty          -> TParty
        TSet t          -> TSet  (mapAnnot f t)
        TFact t         -> TFact (mapAnnot f t)
        TFoid           -> TFoid
        TRcd ns ts      -> TRcd ns (map (mapAnnot f) ts)
        TFun t1 t2      -> TFun (mapAnnot f t1) (mapAnnot f t2)


instance MapAnnot Term where
 mapAnnot f mm
  = case mm of
        MAnn a m        -> MAnn (f a) (mapAnnot f m)

        MVar n          -> MVar n

        MAbs bs ts m    -> MAbs bs (map (mapAnnot f) ts) (mapAnnot f m)
        MApp mFun msArg -> MApp (mapAnnot f mFun) (map (mapAnnot f) msArg)

        MRef tr         -> MRef (mapAnnot f tr)

        MKey tk ms      -> MKey tk (map (mapAnnot f) ms)


instance MapAnnot TermRef where
 mapAnnot f tr
  = case tr of
        MRVal v         -> MRVal (mapAnnot f v)


instance MapAnnot Value where
 mapAnnot f vv
  = case vv of
        VLit lit        -> VLit lit
        VClo en bs ts m -> VClo (mapAnnot f en) bs (map (mapAnnot f) ts) (mapAnnot f m)
        VRcd ns vs      -> VRcd ns (map (mapAnnot f) vs)
        VSet vs         -> VSet vs
        VMap kvs        -> VMap $ Map.fromList [ (k, mapAnnot f v) | (k, v) <- Map.toList kvs]
        VFact fact      -> VFact (mapAnnot f fact)


instance MapAnnot Env where
 mapAnnot f (Env nvs)
  = Env [ (n, mapAnnot f m) | (n, m) <- nvs ]


instance MapAnnot Fact where
 mapAnnot f (Fact n env nsBy nsObs nsUse)
  = Fact n (mapAnnot f env) nsBy nsObs nsUse

