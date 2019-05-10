
module Rainfall.Core.Transform.MapAnnot where
import Rainfall.Core.Exp.Term


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
 mapAnnot _f tr
  = case tr of
        MRVal v         -> MRVal v


