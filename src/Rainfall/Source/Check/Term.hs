
module Rainfall.Source.Check.Term where
import Rainfall.Source.Check.Base


------------------------------------------------------------------------------------------- Term --
-- | Type check a single term.
checkTerm
        :: Show a
        => Context a -> Term a -> IO (Term a, Type a)

checkTerm ctx (MAnn a m)
 = do   (m', t) <- checkTerm ctx m
        return  (MAnn a m', t)

checkTerm _ctx (MRef (MRVal v))
 = do   t'  <- checkValue v
        return  (MRef (MRVal v), t')

checkTerm ctx m@(MVar (Bound n))
 = case lookup n $ contextLocal ctx of
        Nothing -> error $ "checkTerm: variable not in scope " ++ show n
        Just t  -> return (m, t)

checkTerm _ctx (MAbs{})
 = error "checkTerm: general abstraction not used yet."

checkTerm _ctx m@(MPrm _nPrm _mgsArg)
 = return (m, TUnit)

checkTerm _ctx (MApp{})
 = error "checkTerm: general application not used yet."

checkTerm ctx (MRcd nsField msField)
 = do
        (msField', tsField)
         <- fmap unzip $ mapM (checkTerm ctx) msField

        return  ( MRcd nsField msField'
                , TRcd nsField tsField)

checkTerm ctx (MPrj mRcd _nField)
 = do
        (mRcd', _tRcd)
         <- checkTerm ctx mRcd

        return  ( mRcd'
                , TUnit)

checkTerm _ctx (MSet msArg)
 = do
        -- TODO: check elems.
        return  ( MSet msArg
                , TSet TBot)

checkTerm _ctx (MSay nFact mData msBy msObs msUse msNum)
 = do
        -- TODO: check components.
        return  ( MSay  nFact mData msBy msObs msUse msNum
                , TSets TFACT)

checkTerm _ m
 = error $ unlines
        [ "checkTerm: malformed term"
        , show m ]

------------------------------------------------------------------------------------------ Value --
checkValue :: Value -> IO (Type a)
checkValue vv
 = case vv of
        VUnit    -> return TUnit
        VBool{}  -> return TBool
        VNat{}   -> return TNat
        VText{}  -> return TText
        VSym{}   -> return TSymbol
        VParty{} -> return TParty

