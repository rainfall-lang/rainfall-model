
module Rainfall.Source.Check.Term where
import Rainfall.Source.Check.Base
import Rainfall.Source.Codec.Text.Pretty
import Control.Monad
import Text.PrettyPrint.Leijen  hiding ((<$>))


------------------------------------------------------------------------------------------- Term --
-- | Type check a single term.
checkTerm
        :: RL -> Context RL
        -> Term RL -> IO (Term RL, Type RL)

checkTerm _a ctx (MAnn a m)
 = do   (m', t) <- checkTerm a ctx m
        return  (MAnn a m', t)

checkTerm _a _ctx (MRef (MRVal v))
 = do   t'  <- checkValue v
        return  (MRef (MRVal v), t')

checkTerm a ctx m@(MVar (Bound n))
 = case lookup n $ contextLocal ctx of
        Nothing -> nope a [text " unknown variable " <> squotes (ppName n) ]
        Just t  -> return (m, t)

checkTerm _a _ctx (MAbs{})
 = error "checkTerm: general abstraction not used yet."

checkTerm a ctx (MPrm nPrm mgsArg)
 | Just (tsParam, tResult) <- typeOfPrim nPrm
 = do
        when (length tsParam /= length mgsArg)
         $ nope a [ text "wrong number of arguments in primitive application"
                  , text " expected " <> int (length tsParam)
                  , text " actual   " <> int (length mgsArg) ]

        mgsArg' <- zipWithM (checkTermArgIs a ctx) mgsArg tsParam

        return (MPrm nPrm mgsArg', tResult)

 | otherwise
 = nope a [ text " unknown primitive " <> squotes (ppName nPrm) ]

checkTerm _a _ctx (MApp{})
 = error "checkTerm: general application not used yet."

checkTerm a ctx (MRcd nsField msField)
 = do
        (msField', tsField)
         <- fmap unzip $ mapM (checkTerm a ctx) msField

        return  ( MRcd nsField msField'
                , TRcd nsField tsField)

checkTerm a ctx (MPrj mRcd _nField)
 = do
        (mRcd', _tRcd)
         <- checkTerm a ctx mRcd

        return  ( mRcd'
                , TUnit)

checkTerm _a _ctx (MSet msArg)
 = do
        -- TODO: check elems.
        return  ( MSet msArg
                , TSet TBot)

checkTerm _a _ctx (MSay nFact mData msBy msObs msUse msNum)
 = do
        -- TODO: check components.
        return  ( MSay  nFact mData msBy msObs msUse msNum
                , TSets TFACT)

checkTerm _a _ m
 = error $ unlines
        [ "checkTerm: malformed term"
        , show m ]

---------------------------------------------------------------------------------------- TermArg --
checkTermArg
        :: RL -> Context RL
        -> TermArg RL -> IO (TermArg RL, Type RL)

checkTermArg _a ctx (MGAnn a tg)
 = checkTermArg a ctx tg

checkTermArg a ctx (MGTerm m)
 = do   (m', t) <- checkTerm a ctx m
        return (MGTerm m', t)

checkTermArg _ _ MGTerms{}
 = error "checkTermArg: arity mismatch"


checkTermArgIs
        :: RL -> Context RL
        -> TermArg RL -> Type RL
        -> IO (TermArg RL)

checkTermArgIs a ctx mg tExpected
 = do   (mg', tActual)
         <- checkTermArg a ctx mg

        when (not $ checkEq tActual tExpected) $ nope a
         $ [ text "actual type " <> text (show tActual)
--         squotes (ppType tActual)
           , text "does not match"
           , text "expect type " <> text (show tExpected) ]
--           squotes (ppType tExpected) ]

        return mg'


------------------------------------------------------------------------------------------- Prim --
-- | Produce the parameter and result types of a primitive operator.
typeOfPrim :: Name -> Maybe ([Type a], Type a)
typeOfPrim n
 = case n of
        "bool'eq"       -> Just ([TBool, TBool], TBool)
        "bool'and"      -> Just ([TBool, TBool], TBool)
        "bool'or"       -> Just ([TBool, TBool], TBool)

        "nat'add"       -> Just ([TNat, TNat],   TNat)
        "nat'sub"       -> Just ([TNat, TNat],   TNat)
        "nat'eq"        -> Just ([TNat, TNat],   TBool)
        "nat'gt"        -> Just ([TNat, TNat],   TBool)
        "nat'ge"        -> Just ([TNat, TNat],   TBool)
        "nat'lt"        -> Just ([TNat, TNat],   TBool)
        "nat'le"        -> Just ([TNat, TNat],   TBool)

        "text'eq"       -> Just ([TText, TText], TBool)

        "symbol'eq"     -> Just ([TSymbol, TSymbol], TBool)

        "party'eq"      -> Just ([TParty, TParty], TBool)

        "set'one"       -> Just ([TTop], TSet TTop)
        "set'union"     -> Just ([TSet TTop, TSet TTop], TSet TTop)

        "sets'one"      -> Just ([TTop], TSets TTop)
        "sets'some"     -> Just ([TTop, TNat], TSets TTop)
        "sets'union"    -> Just ([TSets TTop, TSets TTop], TSets TTop)

        _               -> Nothing


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

