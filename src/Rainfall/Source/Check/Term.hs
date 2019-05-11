
module Rainfall.Source.Check.Term where
import Rainfall.Source.Check.Base
import Rainfall.Source.Codec.Text.Pretty

import Control.Monad
import Text.PrettyPrint.Leijen          hiding ((<$>))
import qualified Data.Map.Strict        as Map


------------------------------------------------------------------------------------------- Term --
-- | Type check a single term.
checkTerm :: RL -> Context RL
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
 = error "checkTerm: general abstraction not implemented yet."

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
 = error "checkTerm: general application not implemented yet."

checkTerm a ctx (MRcd nsField msField)
 = do
        (msField', tsField)
         <- fmap unzip $ mapM (checkTerm a ctx) msField

        return  ( MRcd nsField msField'
                , TRcd nsField tsField)

checkTerm a ctx (MPrj mRcd nField)
 = do
        (mRcd', tRcd)
         <- checkTerm a ctx mRcd

        ntsField
         <- case tRcd of
                TRcd ns ts -> return $ zip ns ts
                _ -> nope a [ text "term being projected does not have record type"
                            , text " actual type: " <+> squotes (ppType tRcd) ]

        tField
         <- case lookup nField ntsField of
                Just t  -> return t
                _ -> nope a [ text "record does not have field" <+> squotes (ppName nField)
                            , text " record type: " <+> squotes (ppType tRcd) ]

        return  (mRcd', tField)


checkTerm a ctx (MSet msArg)
 = do
        (msArg', tsArg)
         <- fmap unzip $ mapM (checkTerm a ctx) msArg

        tArg
         <- case tsArg of
                []      -> return TTop
                [t]     -> return t
                t : _   -> do   mapM_ (checkTermIs a t ctx) msArg'
                                return t

        return  ( MSet msArg'
                , TSet tArg)

checkTerm a ctx (MSay nFact mData msBy msObs msUse msNum)
 = do
        (nsField, tsField)
         <- fmap unzip
         $  case Map.lookup nFact (contextFacts ctx) of
                Just nts        -> return nts
                _ -> nope a [text "unknown fact " <+> squotes (ppName nFact)]

        mData'  <- checkTermIs a (TRcd nsField tsField) ctx mData
        msBy'   <- mapM (checkTermIs a (TSet TParty)  ctx) msBy
        msObs'  <- mapM (checkTermIs a (TSet TParty)  ctx) msObs
        msUse'  <- mapM (checkTermIs a (TSet TSymbol) ctx) msUse
        msNum'  <- mapM (checkTermIs a (TSet TNat)    ctx) msNum

        return  ( MSay  nFact mData' msBy' msObs' msUse' msNum'
                , TSets TFACT)

checkTerm a ctx mm@(MInfix n m1 m2)
 = case n of
        "&&"    -> checkTerm a ctx (MPrm "bool'and" [MGTerm m1, MGTerm m2])
        "||"    -> checkTerm a ctx (MPrm "bool'or"  [MGTerm m1, MGTerm m2])
        "∧"     -> checkTerm a ctx (MPrm "bool'and" [MGTerm m1, MGTerm m2])
        "∨"     -> checkTerm a ctx (MPrm "bool'or"  [MGTerm m1, MGTerm m2])

        "+"     -> checkTerm a ctx (MPrm "nat'add"  [MGTerm m1, MGTerm m2])
        "-"     -> checkTerm a ctx (MPrm "nat'sub"  [MGTerm m1, MGTerm m2])
        "<"     -> checkTerm a ctx (MPrm "nat'lt"   [MGTerm m1, MGTerm m2])
        ">"     -> checkTerm a ctx (MPrm "nat'gt"   [MGTerm m1, MGTerm m2])
        "≤"     -> checkTerm a ctx (MPrm "nat'le"   [MGTerm m1, MGTerm m2])
        "≥"     -> checkTerm a ctx (MPrm "nat'ge"   [MGTerm m1, MGTerm m2])

        "∪"     -> checkTerm a ctx (MPrm "set'union"        [MGTerm m1, MGTerm m2])
        "∩"     -> checkTerm a ctx (MPrm "set'intersection" [MGTerm m1, MGTerm m2])

        "∪+"    -> checkTerm a ctx (MPrm "sets'union"       [MGTerm m1, MGTerm m2])

        _       -> error $ unlines ["checkTerm: malformed infix exp", show mm]

checkTerm _a _ m
 = error $ unlines ["checkTerm: malformed term", show m]


-- | Check a term, expecting it to have a prior known type.
checkTermIs :: RL -> Type RL -> Context RL
            -> Term RL -> IO (Term RL)

checkTermIs a tExpected ctx m
 = do   (m', tActual) <- checkTerm a ctx m

        when (not $ checkEq tActual tExpected) $ nope a
         $ [ text "actual type " <> squotes (ppType tActual)
           , text "does not match"
           , text "expect type " <> squotes (ppType tExpected) ]

        return m'


---------------------------------------------------------------------------------------- TermArg --
-- | Check a temr argument.
checkTermArg
        :: RL -> Context RL
        -> TermArg RL -> IO (TermArg RL, Type RL)

checkTermArg _a ctx (MGAnn a tg)
 = checkTermArg a ctx tg

checkTermArg a ctx (MGTerm m)
 = do   (m', t) <- checkTerm a ctx m
        return (MGTerm m', t)

checkTermArg _ _ mg@MGTerms{}
 = error $ unlines ["checkTermArg: malformed term", show mg]


-- | Check a term argument, expecting it to have a prior known type.
checkTermArgIs
        :: RL -> Context RL
        -> TermArg RL -> Type RL
        -> IO (TermArg RL)

checkTermArgIs a ctx mg tExpected
 = do   (mg', tActual)
         <- checkTermArg a ctx mg

        when (not $ checkEq tActual tExpected) $ nope a
         $ [ text "actual type " <> squotes (ppType tActual)
           , text "does not match"
           , text "expect type " <> squotes (ppType tExpected) ]

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

