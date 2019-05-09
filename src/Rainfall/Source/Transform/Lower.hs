
module Rainfall.Source.Transform.Lower where
import Rainfall.Core.Exp.Base
import qualified Rainfall.Source.Exp                    as E
import qualified Rainfall.Core.Exp                      as C
import qualified Rainfall.EDSL                          as CC
import qualified Control.Monad.Trans.State.Strict       as S
import Data.Maybe
import qualified Data.Map.Strict                        as Map
import Data.Map                                         (Map)
import qualified Debug.Trace as Debug


------------------------------------------------------------------------------------------ Fresh --
type S a = S.State (String, Int) a

runState :: String -> S a -> a
runState prefix m
 = S.evalState m (prefix, 1)

fresh :: S Name
fresh
 = do   (prefix, n) <- S.get
        S.put (prefix, n + 1)
        return $ Name (prefix ++ show n)

type Facts a = Map Name [(Name, E.Type a)]


------------------------------------------------------------------------------------------- Decl --
-- | Lower a list of source decls to core.
lowerDecls :: Show a => [E.Decl a] -> S [C.Rule a]
lowerDecls ds
 = do   let dsFact = Map.fromList [(nFact, fs) | E.DeclFact nFact fs <- ds ]
        fmap catMaybes $ mapM (lowerDecl dsFact) ds


-- | Lower a source decl to core.
lowerDecl
        :: Show a
        => Facts a -> E.Decl a
        -> S (Maybe (C.Rule a))

lowerDecl dsFact d
 = case d of
        E.DeclFact{}      -> pure Nothing
        E.DeclRule rule   -> Just <$> lowerRule dsFact rule


------------------------------------------------------------------------------------------- Rule --
-- | Lower a source rule to core.
lowerRule
        :: Show a
        => Facts a -> E.Rule a
        -> S (C.Rule a)

lowerRule dsFact (E.Rule nRule hsMatch _m)
 = do
        (_nmsMatch, hsMatch')
         <- lowerMatches dsFact [] hsMatch

        pure $ C.Rule nRule hsMatch' C.MUnit


------------------------------------------------------------------------------------------ Match --
-- | Lower a sequence of matches to core.
lowerMatches
        :: Show a
        => Facts a
        -> [(Name, C.Term a)]           -- ^ Definition of match variables in scope.
        -> [E.Match a]
        -> S ([(Name, C.Term a)], [C.Match a])

lowerMatches _dsFact nmsMatch []
 = return (nmsMatch, [])

lowerMatches dsFact  nmsMatch (m : ms)
 = do   (nmsMatch', m')   <- lowerMatch   dsFact nmsMatch  m
        (nmsMatch'', ms') <- lowerMatches dsFact nmsMatch' ms
        return (nmsMatch'', (m' : ms'))


-- | Lower a source fact matcher to core.
lowerMatch
        :: Show a
        => Facts a
        -> [(Name, C.Term a)]           -- ^ Definitions of match variable in scope.
        -> E.Match a                    -- ^ Match to desugar.
        -> S ([(Name, C.Term a)], C.Match a)

lowerMatch dsFact nmsMatch (E.MatchAnn a m)
 = do   (nmsMatch', m')
         <- lowerMatch dsFact nmsMatch m

        return  (nmsMatch', C.MatchAnn a m')

lowerMatch dsFact nmsMatch (E.Match mbBind gather _select _consume _gain)
 = do
        nBindFact
          <- case mbBind of
                Just (BindName n)  -> pure n
                Just BindNone      -> fresh
                Nothing            -> fresh

        (nmsMatch', gather')
         <- lowerGather dsFact nmsMatch nBindFact gather

        select'  <- pure $ C.SelectAny
        consume' <- pure $ C.ConsumeNone
        gain'    <- pure $ C.GainNone

        return  ( Debug.trace (show nmsMatch) nmsMatch'
                , C.Match (BindName nBindFact) gather' select' consume' gain')


----------------------------------------------------------------------------------------- Gather --
-- | Lower a gather clause to core.
--
--   We take a list of definitions for enclosing match variables (like ?foo),
--   and use these to produce predicates for 'where' expressions as needed.
--
--   The gather itself may bind new match variables, so we also return a
--   possibly extended list of match definitions.
--
lowerGather
        :: Show a
        => Facts a
        -> [(Name, C.Term a)]           -- ^ Definitions of match variables in scope.
        -> Name                         -- ^ Variable bound to the fact being considered.
        -> E.Gather a                   -- ^ Gather to desugar.
        -> S ([(Name, C.Term a)], C.Gather a)

lowerGather dsFact nmsMatch nBindFact (E.GatherAnn a g)
 = do   (nmsMatch', g')
          <- lowerGather dsFact nmsMatch nBindFact g
        return  (nmsMatch', C.GatherAnn a g')

lowerGather dsFact nmsMatch nBindFact (E.GatherPat nFact fsMatch mmPred)
 = do
        let ntsField = fromMaybe [] $ Map.lookup nFact dsFact

        (mnsMatch', msPred)
         <- lowerGatherFields ntsField nmsMatch [] nBindFact fsMatch

        mmPred'
         <- case mmPred of
                Nothing -> return Nothing
                Just m  -> Just <$> lowerTerm nmsMatch m


        return  ( mnsMatch'
                , C.GatherWhere nFact (maybeToList mmPred' ++ reverse msPred))

lowerGather _dsFact _nmsMatch _nBind _
 = error "lowerGather: not finished"


-- | Lower a list of fields in a gather clause.
--   Match variables defined in earlier fields are in-scope in latter fields.
lowerGatherFields
        :: Show a
        => [(Name, E.Type a)]           -- ^ Types of fields for this fact.
        -> [(Name, C.Term a)]           -- ^ Definitions of match variables in scope.
        -> [C.Term a]                   -- ^ Predicate terms so far.
        -> Name                         -- ^ Variable bound to the fact being gathered.
        -> [(Name, E.GatherPat a)]      -- ^ More field matchings to desugar.
        -> S ([(Name, C.Term a)], [C.Term a])

lowerGatherFields _ntsField nmsMatch msPred
        _nBoundFact []
 =      return (nmsMatch, msPred)

lowerGatherFields ntsField nmsMatch msPred
        nBoundFact ((nField, gatherPat) : rest)
 = do
        (nmMatch, mPred)
         <- lowerGatherPat ntsField nmsMatch nBoundFact nField gatherPat

        let nmsMatch'   = maybeToList nmMatch ++ nmsMatch
        let msPred'     = maybeToList mPred   ++ msPred

        lowerGatherFields ntsField nmsMatch' msPred' nBoundFact rest


-- | Lower a gather pattern.
lowerGatherPat
        :: Show a
        => [(Name, E.Type a)]           -- ^ Types of fields for thie fact.
        -> [(Name, C.Term a)]           -- ^ Definitions of match variables in scope.
        -> Name                         -- ^ Variable bound to the fact being considered.
        -> Name                         -- ^ Name of the current field.
        -> E.GatherPat a                -- ^ Pattern to desguar.
        -> S ( Maybe (Name, (C.Term a)) -- Match variable to bind in the body.
             , Maybe (C.Term a))        -- Match predicate to check.

lowerGatherPat _ntsField _nmsMatch nBindFact nField
        (E.GatherPatBind n)
 = do   return  ( Just (n, C.MPrj (C.MVar nBindFact) nField)
                , Nothing)

lowerGatherPat ntsField nmsMatch nBindFact nField
        (E.GatherPatEq mTerm)
 = do
        -- Lower the match term to core.
        mTerm' <- lowerTerm nmsMatch mTerm

        -- Decide what comparison function to use
        -- to compare the field value with the stated term.
        let fEq = case lookup nField ntsField of
                        Just (E.TCon "Bool")   -> CC.bool'eq
                        Just (E.TCon "Nat")    -> CC.nat'eq
                        Just (E.TCon "Text")   -> CC.text'eq
                        Just (E.TCon "Symbol") -> CC.symbol'eq
                        Just (E.TCon "Party")  -> CC.party'eq
                        t -> error $ "lowerGatherPat: no comparison for " ++ show t

        -- Buila a term to do the comparison.
        let mPred' = fEq (C.MVar nBindFact CC.! nField) mTerm'

        return  (Nothing, Just mPred')


------------------------------------------------------------------------------------------- Term --
lowerTerm
        :: Show a
        => [(Name, C.Term a)]
        -> E.Term a
        -> S (C.Term a)

lowerTerm nmsMatch (E.MVar (Bound n))
 = case lookup n nmsMatch of
        Nothing -> pure $ C.MVar n
        Just m' -> pure m'

lowerTerm _nmsMatch (E.MParty n)
 =      return $ C.MParty n

lowerTerm nmsMatch (E.MKey E.MKApp [E.MGTerm mFun, E.MGTerms msArg])
 = do   mFun'   <- lowerTerm nmsMatch mFun
        msArg'  <- mapM (lowerTerm nmsMatch) msArg
        return  $  C.MApp mFun' msArg'

lowerTerm _ _
 = return C.MUnit
