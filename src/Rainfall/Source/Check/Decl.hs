
module Rainfall.Source.Check.Decl where
import Rainfall.Source.Check.Term
import Rainfall.Source.Check.Base
import qualified Data.Map               as Map


------------------------------------------------------------------------------------------- Decl --
-- | Check a list of top level declarations.
checkDecls :: Show a => [Decl a] -> IO [Decl a]
checkDecls ds
 = do   let facts   = Map.fromList [(nFact, ntsField) | DeclFact nFact ntsField <- ds]
        mapM (checkDecl facts) ds


-- | Check a single declaration.
checkDecl :: Show a => Facts a -> Decl a -> IO (Decl a)
checkDecl facts dd
 = case dd of
        DeclFact{}       -> return dd
        DeclRule rule    -> DeclRule     <$> checkRule facts rule
        DeclScenario scn -> DeclScenario <$> checkScenario facts scn


------------------------------------------------------------------------------------------- Rule --
-- | Check a source rule.
--   Type errors are thrown as exceptions in the IO monad.
checkRule :: Show a => Facts a -> Rule a -> IO (Rule a)
checkRule facts (Rule nRule hsMatch mBody)
 = do   -- Initial context.
        let ctx     = Context facts []

        -- Check all the matches, producing an output context with pattern bindings.
        (ctx', hsMatch') <- checkMatches ctx hsMatch

        -- Check the body in the new context.
        (mBody', _tBody')  <- checkTerm ctx' mBody

        -- TODO: check body type

        return (Rule nRule hsMatch' mBody')


------------------------------------------------------------------------------------------ Match --
-- | Check a sequence of matches,
--   where variables bound in earlier ones are in scope in later ones.
checkMatches :: Show a => Context a -> [Match a] -> IO (Context a, [Match a])
checkMatches ctx []
 = return (ctx, [])

checkMatches ctx (h: hs)
 = do   (ctx', h')   <- checkMatch   ctx  h
        (ctx'', hs') <- checkMatches ctx' hs
        return (ctx'', h' : hs')


-- | Check a single match clause.
checkMatch :: Show a => Context a -> Match a -> IO (Context a, Match a)
checkMatch ctx (MatchAnn a h)
 = do   (ctx', h') <- checkMatch ctx h
        return $ (ctx', MatchAnn a h')

checkMatch ctx (Match gather select consume gain)
 = do
        return (ctx, Match gather select consume gain)


----------------------------------------------------------------------------------------- Gather --
-- | Check a fact gather, adding pattern bound variables
checkGather :: Show a => Context a -> Gather a -> IO (Context a, Gather a)
checkGather ctx (GatherAnn a gg)
 = do   (ctx', gg') <- checkGather ctx gg
        return (ctx', GatherAnn a gg')

checkGather ctx (GatherPat nFact ngps mmPred)
 = do
        -- Lookup types of the fields of this fact.
        ntsFactPayload
         <- case Map.lookup nFact (contextFacts ctx) of
                Nothing  -> error "no fact"
                Just nts -> return nts

        -- Check the per-field pattern matches.
        (ctx', ngps')
         <- checkGatherFields ntsFactPayload ctx ngps

        -- Check the 'where' clause, if there is one.
        mmPred'
         <- case mmPred of
                Nothing -> return Nothing
                Just mPred
                 -> do  (mPred', _tPred) <- checkTerm ctx' mPred
                        -- TODO: check tPred is a bool
                        return $ Just mPred'

        return (ctx', GatherPat nFact ngps' mmPred')


-- | Check the fields of a gather pattern match.
--   Match variables bound in earlier fields are in scope in latter ones.
checkGatherFields
        :: Show a
        => [(Name, Type a)]     -- ^ Types of fields of the fact being matched.
        -> Context a -> [(Name, GatherPat a)]
        -> IO (Context a, [(Name, GatherPat a)])

checkGatherFields _ntsFactPayload ctx []
 =      return (ctx, [])

checkGatherFields ntsFactPayload ctx (ngp : ngps)
 = do   (ctx', ngp')   <- checkGatherField  ntsFactPayload ctx  ngp
        (ctx'', ngps') <- checkGatherFields ntsFactPayload ctx' ngps
        return  (ctx'', ngp' : ngps')


-- | Check a single field of a gather pattern match.
checkGatherField
        :: Show a
        => [(Name, Type a)]     -- ^ Types of fields of the fact being matched.
        -> Context a -> (Name, GatherPat a)
        -> IO (Context a, (Name, GatherPat a))

checkGatherField ntsFactPayload ctx (nField, gatherPat)
 = do
        tField
         <- case lookup nField ntsFactPayload of
                Nothing -> error $ "no field" ++ show nField
                Just t  -> return t

        (ctx', gatherPat')
         <- checkGatherPat tField ctx gatherPat

        return (ctx', (nField, gatherPat'))


-- | Check the pattern match of a single field.
checkGatherPat
        :: Show a
        => Type a               -- ^ Type of the current field of the fact.
        -> Context a -> GatherPat a
        -> IO (Context a, GatherPat a)

checkGatherPat tField ctx gp@(GatherPatBind n)
 = do   let ctx' = ctx { contextLocal = (n, tField) : contextLocal ctx }
        return (ctx', gp)

checkGatherPat _tField ctx (GatherPatEq mMatch)
 = do   (mMatch', _tMatch)
         <- checkTerm ctx mMatch

        -- TODO: compare
        return (ctx, GatherPatEq mMatch')


--------------------------------------------------------------------------------------- Scenario --
checkScenario
        :: Show a
        => Facts a -> Scenario a -> IO (Scenario a)
checkScenario _facts s@(Scenario _name _actions)
 = return s




