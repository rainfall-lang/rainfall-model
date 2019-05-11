
module Rainfall.Source.Check.Decl where
import Rainfall.Source.Check.Term
import Rainfall.Source.Check.Base
import qualified Data.Map                               as Map


sname n = "'" ++ takeName n ++ "'"


------------------------------------------------------------------------------------------- Decl --
-- | Check a list of top level declarations.
checkDecls :: [Decl RL] -> IO [Decl RL]
checkDecls ds
 = do   let facts   = Map.fromList [(nFact, ntsField) | DeclFact nFact ntsField <- ds]
        mapM (checkDecl facts) ds


-- | Check a single declaration.
checkDecl :: Facts RL -> Decl RL -> IO (Decl RL)
checkDecl facts dd
 = case dd of
        DeclFact{}       -> return dd

        DeclRule a rule
         -> DeclRule a     <$> checkRule a facts rule

        DeclScenario a scn
         -> DeclScenario a <$> checkScenario facts scn


------------------------------------------------------------------------------------------- Rule --
-- | Check a source rule.
--   Type errors are thrown as exceptions in the IO monad.
checkRule :: RL -> Facts RL -> Rule RL -> IO (Rule RL)
checkRule a facts (Rule nRule hsMatch mBody)
 = do   -- Initial context.
        let ctx     = Context facts []

        -- Check all the matches, producing an output context with pattern bindings.
        (ctx', hsMatch')   <- checkMatches a ctx hsMatch

        -- Check the body in the new context.
        (mBody', _tBody')  <- checkTerm ctx' mBody

        -- TODO: check body type

        return (Rule nRule hsMatch' mBody')


------------------------------------------------------------------------------------------ Match --
-- | Check a sequence of matches,
--   where variables bound in earlier ones are in scope in later ones.
checkMatches
        :: RL -> Context RL
        -> [Match RL] -> IO (Context RL, [Match RL])
checkMatches _a ctx []
 = return (ctx, [])

checkMatches a ctx (h: hs)
 = do   (ctx', h')   <- checkMatch   a ctx  h
        (ctx'', hs') <- checkMatches a ctx' hs
        return (ctx'', h' : hs')


-- | Check a single match clause.
checkMatch
        :: RL -> Context RL
        -> Match RL -> IO (Context RL, Match RL)

checkMatch _a ctx (MatchAnn a h)
 = do   (ctx', h') <- checkMatch a ctx h
        return $ (ctx', MatchAnn a h')

checkMatch a ctx (Match gather select consume gain)
 = do
        (ctx', gather') <- checkGather a ctx gather
        -- TODO: check select
        -- TODO: check consume
        -- TODO: check gain

        return (ctx', Match gather' select consume gain)


----------------------------------------------------------------------------------------- Gather --
-- | Check a fact gather, adding pattern bound variables
checkGather
        :: RL -> Context RL
        -> Gather RL -> IO (Context RL, Gather RL)

checkGather _a ctx (GatherAnn a gg)
 = do   (ctx', gg') <- checkGather a ctx gg
        return (ctx', GatherAnn a gg')

checkGather a ctx (GatherPat nFact ngps mmPred)
 = do
        -- Lookup types of the fields of this fact.
        ntsFactPayload
         <- case Map.lookup nFact (contextFacts ctx) of
                Nothing  -> error "no fact"
                Just nts -> return nts

        -- Check the per-field pattern matches.
        (ctx', ngps')
         <- checkGatherFields a nFact ntsFactPayload ctx ngps

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
        :: RL                   -- ^ Annotation for error messages.
        -> Name                 -- ^ Name of matched fact.
        -> [(Name, Type RL)]    -- ^ Types of fields of the fact being matched.
        -> Context RL -> [(Name, GatherPat RL)]
        -> IO (Context RL, [(Name, GatherPat RL)])

checkGatherFields _a _nFact _ntsFactPayload ctx []
 =      return (ctx, [])

checkGatherFields a nFact ntsFactPayload ctx (ngp : ngps)
 = do   (ctx', ngp')   <- checkGatherField  a nFact ntsFactPayload ctx  ngp
        (ctx'', ngps') <- checkGatherFields a nFact ntsFactPayload ctx' ngps
        return  (ctx'', ngp' : ngps')


-- | Check a single field of a gather pattern match.
checkGatherField
        :: RL                   -- ^ Annotation for error messages.
        -> Name                 -- ^ Name of matched fact.
        -> [(Name, Type RL)]     -- ^ Types of fields of the fact being matched.
        -> Context RL ->   (Name, GatherPat RL)
        -> IO (Context RL, (Name, GatherPat RL))

checkGatherField a nFact ntsFactPayload ctx (nField, gatherPat)
 = do
        tField
         <- case lookup nField ntsFactPayload of
                Nothing -> nope a [ "Fact " ++ sname nFact
                                            ++ " does not have field " ++ sname nField ++ "."]
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




