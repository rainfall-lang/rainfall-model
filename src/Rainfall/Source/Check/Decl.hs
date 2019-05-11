
module Rainfall.Source.Check.Decl where
import Rainfall.Source.Check.Term
import Rainfall.Source.Check.Base
import Rainfall.Source.Codec.Text.Pretty

import Control.Monad
import Text.PrettyPrint.Leijen  hiding ((<$>))
import qualified Data.Map       as Map


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
        DeclFact{}
         -> return dd

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

        -- Check all the matches, producing an output context
        -- containing any field binders.
        (ctx', hsMatch') <- checkMatches a ctx hsMatch

        -- Check the rule body in the new context.
        mBody' <- checkTermIs a (TSets TFACT) ctx' mBody

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
        select'  <- checkSelect  a ctx' select
        consume' <- checkConsume a ctx' consume
        gain'    <- checkGain    a ctx' gain
        return (ctx', Match gather' select' consume' gain')


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
                Nothing  -> nope a [text "unknown fact " <+> squotes (ppName nFact) ]
                Just nts -> return nts

        -- Check the per-field pattern matches.
        (ctx', ngps')
         <- checkGatherFields a nFact ntsFactPayload ctx ngps

        -- Check the 'where' clause, if there is one.
        mmPred'
         <- case mmPred of
                Nothing -> return Nothing
                Just mPred
                 -> do  (mPred', tPred) <- checkTerm a ctx' mPred

                        when (not $ checkEq tPred TBool) $ nope a
                         $ [ text "predicate expression"
                           , text " of type " <> squotes (ppType tPred)
                           , text " does not match expected type 'Bool'" ]

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
        -> [(Name, Type RL)]    -- ^ Types of fields of the fact being matched.
        -> Context RL ->   (Name, GatherPat RL)
        -> IO (Context RL, (Name, GatherPat RL))

checkGatherField a nFact ntsFactPayload ctx (nField, gatherPat)
 = do
        tField
         <- case lookup nField ntsFactPayload of
                Nothing -> nope a
                 [ text "Fact " <> squotes (ppName nFact)
                        <> text " does not have field "
                        <> squotes (ppName nField) <> text "."]
                Just t  -> return t

        (ctx', gatherPat')
         <- checkGatherPat a nField tField ctx gatherPat

        return (ctx', (nField, gatherPat'))


-- | Check the pattern match of a single field.
checkGatherPat
        :: RL                   -- ^ Annotation for error messages.
        -> Name                 -- ^ Name of the current field.
        -> Type RL              -- ^ Type of the current field of the fact.
        -> Context RL -> GatherPat RL
        -> IO (Context RL, GatherPat RL)

checkGatherPat _a _nField tField ctx gp@(GatherPatBind n)
 = do   let ctx' = ctx { contextLocal = (n, tField) : contextLocal ctx }
        return (ctx', gp)

checkGatherPat a nField tField ctx (GatherPatEq mMatch)
 = do   (mMatch', tMatch)
         <- checkTerm a ctx mMatch

        when (not $ checkEq tField tMatch) $ nope a
         $ [ text " in field "            <> squotes (ppName nField)
           , text " term of type "        <> squotes (ppType tMatch)
           , text " does not field type " <> squotes (ppType tField) ]

        return (ctx, GatherPatEq mMatch')


----------------------------------------------------------------------------------------- Select --
-- | Check a select clause.
checkSelect :: RL -> Context RL -> Select RL -> IO (Select RL)
checkSelect _a ctx (SelectAnn a select)
 = do   select' <- checkSelect a ctx select
        return $ SelectAnn a select'

checkSelect _a _ctx s@SelectAny
 = do   return s

checkSelect a ctx (SelectFirst mKey)
 = do   mKey'   <- checkTermIs a TNat ctx mKey
        return $ SelectFirst mKey'

checkSelect a ctx (SelectLast mKey)
 = do   mKey'   <- checkTermIs a TNat ctx mKey
        return $ SelectLast mKey'


---------------------------------------------------------------------------------------- Consume --
-- | Check a consume clause.
checkConsume :: RL -> Context RL -> Consume RL -> IO (Consume RL)
checkConsume _a ctx (ConsumeAnn a consume)
 = do   consume' <- checkConsume a ctx consume
        return $ ConsumeAnn a consume'

checkConsume _a _ctx c@ConsumeNone
 = do   return c

checkConsume a ctx (ConsumeWeight mWeight)
 = do   mWeight' <- checkTermIs a TNat ctx mWeight
        return  $ ConsumeWeight mWeight'


------------------------------------------------------------------------------------------- Gain --
checkGain :: RL -> Context RL -> Gain RL -> IO (Gain RL)
checkGain _a ctx (GainAnn a gain)
 = do   gain' <- checkGain a ctx gain
        return $ GainAnn a gain'

checkGain _a _ctx gg@GainNone
 = do   return gg

checkGain a ctx (GainCheck mParties)
 = do   mParties' <- checkTermIs a (TSet TParty) ctx mParties
        return $ GainCheck mParties'

checkGain a ctx (GainTerm mParties)
 = do   mParties' <- checkTermIs a (TSet TParty) ctx mParties
        return $ GainTerm mParties'


--------------------------------------------------------------------------------------- Scenario --
checkScenario
        :: Show a
        => Facts a -> Scenario a -> IO (Scenario a)
checkScenario _facts s@(Scenario _name _actions)
 = return s




