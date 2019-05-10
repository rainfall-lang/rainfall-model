
module Rainfall.Core.Eval.Rule where
import Rainfall.Core.Eval.Store
import Rainfall.Core.Eval.Term
import Rainfall.Core.Exp

import qualified Data.List              as List
import qualified Data.Map               as Map
import qualified Data.Set               as Set
import Data.Maybe
import Control.Monad


---------------------------------------------------------------------------------------------------
data Transaction
        = Transaction
        { transactionRule       :: Name
        , transactionSpent      :: Factoids
        , transactionNew        :: Factoids }
        deriving Show


---------------------------------------------------------------------------------------------------
-- | Try to fire a rule applied to a store.
applyFire
        :: Show a
        => Auth         -- ^ Authority of submitter.
        -> Store        -- ^ Initial store.
        -> Rule a       -- ^ Rule to apply.
        -> [(Transaction, Store)]

applyFire aSub store rule
 = do
        (aHas, dsSpend, store', env')
         <- applyMatches (ruleName rule) aSub Set.empty
                Map.empty store (Env []) (ruleMatch rule)

        let Just dsNew
                = takeFactoidsOfValue
                $ evalTerm env' (ruleBody rule)

        guard $ all (authCoversFact aHas) $ Map.keys dsNew

        let trans   = Transaction (ruleName rule) dsSpend dsNew
        let store'' = storePrune $ Map.unionWith (+) dsNew store'

        return  (trans, store'')


---------------------------------------------------------------------------------------------------
-- | Match multiple patterns against the store,
--   trying to satisfy them one after another.
applyMatches
        :: Show a
        => Name         -- ^ Name of the current rule.
        -> Auth         -- ^ Authority of the submitter.
        -> Auth         -- ^ Current authority of the rule.
        -> Factoids     -- ^ Factoids spent so far.
        -> Store        -- ^ Initial store.
        -> Env          -- ^ Initial environment.
        -> [Match a]    -- ^ Matches to apply.
        -> [(Auth, Factoids, Store, Env)]

applyMatches _name _aSub aHas dSpent store env []
 =      return (aHas, dSpent, store, env)

applyMatches name aSub aHas dSpent store env (match : matches)
 = do
        (aGain, dSpent', store', env')
         <- applyMatch name aSub store env match

        let aHas'       = Set.union aHas aGain
        let dSpent''    = Map.unionWith (+) dSpent dSpent'

        applyMatches name aSub aHas' dSpent'' store' env' matches


---------------------------------------------------------------------------------------------------
-- | Match a single pattern against the store.
--
--   This rule is non-deterministic through the use of 'selectFromFacts',
--   and returns all available options.
--
applyMatch
        :: Show a
        => Name         -- ^ Name of the current rule.
        -> Auth         -- ^ Authority of submitter.
        -> Store        -- ^ Initial store.
        -> Env          -- ^ Initial environment.
        -> Match a
        -> [(Auth, Factoids, Store, Env)]

applyMatch nRule aSub store env (MatchAnn _a match)
 = applyMatch nRule aSub store env match

applyMatch nRule aSub store env (Match bFact gather select consume gain)
 = do
        -- Gather facts that match the patterns.
        fsGather <- applyGather aSub store env bFact gather

        -- Select a single fact from the gathered set.
        fSelect  <- applySelect fsGather env bFact select

        -- The fact must have the current rule in its whitelist.

        -- Consume the required quantify of the fact,
        -- computing the weight with the new fact in scope.
        let env' = envBind bFact (VFact fSelect) env
        (weight', store') <- applyConsume nRule fSelect store env' consume
        let dSpent      = Map.singleton fSelect weight'

        -- Gain authority from the matched fact.
        aGain    <- applyGain nRule fSelect env' gain

        return  (aGain, dSpent, store', env')


---------------------------------------------------------------------------------------------------
-- | Gather visible facts from the store that match the gather predicates,
--   returning all matching facts and the available weight of each one.
applyGather
        :: Show a
        => Auth         -- ^ Authority of the submitter.
        -> Store        -- ^ Store to gather facts from.
        -> Env          -- ^ Current environment, used in gather predicates.
        -> Bind         -- ^ Binder for the fact value in the gather predicate.
        -> Gather a     -- ^ The gather predicates.
        -> [[Fact]]

applyGather aSub store env bFact (GatherAnn _a gg)
 = applyGather aSub store env bFact gg

applyGather aSub store env bFact (GatherWhere nFact msPred)
 = let fs = [ fact | (fact, weight) <- Map.toList store
                   , weight >= 0
                   , factName fact == nFact
                   , canSeeFact aSub fact
                   , let env' = envBind bFact (VFact fact) env
                     in  all (isVTrue . evalTerm env') msPred ]
   in [fs]


---------------------------------------------------------------------------------------------------
-- | Select a single fact from the given list, according to the selection specifier.
--
--   This rule is non-deterministic due to the 'any' case.
--
applySelect
        :: Show a
        => [Fact]       -- ^ Gathered facts to select from.
        -> Env          -- ^ Current environment.
        -> Bind         -- ^ Fact binder within the rake.
        -> Select a     -- ^ Selection specifier.
        -> [Fact]

applySelect fs env bFact (SelectAnn _a select)
 = applySelect fs env bFact select

applySelect fs _env _bFact SelectAny
 = fs

applySelect fs env bFact (SelectFirst mKey)
 = let  kfs =   [ (evalTerm (envBind bFact (VFact fact) env) mKey, fact)
                | fact <- fs ]

   in   case List.sortOn fst kfs of
         (_k, f) : _    -> [f]
         _              -> []

applySelect fs env bFact (SelectLast mKey)
 = let  kfs =   [ (evalTerm (envBind bFact (VFact fact) env) mKey, fact)
                | fact <- fs ]

   in   case reverse $ List.sortOn fst kfs of
         (_k, f) : _    -> [f]
         _              -> []


---------------------------------------------------------------------------------------------------
-- | Try to consume the given weight of a fact from the store,
--   returning a new store if possible.
applyConsume
        :: Show a
        => Name         -- ^ Name of enclosing rule.
        -> Fact         -- ^ Fact to consume.
        -> Store        -- ^ Initial store.
        -> Env          -- ^ Current environment.
        -> Consume a    -- ^ Consume specifier.
        -> [(Weight, Store)]

applyConsume nRule fact store env (ConsumeAnn _ consume)
 = applyConsume nRule fact store env consume

applyConsume _nRule _fact store _env ConsumeNone
 = [(0, store)]

applyConsume nRule fact store env (ConsumeWeight mWeight)
 = do   let VNat nWeightWant = evalTerm env mWeight
        let nWeightAvail     = fromMaybe 0 $ Map.lookup fact store

        guard  $ nWeightAvail >= nWeightWant
        -- TODO: check fact weight in top level rule.

        guard   $ elem nRule (factUse fact)

        return $ (nWeightWant, Map.insert fact (nWeightAvail - nWeightWant) store)


---------------------------------------------------------------------------------------------------
-- | Gain delegated authority from a given fact.
applyGain
        :: Show a
        => Name         -- ^ Name of enclosing rule.
        -> Fact         -- ^ Fact to acquire authority from.
        -> Env          -- ^ Current environment.
        -> Gain a       -- ^ Gain specification.
        -> [Auth]       -- ^ Resulting authority, including what we started with.

applyGain nRule fact env (GainAnn _a acquire)
 = applyGain nRule fact env acquire

applyGain _nRule _fact _env GainNone
 = [Set.empty]

applyGain _nRule fact env (GainCheck mAuth)
 = do   let Just nsGain = takeAuthOfValue $ evalTerm env mAuth
        guard $ Set.isSubsetOf nsGain (factBy fact)
        return Set.empty

applyGain nRule fact env (GainTerm mAuth)
 = do   let Just nsGain = takeAuthOfValue $ evalTerm env mAuth
        guard $ elem nRule (factUse fact)
        guard $ Set.isSubsetOf nsGain (factBy fact)
        return nsGain