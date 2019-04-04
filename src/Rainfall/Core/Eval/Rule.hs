
module Rainfall.Core.Eval.Rule where
import Rainfall.Core.Eval.Store
import Rainfall.Core.Eval.Term
import Rainfall.Core.Exp

import qualified Data.List              as List
import qualified Data.List.Extra        as List
import qualified Data.Map               as Map
import qualified Data.Set               as Set
import Data.Map                         (Map)
import Data.Maybe

---------------------------------------------------------------------------------------------------
data Result a b
        = Fire b
        | Fizz (Fizz a)
        deriving Show

data Fizz a
        = FizzGatherNone
        { fizzGather    :: Gather a
        , fizzStore     :: Store }

        | FizzSelectNone
        { fizzSelect    :: Select a
        , fizzFactoids  :: [Factoid ()] }

        | FizzConsumeFail
        { fizzRule      :: Name
        , fizzAuth      :: Auth
        , fizzStore     :: Store
        , fizzFact      :: Fact a
        , fizzWeight    :: Weight
        , fizzEnv       :: Env a
        , fizzConsume   :: Consume a }
        deriving Show

data Trans a
        = Trans
        { transRule     :: Name
        , transSpent    :: [Factoid ()]
        , transCreated  :: [Factoid ()] }
        deriving Show

---------------------------------------------------------------------------------------------------
-- TODO: need to handle non-determinism in the selection,
-- if there are multiple possibilities for the 'any' selection.

---------------------------------------------------------------------------------------------------
-- | Try to fire a rule applied to a store.
applyRuleToStore
        :: Rule ()              -- ^ Rule to apply.
        -> Auth                 -- ^ Authority of submitter.
        -> Store                -- ^ Initial store.
        -> Result () ([Factoid ()], [Factoid ()], Store)

applyRuleToStore rule aSub store0
 = goMatch [] [] store0 [] (ruleMatch rule)
 where
        -- Match patterns against facts in the store,
        --   building up our delegated authority, list of spent factoids,
        --   and the term environment.
        goMatch aHas fwsSpent store env (match : matches)
         = case matchFromStore (ruleName rule) aSub aHas store env match of
                -- The current pattern didn't match, so the whole rule fizzes.
                Fizz fizz -> Fizz fizz

                -- The current pattern matched, so continue on to the next one.
                Fire (aHas', fwSpent, store', env')
                 -> goMatch aHas' (fwSpent : fwsSpent) store' env' matches

        -- We have satisfied all the patterns,
        -- so now execute the body of the rule.
        goMatch aHas fwsSpent store env []
         = case execTerm env (ruleBody rule) of
                (VUnit, fwsNew)
                 -> goCommit aHas fwsSpent fwsNew store

        goCommit aHas fwsSpent fwsNew store
         -- Unack the new factoids and check the authority delegated to the
         -- rule covers the authority of all new factoids.
         | all (authCoversFact aHas) $ map fst fwsNew
         = let  store'  = Map.unionWith (+) (Map.fromList fwsNew) store
           in   Fire (fwsSpent, fwsNew, storePrune $ store')


---------------------------------------------------------------------------------------------------
-- | Match rule against facts in the store.
matchFromStore
        :: Name                 -- ^ Name of the current rule.
        -> Auth                 -- ^ Authority of submitter.
        -> Auth                 -- ^ Initial authority of rule.
        -> Store                -- ^ Initial store.
        -> Env ()               -- ^ Initial environment.
        -> Match ()
        -> Result () (Auth, Factoid (), Store, Env ())

matchFromStore nRule aSub aHas store env (MatchAnn a match)
 = matchFromStore nRule aSub aHas store env match

matchFromStore nRule aSub aHas store env (Match rake gain)
 = case rakeFromStore nRule aSub aHas store env rake of
        Fire (fwSpent@(fact :* _weight), store', env')
         -> let aHas' = gainFromFact aHas fact env' gain
            in  Fire (aHas', fwSpent, store', env')

        Fizz fizz -> Fizz fizz


---------------------------------------------------------------------------------------------------
-- | Rake facts from the store,
rakeFromStore
        :: Name                 -- ^ Name of the current rule.
        -> Auth                 -- ^ Authority of the submitter.
        -> Auth                 -- ^ Authority of the rule performing the rake.
        -> Store                -- ^ Store to rake facts from.
        -> Env ()               -- ^ Current environment.
        -> Rake ()              -- ^ Rake to perform.
        -> Result () (Factoid (), Store, Env ())

rakeFromStore nRule aSub aHas store env (Rake bFact gather select consume)
 = goGather
 where
        -- Gather initial facts that match the predicates.
        goGather
         = case gatherFromStore aSub store env bFact gather of
                []              -> Fizz (FizzGatherNone gather store)
                fws             -> goSelect fws

        -- Select a subset of facts to consider.
        goSelect fws
         = case selectFromFacts fws env bFact select of
                Nothing         -> Fizz (FizzSelectNone select fws)
                Just fw         -> goConsume fw

        -- Consume the selected facts from the store.
        goConsume fw@(fact, weight)
         | elem nRule (factRules fact)
         , env'         <- envBind bFact (VFact fact) env
         , Just store'  <- consumeFromStore fact store env' consume
         = Fire (fw, store', env')

         | otherwise
         = Fizz (FizzConsumeFail nRule aHas store fact weight env consume)


---------------------------------------------------------------------------------------------------
-- | Gather visible facts from the store that match the gather predicates,
--   returning all matching facts and the available weight of each one.
gatherFromStore
        :: Auth                 -- ^ Authority of the submitter.
        -> Store                -- ^ Store to gather facts from.
        -> Env ()               -- ^ Current environment, used in gather predicates.
        -> Bind                 -- ^ Binder for the fact value in the gather predicate.
        -> Gather ()            -- ^ The gather predicates.
        -> [Factoid ()]

gatherFromStore aSub store env bFact (GatherAnn _a gg)
 = gatherFromStore aSub store env bFact gg

gatherFromStore aSub store env bFact (GatherWhen nFact msPred)
 = [ fw | fw@(fact, weight)   <- Map.toList store
        , factName fact == nFact
        , canSeeFact aSub fact
        , let env' = envBind bFact (VFact fact) env
          in  all (isVTrue . evalTerm env') msPred ]


---------------------------------------------------------------------------------------------------
selectFromFacts
        :: [Factoid ()]         -- ^ Gathered facts to select from.
        -> Env ()               -- ^ Current environment.
        -> Bind                 -- ^ Fact binder within the rake.
        -> Select ()            -- ^ Selection specifier.
        -> Maybe (Factoid ())

selectFromFacts fws env bFact (SelectAnn a select)
 = selectFromFacts fws env bFact select

selectFromFacts fws _env _bFact SelectAny
 = case fws of
        fw : _  -> Just fw
        _       -> Nothing

selectFromFacts fws env bFact (SelectFirst mKey)
 = let  kfws = [ ( evalTerm (envBind bFact (VFact fact) env) mKey
                 , fact :* weight)
               | fact :* weight <- fws ]

   in   case List.sortOn fst kfws of
         (k, fw) : _ -> Just fw
         _           -> Nothing

selectFromFacts fws env bFact (SelectLast mKey)
 = let  kfws = [ ( evalTerm (envBind bFact (VFact fact) env) mKey
                 , fact :* weight)
               | fact :* weight <- fws ]

   in   case reverse $ List.sortOn fst kfws of
         (k, fw) : _ -> Just fw
         _           -> Nothing


---------------------------------------------------------------------------------------------------
-- | Try to consume the given weight of a fact from the store,
--   returning a new store if possible.
--
--   The fact
--
consumeFromStore
        :: Fact ()              -- ^ Fact to consume.
        -> Store                -- ^ Initial store.
        -> Env ()               -- ^ Current environment.
        -> Consume ()           -- ^ Consume specifier.
        -> Maybe Store

consumeFromStore fact store env (ConsumeAnn _ consume)
 = consumeFromStore fact store env consume

consumeFromStore _fact store _env ConsumeRetain
 = Just store

consumeFromStore fact store env (ConsumeWeight mWeight)
 | nWeightWant
     <- case evalTerm env mWeight of
         VNat n  -> n
         _       -> error "consumeFromStore: weight is not a Nat value"
 , nWeightAvail
     <- fromMaybe 0 $ Map.lookup fact store
 , nWeightAvail >= nWeightWant
 = Just $ Map.insert fact (nWeightAvail - nWeightWant) store

 | otherwise    = Nothing


---------------------------------------------------------------------------------------------------
-- | Gain delegated authority from a given fact.
gainFromFact
        :: Auth                 -- ^ Current authority.
        -> Fact ()              -- ^ Fact to acquire authority from.
        -> Env ()               -- ^ Current environment.
        -> Gain ()              -- ^ Gain specification.
        -> Auth                 -- ^ Resulting authority, including what we started with.

gainFromFact aHas fact env (GainAnn a acquire)
 = gainFromFact aHas fact env acquire

gainFromFact aHas fact env GainNone
 = aHas

gainFromFact aHas fact env (GainTerm mAuth)
 = case evalTerm env mAuth of
        VAuth aFact
          |  Set.isSubsetOf (Set.fromList aFact) (Set.fromList $ factBy fact)
          -> List.nubOrd (aHas ++ aFact)

          |  otherwise -> error $ "gainFromFact: invalid delegation"

        v -> error $ unlines
                [ "gainFromFact: auth term is ill-typed"
                , "  value = " ++ show v ]
