
module Rainfall.Core.Eval.Rule where
import Rainfall.Core.Eval.Term
import Rainfall.Core.Exp

import qualified Data.List              as List
import qualified Data.List.Extra        as List
import qualified Data.Map               as Map
import qualified Data.Set               as Set
import Data.Map                         (Map)
import Data.Maybe

---------------------------------------------------------------------------------------------------
type Weight = Integer
type Store  = Map (Fact ()) Weight


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
        , fizzStore     :: Store }

        | FizzConsumeFail
        { fizzRule      :: Name
        , fizzAuth      :: Auth
        , fizzStore     :: Store
        , fizzFact      :: Fact a
        , fizzWeight    :: Weight
        , fizzEnv       :: Env a
        , fizzConsume   :: Consume a }
        deriving Show


---------------------------------------------------------------------------------------------------
-- | Try to fire a rule applied to a store.
applyRuleToStore
        :: Rule ()              -- ^ Rule to apply.
        -> Auth                 -- ^ Initial authority.
        -> Store                -- ^ Initial store.
        -> Result () (Auth, [(Fact (), Weight)], Store, Env ())

applyRuleToStore rule aHas0 store0
 = goMatch aHas0 [] store0 [] (ruleMatch rule)
 where
        goMatch aHas fwsSpent store env (match : matches)
         = case matchFromStore (ruleName rule) aHas store env match of
                Fizz fizz -> Fizz fizz

                Fire (aHas', fwSpent, store', env')
                 -> goMatch aHas' (fwSpent : fwsSpent) store' env' matches

        -- TODO: need to evaluate the body to get the new facts.
        goMatch aHas fwsSpent store env []
         = Fire (aHas, fwsSpent, store, env)


---------------------------------------------------------------------------------------------------
-- | Match rule against facts in the store.
matchFromStore
        :: Name                 -- ^ Name of the current rule.
        -> Auth                 -- ^ Initial authority.
        -> Store                -- ^ Initial store.
        -> Env ()               -- ^ Initial environment.
        -> Match ()
        -> Result () (Auth, (Fact (), Weight), Store, Env ())

matchFromStore nRule aHas store env (MatchAnn a match)
 = matchFromStore nRule aHas store env match

matchFromStore nRule aHas store env (Match rake acquire)
 = goRake
 where
        goRake
         = case rakeFromStore nRule aHas store env rake of
                Fire (fwSpent@(fact, _weight), store', env')
                 -> let aHas' = acquireFromFact aHas fact env' acquire
                    in  Fire (aHas', fwSpent, store', env')

                Fizz fizz -> Fizz fizz


---------------------------------------------------------------------------------------------------
-- | Rake facts from the store,
rakeFromStore
        :: Name                 -- ^ Name of the current rule.
        -> Auth                 -- ^ Authority of the rule performing the rake.
        -> Store                -- ^ Store to rake facts from.
        -> Env ()               -- ^ Current environment.
        -> Rake ()              -- ^ Rake to perform.
        -> Result () ((Fact (), Weight), Store, Env ())

rakeFromStore nRule aHas store env (Rake bFact gather select consume)
 = goGather
 where
        -- Gather initial facts that match the predicates.
        goGather
         = let  fws     = gatherFromStore aHas store env bFact gather
           in   if null fws
                 then Fizz (FizzGatherNone gather store)
                 else goSelect fws

        -- Select a subset of facts to consider.
        goSelect fws
         = case selectFromFacts fws env bFact select of
                Nothing         -> Fizz (FizzSelectNone select (Map.fromList fws))
                Just fw         -> goConsume fw

        -- Consume the selected facts from the store.
        goConsume (fact, weight)
         = let  env' = envBind bFact (VFact fact) env
           in   case consumeFromStore nRule aHas store fact weight env' consume of
                 Nothing        -> Fizz (FizzConsumeFail nRule aHas store fact weight env' consume)
                 Just store'    -> Fire ((fact, weight), store', env')


---------------------------------------------------------------------------------------------------
-- | Gather visible facts from the store that match the gather predicates,
--   returning all matching facts and the available weight of each one.
gatherFromStore
        :: Auth                 -- ^ Authority of the rule performing the gather.
        -> Store                -- ^ Store to gather facts from.
        -> Env ()               -- ^ Current environment, used in gather predicates.
        -> Bind                 -- ^ Binder for the fact value in the gather predicate.
        -> Gather ()            -- ^ The gather predicates.
        -> [(Fact (), Weight)]

gatherFromStore aHas store env bFact (GatherAnn _a gg)
 = gatherFromStore aHas store env bFact gg

gatherFromStore aHas store env bFact (GatherWhen nFact msPred)
 = [ (fact, weight)
        | (fact, weight)   <- Map.toList store
        , factName fact == nFact        -- Fact has the name that we want.
        , canSeeFact aHas fact || True
                -- Fact is visible with the current authority.
                -- TODO: hardwired True until get private store working.
        , let env' = envBind bFact (VFact fact) env
          in  all (isVTrue . evalTerm env') msPred ]


---------------------------------------------------------------------------------------------------
-- TODO: To model a concurrent system, select a fact pseudo randomly in the 'any' mode.
selectFromFacts
        :: [(Fact (), Weight)]  -- ^ Gathered facts to select from.
        -> Env ()               -- ^ Current environment.
        -> Bind                 -- ^ Fact binder within the rake.
        -> Select ()            -- ^ Selection specifier.
        -> Maybe (Fact (), Weight)

selectFromFacts fws env bFact (SelectAnn a select)
 = selectFromFacts fws env bFact select

selectFromFacts fws _env _bFact SelectOne
 = case fws of
        [fw]    -> Just fw
        _       -> Nothing

selectFromFacts fws _env _bFact SelectAny
 = case fws of
        fw : _  -> Just fw
        _       -> Nothing

selectFromFacts fws env bFact (SelectFirst mKey)
 = let  kfws = [ ( evalTerm (envBind bFact (VFact fact) env) mKey
               , (fact, weight))
               | (fact, weight) <- fws ]

   in   case List.sortOn fst kfws of
         (k, fw) : _ -> Just fw
         _           -> Nothing

selectFromFacts fws env bFact (SelectLast mKey)
 = let  kfws = [ ( evalTerm (envBind bFact (VFact fact) env) mKey
               , (fact, weight))
               | (fact, weight) <- fws ]

   in   case reverse $ List.sortOn fst kfws of
         (k, fw) : _ -> Just fw
         _           -> Nothing


---------------------------------------------------------------------------------------------------
-- | Try to consume the given weight of a fact from the store.
consumeFromStore
        :: Name                 -- ^ Name of the current rule.
        -> Auth                 -- ^ Authority of the rule.
        -> Store                -- ^ Initial store.
        -> Fact ()              -- ^ Fact to consume.
        -> Weight               -- ^ Weight of the fact to consume.
        -> Env ()               -- ^ Current environment.
        -> Consume ()           -- ^ Consume specifier.
        -> Maybe Store

consumeFromStore  nRule aHas store fact weight env (ConsumeAnn _ consume)
 = consumeFromStore nRule aHas store fact weight env consume

consumeFromStore _nRule _aHas store _fact _weight _env ConsumeRetain
 = Just store

consumeFromStore  nRule  aHas store fact weight env (ConsumeWeight mWeight)
 | elem nRule (factRules fact)
 , nWeightWant
     <- case evalTerm env mWeight of
         VNat n  -> n
         _       -> error "consumeFromStore: weight is not a Nat value"
 , nWeightAvail
     <- fromMaybe 0 $ Map.lookup fact store
 , nWeightAvail >= nWeightWant
 = Just $ Map.insert fact (nWeightAvail - nWeightWant) store

 | otherwise    = Nothing


---------------------------------------------------------------------------------------------------
-- | Aquire delegated authority from a given fact.
acquireFromFact
        :: Auth                 -- ^ Current authority.
        -> Fact ()              -- ^ Fact to acquire authority from.
        -> Env ()               -- ^ Current environment.
        -> Acquire ()           -- ^ Acquire specification.
        -> Auth                 -- ^ Resulting authority, including what we started with.

acquireFromFact aHas fact env (AcquireAnn a acquire)
 = acquireFromFact aHas fact env acquire

acquireFromFact aHas fact env AcquireSame
 = aHas

acquireFromFact aHas fact env (AcquireTerm mAuth)
 = case evalTerm env mAuth of
        VAuth aFact
          |  Set.isSubsetOf (Set.fromList aFact) (Set.fromList $ factBy fact)
          -> List.nubOrd (aHas ++ aFact)

          |  otherwise -> error $ "acquireFromFact: invalid delegation"

        v -> error $ unlines
                [ "acquireFromFact: auth term is ill-typed"
                , "  value = " ++ show v ]
