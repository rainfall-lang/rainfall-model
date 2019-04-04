
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
        , fizzEnv       :: Env a
        , fizzConsume   :: Consume a }
        deriving Show

data Trans a
        = Trans
        { transRule     :: Name
        , transSpent    :: [Factoid ()]
        , transCreated  :: [Factoid ()] }
        deriving Show

data Firing
        = Firing
        { firingName    :: Name
        , firingSpent   :: [Factoid ()]
        , firingNew     :: [Factoid ()]
        , firingStore   :: Store }
        deriving Show


---------------------------------------------------------------------------------------------------
-- | Try to fire a rule applied to a store.
applyRuleToStore
        :: Rule ()              -- ^ Rule to apply.
        -> Auth                 -- ^ Authority of submitter.
        -> Store                -- ^ Initial store.
        -> [Result () Firing]

applyRuleToStore rule aSub store0
 = goMatch [] [] store0 [] (ruleMatch rule)
 where
        -- Match patterns against facts in the store,
        --   building up our delegated authority, list of spent factoids,
        --   and the term environment.
        goMatch :: Auth
                -> [Factoid ()]
                -> Store
                -> Env ()
                -> [Match ()]
                -> [Result () Firing]

        goMatch aHas fwsSpent store env (match : matches)
         = case matchFromStore (ruleName rule) aSub aHas store env match of
                -- The current pattern didn't match, so the whole rule fizzes.
                Fizz fizz -> [Fizz fizz]

                -- The current pattern matched, so continue on to the next one.
                --
                --  This map handles non-determinism in the evaluation rules as we
                --  compare all the ways the current pattern can match
                --  with all the ways the rest of the rules can match.
                Fire opts
                 -> concat [ goMatch aHas' (fwSpent' : fwsSpent) store' env' matches
                           | (aHas', fwSpent', store', env') <- opts ]


        -- We have satisfied all the patterns, so now execute the body of the rule.
        -- Unack the new factoids and check the authority delegated to the
        -- rule covers the authority of all new factoids.
        goMatch aHas fwsSpent store env []
         | fwsNew <- case execTerm env (ruleBody rule) of
                       (VUnit, fwsNew) -> fwsNew
                       _               -> error "result of say is ill-typed"
         , all (authCoversFact aHas) $ map fst fwsNew
         = let  store'  = Map.unionWith (+) (Map.fromList fwsNew) store
           in   [Fire $ Firing (ruleName rule) fwsSpent fwsNew (storePrune $ store')]

         | otherwise
         = []


---------------------------------------------------------------------------------------------------
-- | Match rule against facts in the store.
matchFromStore
        :: Name                 -- ^ Name of the current rule.
        -> Auth                 -- ^ Authority of submitter.
        -> Auth                 -- ^ Initial authority of rule.
        -> Store                -- ^ Initial store.
        -> Env ()               -- ^ Initial environment.
        -> Match ()
        -> Result () [(Auth, Factoid (), Store, Env ())]

matchFromStore nRule aSub aHas store env (MatchAnn a match)
 = matchFromStore nRule aSub aHas store env match

matchFromStore nRule aSub aHas store env (Match rake gain)
 = goRake
 where
        goRake
         = case rakeFromStore nRule aSub aHas store env rake of
                Fizz fizz       -> Fizz fizz
                Fire opts       -> case mapMaybe goGain opts of
                                        []      -> error "fizz"
                                        result  -> Fire result

        goGain (fwSpent@(fact :* _weight), store', env')
         = case gainFromFact aHas fact env' gain of
                Just aHas'      -> Just (aHas', fwSpent, store', env')
                Nothing         -> Nothing


---------------------------------------------------------------------------------------------------
-- | Apply a rake to the store, producing the possible matches.
rakeFromStore
        :: Name                 -- ^ Name of the current rule.
        -> Auth                 -- ^ Authority of the submitter.
        -> Auth                 -- ^ Authority of the rule performing the rake.
        -> Store                -- ^ Store to rake facts from.
        -> Env ()               -- ^ Current environment.
        -> Rake ()              -- ^ Rake to perform.
        -> Result () [(Factoid (), Store, Env ())]

rakeFromStore nRule aSub aHas store env (Rake bFact gather select consume)
 = goGather
 where
        -- Gather initial facts that match the predicates.
        goGather
         = case gatherFromStore aSub store env bFact gather of
                []      -> Fizz (FizzGatherNone gather store)
                fws     -> goSelect fws

        -- Select a subset of facts to consider.
        goSelect fws
         = case selectFromFacts fws env bFact select of
                []      -> Fizz (FizzSelectNone select fws)
                fws     -> case mapMaybe goConsume fws of
                                []      -> Fizz (FizzConsumeFail nRule aHas store env consume)
                                result  -> Fire result

        -- Consume the weight of the selected fact from the store.
        goConsume fw@(fact, weight)
         | elem nRule (factRules fact)
         , env'         <- envBind bFact (VFact fact) env
         , Just store'  <- consumeFromStore fact store env' consume
         = Just (fw, store', env')

         | otherwise
         = Nothing


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
-- | Select a single fact from the given list,
--   according to the selection specifier,
--   returning all the available options.
selectFromFacts
        :: [Factoid ()]         -- ^ Gathered facts to select from.
        -> Env ()               -- ^ Current environment.
        -> Bind                 -- ^ Fact binder within the rake.
        -> Select ()            -- ^ Selection specifier.
        -> [Factoid ()]

selectFromFacts fws env bFact (SelectAnn a select)
 = selectFromFacts fws env bFact select

selectFromFacts fws _env _bFact SelectAny
 = fws

selectFromFacts fws env bFact (SelectFirst mKey)
 = let  kfws = [ ( evalTerm (envBind bFact (VFact fact) env) mKey
                 , fact :* weight)
               | fact :* weight <- fws ]

   in   case List.sortOn fst kfws of
         (k, fw) : _ -> [fw]
         _           -> []

selectFromFacts fws env bFact (SelectLast mKey)
 = let  kfws = [ ( evalTerm (envBind bFact (VFact fact) env) mKey
                 , fact :* weight)
               | fact :* weight <- fws ]

   in   case reverse $ List.sortOn fst kfws of
         (k, fw) : _ -> [fw]
         _           -> []


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
        -> Maybe Auth           -- ^ Resulting authority, including what we started with.

gainFromFact aHas fact env (GainAnn a acquire)
 = gainFromFact aHas fact env acquire

gainFromFact aHas fact env GainNone
 = Just aHas

gainFromFact aHas fact env (GainTerm mAuth)
 = case evalTerm env mAuth of
        VAuth aFact
          |  Set.isSubsetOf (Set.fromList aFact) (Set.fromList $ factBy fact)
          -> Just (List.nubOrd (aHas ++ aFact))

          |  otherwise -> Nothing

        v -> error $ unlines
                [ "gainFromFact: auth term is ill-typed"
                , "  value = " ++ show v ]
