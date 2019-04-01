
import Rainfall.EDSL
import Rainfall.Core.Eval

store1  = Store
        [ Fact  "Coin"  ["holder" := "Alice", "stamp" := "RainCoin"]
                ["Alice"] [] ["transfer"]
        := 1 ]


rule'transfer
 = rule "transfer"
 [ match (rake'facts "accept" "Accept"
                anyof (consume 1))
         (acquire ("accept" ! "receiver"))

 , match (rake'when "offer" "Offer"
                [ symbol'eq ("accept" ! "id") ("offer" ! "id")
                , party'eq  ("accept" ! "accepter") ("offer" ! "receiver") ]
                anyof (consume 1))
         (acquire ("offer" ! "giver"))

 , match (rake'when "coin" "Coin"
                [ party'eq ("coin" ! "holder") ("offer" ! "giver") ]
                anyof (consume 1))
         (acquire ("coin" ! "owner"))]
 $ say  "Coin"
        [ "stamp"       := sym   "RainCoin"
        , "holder"      := party "Alice" ]
        [ "by"          := auth  ["Alice", "Bank"]
        , "rules"       := rules ["transfer"] ]


-- rakeCoin = rake'when "Coin" [party'eq ("c" ! "holder") ("offer" ! "giver")] anyof (consume 1)


-- | Rake facts from the store,
rakeFromStore
        :: Name                 -- ^ Name of the current rule.
        -> Auth                 -- ^ Authority of the rule performing the rake.
        -> Env ()               -- ^ Current environment.
        -> Rake ()              -- ^ Rake to perform.
        -> Store                -- ^ Store to rake facts from.
        -> ([(Fact (), Weight)], Store)

rakeFromStore nRule auth env (Rake bFact gather _select consume) store
 = let
        -- Gather initial facts that match the predicates.
        fsGathered
         = gatherFromStore auth env bFact gather store

        -- TODO: select a subset of the gathered facts.

        -- TODO: remove consumed facts from the store,
        -- as we cannot rake the same facts a second time.
        -- TODO: we can only consume facts that have the current rule name in their use set.

   in   (fsGathered, store)


-- | Gather visible facts from the store that match the gather predicates,
--   returning all matching facts and the available weight of each one.
gatherFromStore
        :: Auth                 -- ^ Authority of the rule performing the gather.
        -> Env ()               -- ^ Current environment, used in gather predicates.
        -> Bind                 -- ^ Binder for the fact value in the gather predicate.
        -> Gather ()            -- ^ The gather predicates.
        -> Store                -- ^ Store to gather facts from.
        -> [(Fact (), Weight)]

gatherFromStore aHas env bFact (GatherAnn _a gg) store
 = gatherFromStore nRule aHas env bFact gg store

gatherFromStore aHas env bFact (GatherWhen nFact msPred) (Store fws)
 = [ (fact, weight)
        | (fact, weight)   <- fws
        , factName fact == nFact        -- Fact has name that we want.
        , seesFact aHas fact            -- Fact is visible with the current authority.
        , let env' = envBind bFact (VFact fact) env
          in  all (isVTrue . evalTerm env') msPred ]
