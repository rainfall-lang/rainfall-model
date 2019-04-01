
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


-- Coin [ stamp: Symbol, holder: Party ]


-- rakeFromStore :: Rake a -> Store -> ([Fact ()], Consume ())
-- rakeFromStore (Rake n _gather _select _consume)


-- | Gather visible facts from the store that match the gather predicates,
--   returning all matching facts and the available weight of each one.
-- gatherFromStore :: Auth -> Env a -> Bind -> Gather a -> Store -> [(Fact (), Weight)]
-- gatherFromStore aHas env bFact (GatherAnn _a gg) store
-- = gatherFromStore bFact gg

-- gatherFromStore aHas env bFact (GatherWhen nFact msPred) (Store fws)
-- = [ fact | (fact, weight)   <- fws
--          , factName fact == nFact
--          , seesFact aHas fact
--          , all (isVTrue . eval env) msPred ]    -- TODO: bind fact into env.








