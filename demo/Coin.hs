
module Coin where
import Rainfall.EDSL
import Rainfall.Core.Eval
import Rainfall.Core.Codec.Text.Pretty
import qualified Data.Map       as Map
import Text.Show.Pretty


---------------------------------------------------------------------------------------------------
store1 :: Store
store1
 = Map.fromList
 [ Fact  "Coin" [ "holder"      := VParty "Alice"
                , "issuer"      := VParty "Isabelle"]
        (auths ["Isabelle", "Alice"]) (auths psAll) ["transfer"]
   := 1

 , Fact "Offer" [ "id"          := VSym   "1234"
                , "giver"       := VParty "Alice"
                , "receiver"    := VParty "Bob" ]
        (auths ["Alice"]) (auths psAll) ["transfer"]
   := 1

 , Fact "Accept" [ "id"          := VSym   "1234"
                 , "accepter"    := VParty "Bob" ]
        (auths ["Bob"])  (auths psAll)  ["transfer"]
   := 1
  ]

psAll   = ["Isabelle", "Alice", "Bob"]


---------------------------------------------------------------------------------------------------
rule'transfer
 = rule "transfer"
 [ match'any "accept" "Accept"
        anyof (consume 1)
        (gain (auth'one ("accept" ! "accepter")))

 , match'when "offer" "Offer"
        [ symbol'eq ("accept" ! "id") ("offer" ! "id")
        , party'eq  ("accept" ! "accepter") ("offer" ! "receiver") ]
        anyof (consume 1)
        (gain (auth'one ("offer" ! "giver")))

 , match'when "coin" "Coin"
        [ party'eq ("coin" ! "holder") ("offer" ! "giver") ]
        anyof (consume 1)
        (gain (auth'one ("coin" ! "issuer")))
 ]
 $ say  "Coin"
        [ "issuer"      := ("coin"  ! "issuer")
        , "holder"      := ("offer" ! "receiver") ]
        [ "by"          := auth'union (auth'one ("coin" ! "issuer")) (auth'one ("offer" ! "receiver"))
        , "rules"       := rules ["transfer"] ]


---------------------------------------------------------------------------------------------------
test1   = runFire (auths ["Alice"]) store1 rule'transfer


---------------------------------------------------------------------------------------------------
-- Source form of the rule.
--
-- fact Coin   [issuer: Party, holder: Party]
-- fact Offer  [id: Symbol, giver: Party, receiver: Party]
-- fact Accept [id: Symbol, accepter: Party]
--
-- rule transfer
-- await Accept [id = ?i, accepter = ?a]  gain a
--  and  Offer  [id = i,  receiver = a, giver = g]  gain g
--  and  Coin   [issuer = ?s, holder = g] gain s
-- to
--  say  Coin   [issuer = s,  holder = r]
--       by {s, r} use {transfer}
--

---------------------------------------------------------------------------------------------------
-- Desugared version of above.
--
-- rule transfer
-- await Accept as accept
--       acquire (auth'one accept.accepter)
--   and Offer  as offer
--       where  accept.id       == offer.id,
--              accept.accepter == offer.receiver
--       acquire (auth'one offer.giver)
--   and Coin   as coin
--       where  coin.holder     == offer.giver
--       acquire (auth'one %Bank)
-- to
--      say Coin [ stamp  = coin.stamp
--               , holder = offer.receiver ]
--      by (auth'union (auth'one %Bank) (auth'one offer.receiver)
--      rules (rule'one `transfer)
--

