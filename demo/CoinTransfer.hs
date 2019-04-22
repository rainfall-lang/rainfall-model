
module CoinTransfer where
import Rainfall.EDSL
import Rainfall.Core.Eval
import qualified Data.Map       as Map
import Text.Show.Pretty


---------------------------------------------------------------------------------------------------
-- fact Coin   [issuer: Party, holder: Party]
-- fact Offer  [id: Symbol, terms: Text, giver: Party, receiver: Party]
-- fact Accept [id: Symbol, accepter: Party]

store1 :: Store
store1
 = Map.fromList
 [ Fact  "Coin" [ "issuer"      := VParty "Isabelle"
                , "holder"      := VParty "Alice" ]
        (auths ["Isabelle", "Alice"]) (auths ["Mona"]) ["transfer"]
   := 1

 , Fact "Offer" [ "id"          := VSym   "1234"
                , "giver"       := VParty "Alice"
                , "receiver"    := VParty "Bob" ]
        (auths ["Alice"]) (auths ["Mona", "Bob"])    ["transfer"]
   := 1

 , Fact "Accept" [ "id"         := VSym   "1234"
                 , "accepter"   := VParty "Bob" ]
        (auths ["Bob"])   (auths ["Mona", "Alice"])  ["transfer"]
   := 1
  ]


---------------------------------------------------------------------------------------------------
rule'transfer
 = rule "transfer"
 [ match'any  "accept" "Accept"
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
        [ "issuer"      := ("coin"   ! "issuer")
        , "holder"      := ("accept" ! "accepter") ]
        [ "by"          := auth'union (auth'one ("coin"   ! "issuer"))
                                      (auth'one ("accept" ! "accepter"))
        , "obs"         := auth'one (party "Mona")
        , "use"         := rules ["transfer"] ]


---------------------------------------------------------------------------------------------------
test1   = runFire (auths ["Alice"]) store1 rule'transfer
