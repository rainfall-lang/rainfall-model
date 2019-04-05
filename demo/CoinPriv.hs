
module CoinPriv where
import Rainfall.EDSL
import Rainfall.Core.Eval
import qualified Data.Map       as Map
import Text.Show.Pretty


---------------------------------------------------------------------------------------------------
store1 :: Store
store1
 = Map.fromList
 [ Fact  "Coin" [ "holder"      := VParty "Alice"
                , "issuer"      := VParty "Issuer"]
        (auths ["Issuer", "Alice"]) (auths ["Monitor"]) ["transfer"]
   := 1

 , Fact "Offer" [ "id"          := VSym   "1234"
                , "giver"       := VParty "Alice"
                , "receiver"    := VParty "Bob" ]
        (auths ["Alice"]) (auths ["Monitor", "Bob"])    ["transfer"]
   := 1

 , Fact "Accept" [ "id"         := VSym   "1234"
                 , "accepter"   := VParty "Bob" ]
        (auths ["Bob"])   (auths ["Monitor", "Alice"])  ["transfer"]
   := 1
  ]

psAll   = ["Issuer", "Monitor", "Alice", "Bob"]


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
        [ "issuer"      := ("coin"  ! "issuer")
        , "holder"      := ("offer" ! "receiver") ]
        [ "by"          := auth'union (auth'one ("coin" ! "issuer"))
                                      (auth'one ("offer" ! "receiver"))
        , "obs"         := auth'one (party "Monitor")
        , "rules"       := rules ["transfer"] ]


---------------------------------------------------------------------------------------------------
test1   = putStrLn $ ppShow
        $ applyRuleToStore rule'transfer (auths ["Alice"]) store1