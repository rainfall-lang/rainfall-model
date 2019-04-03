
import Rainfall.EDSL
import Rainfall.Core.Eval
import qualified Data.Map       as Map
import Text.Show.Pretty


store1  :: Store
store1  = Map.fromList
        [ Fact  "Coin"  [ "holder"      := VParty "Alice"
                        , "stamp"       := VSym   "RainCoin"]
                ["Alice", "Bank"] [] ["transfer"]
          := 1

        , Fact "Offer"  [ "id"          := VSym   "1234"
                        , "giver"       := VParty "Alice"
                        , "receiver"    := VParty "Bob" ]
                ["Alice"] [] ["transfer"]
          := 1

        , Fact "Accept" [ "id"          := VSym   "1234"
                        , "accepter"    := VParty "Bob" ]
                ["Bob"] [] ["transfer"]
          := 1
        ]


rule'transfer
 = rule "transfer"
 [ match (rake'facts "accept" "Accept"
                anyof (consume 1))
         (acquire (auth'one ("accept" ! "accepter")))

 , match (rake'when "offer" "Offer"
                [ symbol'eq ("accept" ! "id") ("offer" ! "id")
                , party'eq  ("accept" ! "accepter") ("offer" ! "receiver") ]
                anyof (consume 1))
         (acquire (auth'one ("offer" ! "giver")))

 , match (rake'when "coin" "Coin"
                [ party'eq ("coin" ! "holder") ("offer" ! "giver") ]
                anyof (consume 1))
         (acquire (auth'union (auth'one ("coin" ! "holder")) (auth'one (party "Bank"))))
 ]
 $ say  "Coin"
        [ "stamp"       := sym   "RainCoin"
        , "holder"      := ("offer" ! "receiver") ]
        [ "by"          := auth'union (auth'one "Bank") ("offer" ! "receiver")
        , "rules"       := rules ["transfer"] ]


