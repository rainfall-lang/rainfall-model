
import Rainfall.EDSL
import Rainfall.Core.Eval
import qualified Data.Map       as Map


store1  :: Store
store1  = Map.fromList
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

