
import Rainfall.EDSL
import qualified Data.List      as List


sees  :: Auth -> Fact a -> Bool
sees aHas (Fact n _env aBy aObs _nsRules)
 = not $ null $ List.intersect aHas (List.union aBy aObs)



aBob    = ["Bob"]

fTok    = Fact "Tok" [("stamp", VSym "Dude")] aBob aBob []
mcFalse = MAbs "x" TAuth MFalse



ruleTransfer
 = rule "transfer"
 [ match "a" "accept"
        (rake'facts "Accept" anyof (consume 1))
        (acquire ("a" ! "receiver"))

 , match "o" "offer"
        (rake'when "Offer"
                [ symbol'eq ("accept" ! "id") ("o" ! "id")
                , party'eq  ("accept" ! "accepter") ("o" ! "receiver") ]
                anyof (consume 1))
        (acquire ("o" ! "giver"))

 , match "c" "coin"
        (rake'when "Coin"
                [ party'eq ("c" ! "holder") ("offer" ! "giver") ]
                anyof (consume 1))
        (acquire ("c" ! "owner"))]
 $ say  "Coin"
        [ "stamp"       := sym   "RainCoin"
        , "holder"      := party "Alice" ]
        [ "by"          := auth  ["Alice", "Bank"]
        , "rules"       := rules ["transfer"] ]






