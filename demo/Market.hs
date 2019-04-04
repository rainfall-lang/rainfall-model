
module Market where
import Rainfall.EDSL
import Rainfall.Core.Eval

import Text.Show.Pretty
import qualified Data.Map       as Map


---------------------------------------------------------------------------------------------------
-- fact BuyReq  [id: Symbol, customer: Party, symbol: Symbol, priceMin: Nat, priceMax: Nat ]
-- fact BuyAck  [id: Symbol, broker: Party,   price:  Nat]
-- fact BuyOrd  [id: Symbol, customer: Party, symbol: Symbol, price: Nat ]

-- fact Quote   [seq: Nat,   symbol: Symbol, priceBid: Nat, priceAsk: Nat]

---------------------------------------------------------------------------------------------------




---------------------------------------------------------------------------------------------------
rule'forward'buy
 = rule "forward'buy"
 [ match (rake'when  "quote" "Quote"
                [ symbol'eq ("quote" ! "symbol")   ("req" ! "symbol")
                , nat'ge    ("quote" ! "priceAsk") ("req" ! "priceMin")
                , nat'le    ("quote" ! "priceAsk") ("req" ! "priceMax") ]
                (lastof ("quote" ! "seq")) retain)
         none

 , match (rake'facts "req"   "BuyReq" anyof (consume 1))
         (gain (auth'one ("req" ! "customer")))

 , match (rake'when  "ack"   "BuyAck"
                [ symbol'eq ("req" ! "id") ("ack" ! "id") ]
                anyof (consume 1))
         (gain (auth'one ("ack" ! "broker")))
 ]
 $ say  "BuyOrd"
        [ "id"          := ("req" ! "id")
        , "customer"    := ("req" ! "customer")
        , "symbol"      := ("req" ! "symbol")
        , "price"       := ("req" ! "price") ]
        [ "by"          := auth'union (auth'one ("req" ! "customer"))
                                      (auth'one ("ack" ! "broker"))
        , "obs"         := auth'one   (party "Market")
        , "rules"       := rules ["buy'match"] ]



