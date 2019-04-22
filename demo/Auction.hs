
module Auction where
import Rainfall.EDSL
import Rainfall.Core.Eval

import Text.Show.Pretty
import qualified Data.Map       as Map


---------------------------------------------------------------------------------------------------
-- fact Order   [desc: Text, buyer: Party, limit: Nat]
-- fact Item    [lot: Symbol, desc: Text, ask: Nat]
-- fact Enter   [lot: Symbol, broker: Party, offer: Nat]

-- fact Bid     [lot: Symbol, broker: Party, offer: Nat]

---------------------------------------------------------------------------------------------------

store1 :: Store
store1
 = Map.fromList
 [ Fact "Item"  [ "lot"         := VNat 1001
                , "desc"        := VText "Rock Lobster"
                , "ask"         := VNat 24 ]
        (auths ["Mark"]) (auths ["Bob"]) ["auction'bid"]
   := 5

 , Fact "Item"  [ "lot"         := VNat 1002
                , "desc"        := VText "Rock Lobster"
                , "ask"         := VNat 26 ]
        (auths ["Mark"]) (auths ["Bob"]) ["auction'bid"]
   := 2

 , Fact "Item"  [ "lot"         := VNat 1003
                , "desc"        := VText "Bikini Whale"
                , "ask"         := VNat 645 ]
        (auths ["Mark"]) (auths ["Bob"]) ["auction'bid"]
   := 2

 , Fact "Order" [ "desc"        := VText "Rock Lobster"
                , "buyer"       := VParty "Alice"
                , "limit"       := VNat  28 ]
        (auths ["Alice"]) (auths ["Bob"]) ["auction'bid"]
   := 1

 , Fact "Enter" [ "lot"         := VNat 1001
                , "broker"      := VParty "Bob"
                , "offer"       := VNat 23 ]
        (auths ["Bob"]) (auths ["Mark"]) ["auction'bid"]
   := 1
 ]


---------------------------------------------------------------------------------------------------
rule'auction'bid
 = rule "auction'bid"
 [ match'any  "order" "Order"
        anyof (consume 1)
        (gain (auth'one ("order" ! "buyer")))

 , match'when "item" "Item"
        [ text'eq ("item" ! "desc") ("order" ! "desc")]
        (firstof  ("item" ! "ask")) none
        same

 , match'when "enter" "Enter"
        [ nat'eq ("item"  ! "lot")   ("enter" ! "lot")
        , nat'le ("enter" ! "offer") ("order" ! "limit") ]
        anyof (consume 1)
        (gain (auth'one ("enter" ! "broker")))
 ]
 $ say  "Bid"
        [ "id"          := ("item"  ! "lot")
        , "broker"      := ("enter" ! "broker")
        , "price"       := ("enter" ! "offer") ]
        [ "by"          := auth'union (auth'one ("enter" ! "broker"))
                                      (auth'one ("order" ! "buyer"))
        , "obs"         := auth'one (party "Mark") ]


---------------------------------------------------------------------------------------------------
test1   = runFire (auths ["Bob"]) store1 rule'auction'bid


