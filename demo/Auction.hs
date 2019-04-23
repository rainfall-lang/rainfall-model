
module Auction where
import Rainfall.EDSL
import Rainfall.Core.Eval

import Text.Show.Pretty
import qualified Data.Map       as Map


---------------------------------------------------------------------------------------------------
-- fact Item    [lot: Symbol, desc: Text, ask: Nat]
-- fact Enter   [lot: Symbol, broker: Party, offer: Nat]
-- fact Bid     [lot: Symbol, broker: Party, offer: Nat]

-- fact Order   [broker: Party, buyer: Party, desc: Text, limit: Nat]
-- fact Reserve [broker: Party, buyer: Party, lot: Nat, offer: Nat]
-- fact Budget  [broker: Party, buyer: Party, budget: Nat]

-- TODO
-- add private Budget workflow on Brendan's side,
-- to track outsanding bids entered for alice.

---------------------------------------------------------------------------------------------------
auction'rules
 =      [ "auction'bid'enter"
        , "auction'bid'reserve" ]


-- | A broker enters an order for a client.
auction'bid'enter
 = rule "auction'bid'enter"
 [ match'any "enter" "Enter"
        anyof (consume 1)
        (gain (auth'one ("enter" ! "broker")))

  , match'when "item" "Item"
        [ nat'eq  ("item" ! "lot")    ("enter" ! "lot")
        , nat'le  ("enter" ! "offer") ("item" ! "ask")  ]
        anyof none
        (gain (auth'one (party "Mark")))
 ]
 $ say  "Bid"
        [ "id"          := ("item"  ! "lot")
        , "broker"      := ("enter" ! "broker")
        , "price"       := ("enter" ! "offer") ]
        [ "by"          := auth'one ("enter" ! "broker")
        , "obs"         := auth'one (party "Mark")
        , "use"         := rules auction'rules ]


-- | A broker reserves a portion of the client's budget
--   and forwards an order to the market.
auction'bid'reserve
 = rule "auction'bid'reserve"
 [ match'any "order" "Order"
        anyof none
        (gain (auth'one ("order" ! "buyer")))

 , match'when "item" "Item"
        [ text'eq ("item" ! "desc") ("order" ! "desc")]
        (firstof  ("item" ! "ask")) none
        same -- TODO: check auth without gain.

 , match'when "reserve" "Reserve"
        [ party'eq ("reserve" ! "broker") ("order" ! "broker")
        , party'eq ("reserve" ! "buyer")  ("order" ! "buyer")
        , nat'eq   ("reserve" ! "lot")    ("item"  ! "lot")
        , nat'le   ("reserve" ! "amount") ("order" ! "limit") ]
        anyof (consume 1)
        (gain (auth'one ("reserve" ! "broker")))

 , match'when "budget"  "Budget"
        [ party'eq ("budget" ! "broker") ("reserve" ! "broker")
        , party'eq ("budget" ! "buyer")  ("reserve" ! "buyer")
        , nat'ge   ("budget" ! "remain") ("reserve" ! "amount") ]
        anyof (consume 1)
        (gain (auth'one ("budget" ! "broker")))
 ]
 $ (say "Budget"
        [ "broker"      := ("budget" ! "broker")
        , "buyer"       := ("budget" ! "buyer")
        , "budget"      := ("budget" ! "budget")
        , "remain"      := nat'sub ("budget" ! "remain") ("reserve" ! "amount") ]
        [ "by"          := auth'one ("budget" ! "broker")
        , "use"         := rules auction'rules ])
  `sqq`
   (say "Enter"
        [ "lot"         := ("item"    ! "lot")
        , "broker"      := ("reserve" ! "broker")
        , "offer"       := ("reserve" ! "amount") ]
        [ "by"          := auth'union   (auth'one ("reserve" ! "broker"))
                                        (auth'one ("order"   ! "buyer"))
        , "obs"         := auth'one (party "Mark")
        , "use"         := rules auction'rules ])




-- auction'bid'clear


---------------------------------------------------------------------------------------------------

aSay1   nSub nsObs nFact nmsField
 = sayS' nSub nsObs nFact nmsField auction'rules 1


test1
 = runScenario ["Bob"]
        [ auction'bid'enter
        , auction'bid'reserve ]
 $ do
        -- Alice tells Brendan that she wants Rock Lobsters,
        --   for less than 28 each,
        --   with a total budget of 100.
        aSay1   "Alice" ["Brendan"] "Order"
                [ "broker" := party "Brendan"
                , "buyer"  := party "Alice"
                , "desc"   := text "Rock Lobster"
                , "limit"  := nat 28, "budget" := nat 100 ]

        -- Brendan initializes a budget to track outstanding bids for Alice.
        --  The budget only needs to be observable to Brendan.
        aSay1   "Brendan" [] "Budget"
                [ "broker" := party "Brendan"
                , "buyer"  := party "Alice"
                , "desc"   := text "Rock Lobster"
                , "budget" := nat 100
                , "remain" := nat 100 ]

        -- Mark announces the items for sale.
        aSay1   "Mark"  ["Brendan", "Brett"] "Item"
                [ "lot" := nat 1001, "desc" := text "Rock Lobster"
                , "ask" := nat 24 ]

        aSay1   "Mark"  ["Brendan", "Brett"] "Item"
                [ "lot" := nat 1002, "desc" := text "Rock Lobster"
                , "ask" := nat 26 ]

        aSay1   "Mark"  ["Brendan", "Brett"] "Item"
                [ "lot" := nat 1002, "desc" := text "Bikini Whale"
                , "ask" := nat 645 ]

        -- Print state at the start of the auction.
        printStoreS

        -- Brendan enters a bid of 22 for the first lobster,
        --  checking the current budget along the way.
        --  The reservation fires one of his internal business rules,
        --  so it only needs to be visible to him.
        aSay1   "Brendan" [] "Reserve"
                [ "broker" := party "Brendan"
                , "buyer"  := party "Alice"
                , "lot"    := nat 1001
                , "amount" := nat 22 ]

        fireS ["Brendan"] "auction'bid'reserve"

        -- The first lobster goes to Bob, for a higher price.
--        aSay1   "Mark"   [ "Bob", "Brendan", "Alice"]
--                "Accept" [ "lot" := nat 1001, "broker" := party "Bob", "price" := nat 23 ]

        printStoreS

        fireS ["Brendan"] "auction'bid'enter"


