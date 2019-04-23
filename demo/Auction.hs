
module Auction where
import Rainfall.EDSL
import Rainfall.Core.Eval

import Text.Show.Pretty
import qualified Data.Map       as Map


---------------------------------------------------------------------------------------------------
-- fact Item    [lot: Symbol, desc: Text, ask: Nat]
-- fact Offer   [lot: Symbol, broker: Party, offer: Nat]
-- fact Bid     [lot: Symbol, broker: Party, buyer: Party, offer: Nat]

-- fact Order   [broker: Party, buyer: Party, desc: Text, limit: Nat]
-- fact Reserve [broker: Party, buyer: Party, lot: Nat, offer: Nat]
-- fact Budget  [broker: Party, buyer: Party, budget: Nat]

-- TODO
-- add private Budget workflow on Brendan's side,
-- to track outsanding bids entered for alice.

---------------------------------------------------------------------------------------------------
-- TODO: split rule lists to market side vs broker side.
auction'rules
 = [auction'reserve, auction'bid, auction'accept]

use'auction
 = rules $ map ruleName auction'rules


-- | The market receives a bid from a broker,
--     checks that there is a matching item for sale,
--     and that the bid price is not more than the asking price.
--   On success the bid is converted to a valid offer.
auction'bid
 = rule "auction'bid"
 [ match'any "bid" "Bid"
        anyof (consume 1)
        (gain $ auth'union (auth'one ("bid" ! "buyer"))
                           (auth'one ("bid" ! "broker")))

  , match'when "item" "Item"
        [ nat'eq  ("item" ! "lot")    ("bid" ! "lot")
        , nat'le  ("bid" ! "price") ("item" ! "ask")  ]
        anyof none
        (gain (auth'one (party "Mark")))
 ]
 $ say  "Offer"
        [ "lot"         := ("item"  ! "lot")
        , "broker"      := ("bid" ! "broker")
        , "buyer"       := ("bid" ! "buyer")
        , "price"       := ("bid" ! "price") ]
        [ "by"          := auth'union
                                (auth'union (auth'one ("bid" ! "buyer"))
                                            (auth'one ("bid" ! "broker")))
                                (auth'one (party "Mark"))
        , "obs"         := auth'one (party "Mark")
        , "use"         := use'auction ]


-- | The market accepts an offer, completing the sale.
--   The both the offer and item are removed from the listing,
--   and an Invoice is created for the order.
auction'accept
 = rule "auction'accept"
 [ match'any "accept" "Accept"
        anyof (consume 1)
        (gain $ auth'one (party "Mark"))

 , match'when "offer" "Offer"
        [ nat'eq   ("offer" ! "lot")    ("accept" ! "lot")
        , party'eq ("offer" ! "broker") ("accept" ! "broker") ]
        anyof (consume 1)
        (gain $ auth'union
                        (auth'one ("offer" ! "broker"))
                        (auth'one ("offer" ! "buyer")))

 , match'when "item" "Item"
        [ nat'eq   ("item"  ! "lot")   ("offer" ! "lot") ]
        anyof (consume 1)
        (gain $ auth'one (party "Mark"))
 ]
 $ say  "Invoice"
        [ "broker"      := ("offer" ! "broker")
        , "buyer"       := ("offer" ! "buyer")
        , "desc"        := ("item"  ! "desc")
        , "amount"      := ("offer" ! "price") ]
        [ "by"  := auth'union
                                (auth'union (auth'one ("offer" ! "buyer"))
                                            (auth'one ("offer" ! "broker")))
                                (auth'one (party "Mark")) ]


-- | A broker reserves a portion of the client's budget and
--   sends a bid to the market for one of the items the client has ordered.
auction'reserve
 = rule "auction'reserve"
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
        , "use"         := use'auction ])
  `sqq`
   (say "Bid"
        [ "lot"         := ("item"    ! "lot")
        , "broker"      := ("reserve" ! "broker")
        , "buyer"       := ("order"   ! "buyer")
        , "price"       := ("reserve" ! "amount") ]
        [ "by"          := auth'union   (auth'one ("reserve" ! "broker"))
                                        (auth'one ("order"   ! "buyer"))
        , "obs"         := auth'one (party "Mark")
        , "use"         := use'auction ])


---------------------------------------------------------------------------------------------------
aSay1   nSub nsObs nFact nmsField
 = sayS' nSub nsObs nFact nmsField
        (map ruleName auction'rules)
        1

test1
 = runScenario ["Bob"] auction'rules
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
                [ "lot" := nat 1003, "desc" := text "Bikini Whale"
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

        fireS ["Brendan"] "auction'reserve"


        -- Mark cycles Brendan's bid into a valid offer.
        fireS ["Mark"] "auction'bid"

        -- Mark accepts Brendan's bid.
        --  Item listing is removed and invoice to Brendan generated.
        --  Rock Lobster is sold.
        aSay1   "Mark"   ["Brendan"] "Accept"
                [ "lot" := nat 1001, "broker" := party "Brendan", "price" := nat 22 ]

        fireS ["Mark"] "auction'accept"

