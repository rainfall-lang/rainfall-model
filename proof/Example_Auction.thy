(* Auction example: see also demo/Auction.hs *)
theory Example_Auction
  imports Dynamic
begin
section \<open>Rule names\<close>

definition "auction_bid_rn    = rule_name ''auction_bid''"
definition "auction_accept_rn = rule_name ''auction_accept''"
definition "broker_reserve_rn = rule_name ''broker_reserve''"

definition "auction_rules = {auction_bid_rn, auction_accept_rn}"
definition "broker_rules  = {broker_reserve_rn}" 

section \<open>Fact definitions\<close>
(*
auction side:
fact Accept  [lot: Symbol, broker: Party, price: Nat]
fact Item    [lot: Symbol, desc: Text, ask: Nat]
fact Invoice [broker: Party, buyer: Party, desc: Text, amount: Nat]
fact Bid     [lot: Symbol, broker: Party, buyer: Party, price: Nat]
fact Offer   [lot: Symbol, broker: Party, buyer: Party, price: Nat]

broker side:
fact Order   [broker: Party, buyer: Party, desc: Text, limit: Nat]
fact Reserve [broker: Party, buyer: Party, lot: Nat, offer: Nat]
fact Budget  [broker: Party, buyer: Party, budget: Nat]
*)

(* Boilerplate for fact definitions: these would be a lot cleaner if we used a shallow embedding for the types,
   but they're all pretty mechanical anyway.
*)
definition "mk_AcceptPayload lot broker price = vpair (vlit (lsymbol lot)) (vpair (vlit (lparty broker)) (vlit (lnat price)))"
fun tk_AcceptPayload where
  "tk_AcceptPayload (vpair (vlit (lsymbol lot)) (vpair (vlit (lparty broker)) (vlit (lnat price)))) = (lot, broker, price)"
| "tk_AcceptPayload _ = undefined" 

definition "Accept_lot    =       fst o tk_AcceptPayload o fact_value"
definition "Accept_broker = fst o snd o tk_AcceptPayload o fact_value"
definition "Accept_ask    = snd o snd o tk_AcceptPayload o fact_value"

definition "Accept = fact_ctor ''Accept''"
definition "mk_Accept lot broker price by obs = \<lparr>fact_name = Accept, fact_value = mk_AcceptPayload lot broker price, fact_by = by, fact_obs = obs, fact_rules = auction_rules\<rparr>"


definition "mk_ItemPayload lot desc ask = vpair (vlit (lsymbol lot)) (vpair (vlit (lsymbol desc)) (vlit (lnat ask)))"
fun tk_ItemPayload where
  "tk_ItemPayload (vpair (vlit (lsymbol lot)) (vpair (vlit (lsymbol desc)) (vlit (lnat ask)))) = (lot, desc, ask)"
| "tk_ItemPayload _ = undefined" 

definition "Item_lot  =       fst o tk_ItemPayload o fact_value"
definition "Item_desc = fst o snd o tk_ItemPayload o fact_value"
definition "Item_ask  = snd o snd o tk_ItemPayload o fact_value"

definition "Item = fact_ctor ''Item''"
definition "mk_Item lot desc ask by obs = \<lparr>fact_name = Item, fact_value = mk_ItemPayload lot desc ask, fact_by = by, fact_obs = obs, fact_rules = auction_rules\<rparr>"


definition "mk_InvoicePayload broker buyer desc amount = vpair (vlit (lparty broker)) (vpair (vlit (lparty buyer)) (vpair (vlit (lsymbol desc)) (vlit (lnat amount))))"
fun tk_InvoicePayload where
  "tk_InvoicePayload (vpair (vlit (lparty broker)) (vpair (vlit (lparty buyer)) (vpair (vlit (lsymbol desc)) (vlit (lnat amount))))) = (broker, buyer, desc, amount)"
| "tk_InvoicePayload _ = undefined" 

definition "Invoice_buyer  =             fst o tk_InvoicePayload o fact_value"
definition "Invoice_broker =       fst o snd o tk_InvoicePayload o fact_value"
definition "Invoice_desc   = fst o snd o snd o tk_InvoicePayload o fact_value"
definition "Invoice_amount = snd o snd o snd o tk_InvoicePayload o fact_value"

definition "Invoice = fact_ctor ''Invoice''"
definition "mk_Invoice broker buyer desc amount by obs = \<lparr>fact_name = Invoice, fact_value = mk_InvoicePayload broker buyer desc amount, fact_by = by, fact_obs = obs, fact_rules = auction_rules\<rparr>"


definition "mk_BidPayload lot broker buyer price = vpair (vlit (lsymbol lot)) (vpair (vlit (lparty broker)) (vpair (vlit (lparty buyer)) (vlit (lnat price))))"
fun tk_BidPayload where
  "tk_BidPayload (vpair (vlit (lsymbol lot)) (vpair (vlit (lparty broker)) (vpair (vlit (lparty buyer)) (vlit (lnat price))))) = (lot, broker, buyer, price)"
| "tk_BidPayload _ = undefined" 

definition "Bid_lot    =             fst o tk_BidPayload o fact_value"
definition "Bid_buyer  =       fst o snd o tk_BidPayload o fact_value"
definition "Bid_broker = fst o snd o snd o tk_BidPayload o fact_value"
definition "Bid_price  = snd o snd o snd o tk_BidPayload o fact_value"

definition "Bid = fact_ctor ''Bid''"
definition "mk_Bid lot broker buyer price by obs = \<lparr>fact_name = Bid, fact_value = mk_BidPayload lot broker buyer price, fact_by = by, fact_obs = obs, fact_rules = auction_rules\<rparr>"

(* Offer has same payload as Bid *)
definition "mk_OfferPayload = mk_BidPayload"
definition "tk_OfferPayload = tk_BidPayload"
definition "Offer_lot    = Bid_lot"
definition "Offer_buyer  = Bid_buyer"
definition "Offer_broker = Bid_broker"
definition "Offer_price  = Bid_price"

definition "Offer = fact_ctor ''Offer''"
definition "mk_Offer lot broker buyer price by obs = \<lparr>fact_name = Offer, fact_value = mk_OfferPayload lot broker buyer price, fact_by = by, fact_obs = obs, fact_rules = auction_rules\<rparr>"


definition "mk_OrderPayload broker buyer desc limit = vpair (vlit (lparty broker)) (vpair (vlit (lparty buyer)) (vpair (vlit (lsymbol desc)) (vlit (lnat limit))))"
fun tk_OrderPayload where
  "tk_OrderPayload (vpair (vlit (lparty broker)) (vpair (vlit (lparty buyer)) (vpair (vlit (lsymbol desc)) (vlit (lnat limit))))) = (broker, buyer, desc, limit)"
| "tk_OrderPayload _ = undefined" 

definition "Order_broker =             fst o tk_OrderPayload o fact_value"
definition "Order_buyer  =       fst o snd o tk_OrderPayload o fact_value"
definition "Order_desc   = fst o snd o snd o tk_OrderPayload o fact_value"
definition "Order_limit  = snd o snd o snd o tk_OrderPayload o fact_value"

definition "Order = fact_ctor ''Order''"
definition "mk_Order broker buyer desc limit by obs = \<lparr>fact_name = Order, fact_value = mk_OrderPayload broker buyer desc limit, fact_by = by, fact_obs = obs, fact_rules = broker_rules\<rparr>"


definition "mk_ReservePayload broker buyer lot amount = vpair (vlit (lparty broker)) (vpair (vlit (lparty buyer)) (vpair (vlit (lsymbol lot)) (vlit (lnat amount))))"
fun tk_ReservePayload where
  "tk_ReservePayload (vpair (vlit (lparty broker)) (vpair (vlit (lparty buyer)) (vpair (vlit (lsymbol lot)) (vlit (lnat amount))))) = (broker, buyer, lot, amount)"
| "tk_ReservePayload _ = undefined" 

definition "Reserve_broker =             fst o tk_ReservePayload o fact_value"
definition "Reserve_buyer  =       fst o snd o tk_ReservePayload o fact_value"
definition "Reserve_lot    = fst o snd o snd o tk_ReservePayload o fact_value"
definition "Reserve_amount = snd o snd o snd o tk_ReservePayload o fact_value"

definition "Reserve = fact_ctor ''Reserve''"
definition "mk_Reserve broker buyer lot amount by obs = \<lparr>fact_name = Reserve, fact_value = mk_ReservePayload broker buyer lot amount, fact_by = by, fact_obs = obs, fact_rules = broker_rules\<rparr>"


definition "mk_BudgetPayload broker buyer budget remain = vpair (vlit (lparty broker)) (vpair (vlit (lparty buyer)) (vpair (vlit (lnat budget)) (vlit (lnat remain))))"
fun tk_BudgetPayload where
  "tk_BudgetPayload (vpair (vlit (lparty broker)) (vpair (vlit (lparty buyer)) (vpair (vlit (lnat budget)) (vlit (lnat remain))))) = (broker, buyer, budget, remain)"
| "tk_BudgetPayload _ = undefined" 

definition "Budget_broker =             fst o tk_BudgetPayload o fact_value"
definition "Budget_buyer  =       fst o snd o tk_BudgetPayload o fact_value"
definition "Budget_budget = fst o snd o snd o tk_BudgetPayload o fact_value"
definition "Budget_remain = snd o snd o snd o tk_BudgetPayload o fact_value"

definition "Budget = fact_ctor ''Budget''"
definition "mk_Budget broker buyer budget remain by obs = \<lparr>fact_name = Budget, fact_value = mk_BudgetPayload broker buyer budget remain, fact_by = by, fact_obs = obs, fact_rules = broker_rules\<rparr>"

(* Fact variables *)
definition "accept_v  = fact_var ''accept''"
definition "item_v    = fact_var ''item''"
definition "bid_v     = fact_var ''bid''"
definition "offer_v   = fact_var ''offer''"
definition "order_v   = fact_var ''order''"
definition "reserve_v = fact_var ''reserve''"
definition "budget_v  = fact_var ''budget''"


section \<open>Auction bid rule\<close>

definition "match_any_when var factctor when consume auth_f = match var (gather_when factctor when) select_any (consume_weight (\<lambda>h. consume)) (gain_auth auth_f)"
definition "match_any var factctor consume auth_f = match_any_when var factctor (\<lambda>h. True) consume auth_f"
definition "match_first_when var factctor when fstby consume auth_f = match var (gather_when factctor when) (select_first fstby) (consume_weight (\<lambda>h. consume)) (gain_auth auth_f)"

definition
  "auction_bid = rule auction_bid_rn
  [ match_any bid_v Bid 1 (\<lambda>h. {Bid_buyer (h bid_v), Bid_broker (h bid_v)})
  , match_any_when item_v Item
        (\<lambda>h. Item_lot (h item_v) = Bid_lot (h bid_v) \<and> Bid_price (h bid_v) < Item_ask (h item_v))
        0
        (\<lambda>h. {party ''Mark''})
  ]
  (\<lambda>h. {#
    mk_Offer (Item_lot (h item_v)) (Bid_broker (h bid_v)) (Bid_buyer (h bid_v)) (Bid_price (h bid_v))
          {Bid_buyer (h bid_v), Bid_broker (h bid_v), party ''Mark''}
          {party ''Mark''}
  #})"


definition
  "auction_accept = rule auction_accept_rn
  [ match_any accept_v Accept 1 (\<lambda>h. {party ''Mark''})
  , match_any_when offer_v Offer
        (\<lambda>h. Offer_lot (h offer_v) = Accept_lot (h accept_v) \<and> Offer_broker (h offer_v) = Accept_broker (h accept_v))
        1
        (\<lambda>h. {Offer_broker (h offer_v), Offer_buyer (h offer_v)})
  , match_any_when item_v Item
        (\<lambda>h. Offer_lot (h offer_v) = Item_lot (h item_v))
        1
        (\<lambda>h. {party ''Mark''})

  ]
  (\<lambda>h. {#
    mk_Invoice (Offer_broker (h offer_v)) (Offer_buyer (h offer_v)) (Item_desc (h item_v)) (Offer_price (h offer_v))
          {Offer_buyer (h offer_v), Offer_broker (h offer_v), party ''Mark''}
          {}
  #})"


definition
  "broker_reserve = rule broker_reserve_rn
  [ match_any order_v Order 0 (\<lambda>h. {Order_buyer (h order_v)})
  , match_first_when item_v Item
        (\<lambda>h. Item_desc (h item_v) = Order_desc (h order_v))
        (\<lambda>h. Item_ask (h item_v))
        0
        (\<lambda>h. {party ''Mark''})
  , match_any_when reserve_v Reserve
        (\<lambda>h. Reserve_broker (h reserve_v) = Order_broker (h order_v)
           \<and> Reserve_buyer  (h reserve_v) = Order_buyer  (h order_v)
           \<and> Reserve_lot    (h reserve_v) = Item_lot     (h item_v)
           \<and> Reserve_amount (h reserve_v) \<le> Order_limit  (h order_v))
        1
        (\<lambda>h. {Reserve_broker (h reserve_v)})
  , match_any_when budget_v Budget
        (\<lambda>h. Reserve_broker (h reserve_v) = Budget_broker (h budget_v)
           \<and> Reserve_buyer  (h reserve_v) = Budget_buyer  (h budget_v)
           \<and> Reserve_amount (h reserve_v) \<le> Budget_remain (h budget_v))
        1
        (\<lambda>h. {Budget_broker (h budget_v)})
  ]
  (\<lambda>h. {#
    mk_Budget (Budget_broker (h budget_v)) (Budget_buyer (h budget_v)) (Budget_budget (h budget_v))
          (Budget_budget (h budget_v) - Reserve_amount (h reserve_v))
          {Budget_broker (h budget_v)}
          {}
  , mk_Bid (Item_lot (h item_v)) (Reserve_broker (h reserve_v)) (Order_buyer (h order_v)) (Reserve_amount (h reserve_v))
          {Reserve_broker (h reserve_v), Order_buyer (h order_v)}
          {party ''Mark''}
  #})"
