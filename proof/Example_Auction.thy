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

record Value =
  item_lot      :: symbol
  item_desc     :: symbol
  party_buyer   :: party
  party_broker  :: party
  price_amount  :: nat
  price_limit   :: nat
  budget_total  :: nat
  budget_remain :: nat

declare Value.make_def[simp]
definition [simp]:
  "value0 = Value.make undefined undefined undefined undefined undefined undefined undefined undefined"

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


definition "Accept = fact_ctor ''Accept''"
definition "mk_Accept lot broker price by obs =
  \<lparr>fact_name = Accept,
  fact_value = value0 \<lparr>item_lot := lot, party_broker := broker, price_amount := price\<rparr>,
  fact_by = by, fact_obs = obs, fact_rules = auction_rules\<rparr>"

definition "Item = fact_ctor ''Item''"
definition "mk_Item lot desc ask by obs =
  \<lparr>fact_name = Item,
  fact_value = value0 \<lparr>item_lot := lot, item_desc := desc, price_amount := ask\<rparr>,
  fact_by = by, fact_obs = obs, fact_rules = auction_rules\<rparr>"

definition "Invoice = fact_ctor ''Invoice''"
definition "mk_Invoice broker buyer desc amount by obs =
  \<lparr>fact_name = Invoice,
  fact_value = value0 \<lparr>party_broker := broker, party_buyer := buyer, item_desc := desc, price_amount := amount\<rparr>,
  fact_by = by, fact_obs = obs, fact_rules = auction_rules\<rparr>"

definition "Bid = fact_ctor ''Bid''"
definition "mk_Bid lot broker buyer price by obs =
  \<lparr>fact_name = Bid,
  fact_value = value0 \<lparr> item_lot := lot, party_broker := broker, party_buyer := buyer, price_amount := price\<rparr>,
  fact_by = by, fact_obs = obs, fact_rules = auction_rules\<rparr>"

definition "Offer = fact_ctor ''Offer''"
definition "mk_Offer lot broker buyer price by obs =
  \<lparr>fact_name = Offer,
  fact_value = value0 \<lparr> item_lot := lot, party_broker := broker, party_buyer := buyer, price_amount := price \<rparr>,
  fact_by = by, fact_obs = obs, fact_rules = auction_rules\<rparr>"

definition "Order = fact_ctor ''Order''"
definition "mk_Order broker buyer desc limit budget by obs =
  \<lparr>fact_name = Order,
  fact_value = value0 \<lparr> party_broker := broker, party_buyer := buyer, item_desc := desc, price_limit := limit, budget_total := budget\<rparr>,
  fact_by = by, fact_obs = obs, fact_rules = broker_rules\<rparr>"

definition "Reserve = fact_ctor ''Reserve''"
definition "mk_Reserve broker buyer lot amount by obs =
  \<lparr>fact_name = Reserve,
  fact_value = value0 \<lparr>party_broker := broker, party_buyer := buyer, item_lot := lot, price_amount := amount\<rparr>,
  fact_by = by, fact_obs = obs, fact_rules = broker_rules\<rparr>"

definition "Budget = fact_ctor ''Budget''"
definition "mk_Budget broker buyer budget remain by obs =
  \<lparr>fact_name = Budget,
  fact_value = value0 \<lparr>party_broker := broker, party_buyer := buyer, budget_total := budget, budget_remain := remain\<rparr>,
  fact_by = by, fact_obs = obs, fact_rules = broker_rules\<rparr>"

(* Fact variables *)
definition "accept_v  = fact_var ''accept''"
definition "item_v    = fact_var ''item''"
definition "bid_v     = fact_var ''bid''"
definition "offer_v   = fact_var ''offer''"
definition "order_v   = fact_var ''order''"
definition "reserve_v = fact_var ''reserve''"
definition "budget_v  = fact_var ''budget''"


section \<open>Auction bid rule\<close>

definition [simp]: "match_any_when var factctor when consume auth_f = match var (gather_when factctor when) select_any (consume_weight (\<lambda>h. consume)) (gain_auth auth_f)"
definition [simp]: "match_any var factctor consume auth_f = match_any_when var factctor (\<lambda>h. True) consume auth_f"
definition [simp]: "match_first_when var factctor when fstby consume auth_f = match var (gather_when factctor when) (select_first fstby) (consume_weight (\<lambda>h. consume)) (gain_auth auth_f)"

definition [simp]: "field f h v = f (fact_value (h v))"


definition [simp]:
  "auction_bid = rule auction_bid_rn
  [ match_any bid_v Bid 1 (\<lambda>h. {field party_buyer h bid_v, field party_broker h bid_v})
  , match_any_when item_v Item
        (\<lambda>h. field item_lot h item_v = field item_lot h bid_v \<and> field price_amount h bid_v \<le> field price_amount h item_v)
        0
        (\<lambda>h. {party ''Mark''})
  ]
  (\<lambda>h. {#
    mk_Offer (field item_lot    h item_v) (field party_broker h bid_v)
             (field party_buyer h bid_v)  (field price_amount h bid_v)
          {field party_buyer h bid_v, field party_broker h bid_v, party ''Mark''}
          {party ''Mark''}
  #})"


definition
  "auction_accept = rule auction_accept_rn
  [ match_any accept_v Accept 1 (\<lambda>h. {party ''Mark''})
  , match_any_when offer_v Offer
        (\<lambda>h. field item_lot h offer_v = field item_lot h accept_v
           \<and> field party_broker h offer_v = field party_broker h accept_v)
        1
        (\<lambda>h. {field party_broker h offer_v, field party_buyer h offer_v})
  , match_any_when item_v Item
        (\<lambda>h. field item_lot h offer_v = field item_lot h item_v)
        1
        (\<lambda>h. {party ''Mark''})

  ]
  (\<lambda>h. {#
    mk_Invoice (field party_broker h offer_v) (field party_buyer  h offer_v)
               (field item_desc    h item_v)  (field price_amount h offer_v)
          {field party_buyer h offer_v, field party_broker h offer_v, party ''Mark''}
          {}
  #})"


definition
  "broker_reserve = rule broker_reserve_rn
  [ match_any order_v Order 0 (\<lambda>h. {field party_buyer h order_v})
  , match_first_when item_v Item
        (\<lambda>h. field item_desc    h item_v = field item_desc h order_v)
        (\<lambda>h. field price_amount h item_v)
        0
        (\<lambda>h. {party ''Mark''})
  , match_any_when reserve_v Reserve
        (\<lambda>h. field party_broker h reserve_v = field party_broker h order_v
           \<and> field party_buyer  h reserve_v = field party_buyer  h order_v
           \<and> field item_lot     h reserve_v = field item_lot     h item_v
           \<and> field price_amount h reserve_v \<le> field price_limit  h order_v)
        1
        (\<lambda>h. {field party_broker h reserve_v})
  , match_any_when budget_v Budget
        (\<lambda>h. field party_broker h reserve_v = field party_broker h budget_v
           \<and> field party_buyer  h reserve_v = field party_buyer  h budget_v
           \<and> field price_amount h reserve_v \<le> field budget_remain h budget_v)
        1
        (\<lambda>h. {field party_broker h budget_v})
  ]
  (\<lambda>h. {#
    mk_Budget
          (field party_broker  h budget_v)
          (field party_buyer   h budget_v)
          (field budget_total  h budget_v)
          (field budget_remain h budget_v - field price_amount h reserve_v)
          {field party_broker  h budget_v}
          {}
  , mk_Bid
          (field item_lot     h item_v)
          (field party_broker h reserve_v)
          (field party_buyer  h order_v)
          (field price_amount h reserve_v)
          {field party_broker h reserve_v, field party_buyer h order_v}
          {party ''Mark''}
  #})"


section \<open>Invariants\<close>

definition facts_of_type :: "fact_ctor \<Rightarrow> Value store \<Rightarrow> Value store" where
"facts_of_type ctor s = {# f \<in># s. fact_name f = ctor #}"

definition "bids_for_budget s b =
  {# f \<in># facts_of_type Bid s.
    party_buyer  (fact_value f) = party_buyer  (fact_value b)
  \<and> party_broker (fact_value f) = party_broker (fact_value b) #}"

definition "invoices_for_budget s b =
  {# f \<in># facts_of_type Invoice s.
    party_buyer (fact_value f) = party_buyer (fact_value b)
  \<and> party_broker (fact_value f) = party_broker (fact_value b) #}"

definition "offers_for_budget s b =
  {# f \<in># facts_of_type Offer s.
    party_buyer (fact_value f) = party_buyer (fact_value b)
  \<and> party_broker (fact_value f) = party_broker (fact_value b) #}"

definition "budget_matches_order b order =
  (party_buyer (fact_value order) = party_buyer (fact_value b)
 \<and> party_broker (fact_value order) = party_broker (fact_value b))"
(* TODO: Budget is missing the description, so we only allow one order per buyer.
   We should add the restriction that budgets are specific to order descriptions *)

definition "budgets_for_order s order =
  {# b \<in># facts_of_type Budget s. budget_matches_order b order #}"

(* Invariant: a Budget is OK if the sum of its bids and invoices are less than the budget.
   The remaining must be the budget minus whatever has been committed in bids and invoices. *)
definition budget_ok :: "Value store \<Rightarrow> Value fact \<Rightarrow> bool" where
"budget_ok s b = 
    (let bids        = bids_for_budget s b
  in let invoices    = invoices_for_budget s b
  in let offers      = offers_for_budget s b
  in let sum_all = sum_mset (image_mset (price_amount o fact_value) bids)
                 + sum_mset (image_mset (price_amount o fact_value) invoices)
                 + sum_mset (image_mset (price_amount o fact_value) offers)
  in sum_all \<le> budget_total (fact_value b)
  \<and> budget_remain (fact_value b) = budget_total (fact_value b) - sum_all)"

(* Invariant: an Order is OK if all the budgets (there should only be one) are OK *)
definition order_ok :: "Value store \<Rightarrow> Value fact \<Rightarrow> bool" where
"order_ok s order = 
  ((size (budgets_for_order s order) \<le> 1) \<and>
  (\<forall> b \<in># budgets_for_order s order.
    budget_ok s b
  \<and> budget_total (fact_value b) = budget_total (fact_value order)))"

(* Invariant: a store is OK if all the orders are OK *)
definition store_ok :: "Value store \<Rightarrow> bool" where
"store_ok s = 
  (\<forall> order \<in># facts_of_type Order s. order_ok s order)"


(* Empty store is ok *)
lemma empty_store_ok: "store_ok {#}"
  by (simp add: facts_of_type_def store_ok_def)

(* Adding a new fact doesn't affect budgets *)
lemma budget_ok__add_irrelevant_fact:
    "budget_ok s b
 \<Longrightarrow> fact_name f \<noteq> Invoice
 \<Longrightarrow> fact_name f \<noteq> Bid
 \<Longrightarrow> fact_name f \<noteq> Offer
 \<Longrightarrow> budget_ok ({#f#} \<union># s) b"
  unfolding
    store_ok_def order_ok_def budget_ok_def
    facts_of_type_def bids_for_budget_def invoices_for_budget_def offers_for_budget_def budgets_for_order_def
    Invoice_def Bid_def Budget_def Order_def Offer_def
  by simp

lemma order_ok__add_irrelevant_fact:
    "order_ok s or
 \<Longrightarrow> fact_name f \<noteq> Invoice
 \<Longrightarrow> fact_name f \<noteq> Bid
 \<Longrightarrow> fact_name f \<noteq> Budget
 \<Longrightarrow> fact_name f \<noteq> Offer
 \<Longrightarrow> order_ok ({#f#} \<union># s) or"
  unfolding
    store_ok_def order_ok_def budget_ok_def
    facts_of_type_def bids_for_budget_def invoices_for_budget_def offers_for_budget_def budgets_for_order_def
    Invoice_def Bid_def Budget_def Order_def Offer_def
  by auto

lemma store_ok__add_irrelevant_fact:
    "store_ok s
 \<Longrightarrow> fact_name f \<noteq> Invoice
 \<Longrightarrow> fact_name f \<noteq> Bid
 \<Longrightarrow> fact_name f \<noteq> Budget
 \<Longrightarrow> fact_name f \<noteq> Order
 \<Longrightarrow> fact_name f \<noteq> Offer
 \<Longrightarrow> store_ok ({#f#} \<union># s)"
  unfolding
    store_ok_def order_ok_def budget_ok_def
    facts_of_type_def bids_for_budget_def invoices_for_budget_def offers_for_budget_def budgets_for_order_def
    Invoice_def Bid_def Budget_def Order_def Offer_def
  by force

(* The customer can add a new order that doesn't conflict with existing order *)
lemma store_ok__add_order:
    "store_ok s
 \<Longrightarrow> fact_name or = Order
 \<Longrightarrow> budgets_for_order s or = {#}
 \<Longrightarrow> store_ok ({#or#} \<union># s)"
  unfolding
    store_ok_def order_ok_def
    budgets_for_order_def facts_of_type_def
    Budget_def Order_def
  apply simp
  apply (intro conjI)
  using multi_member_split apply force
  by (simp add: Bid_def Invoice_def Offer_def budget_ok__add_irrelevant_fact)


(* The broker can add a new budget for which there are no pre-existing bids or invoices *)
lemma store_ok__add_budget:
    "store_ok s
 \<Longrightarrow> fact_name b = Budget
 \<Longrightarrow> budget_remain (fact_value b) = budget_total (fact_value b)
 \<Longrightarrow> bids_for_budget s b = {#}
 \<Longrightarrow> invoices_for_budget s b = {#}
 \<Longrightarrow> offers_for_budget s b = {#}
 \<Longrightarrow> (\<forall>or \<in># facts_of_type Order s. budget_matches_order b or \<longrightarrow> budgets_for_order s or = {#} \<and> budget_total (fact_value or) = budget_total (fact_value b))
 \<Longrightarrow> store_ok ({#b#} \<union># s)"
  unfolding store_ok_def order_ok_def budget_ok_def
    facts_of_type_def bids_for_budget_def invoices_for_budget_def offers_for_budget_def 
    budget_matches_order_def budgets_for_order_def facts_of_type_def
    Invoice_def Bid_def Budget_def Budget_def Order_def Offer_def
  apply simp
  apply (intro allI conjI impI)
  by (metis (no_types, lifting))+


lemma store_ok__add_budget:
  "store_ok (add_mset fb s) \<Longrightarrow>
   fc \<in># s \<Longrightarrow>
   fact_name fb = Bid \<Longrightarrow>
   fact_name fc = Item \<Longrightarrow>
   item_lot (fact_value fc) = item_lot (fact_value fb) \<Longrightarrow>
   price_amount (fact_value fb) \<le> price_amount (fact_value fc) \<Longrightarrow>
   store_ok
    (add_mset
      (mk_Offer (item_lot (fact_value fb)) (party_broker (fact_value fb)) (party_buyer (fact_value fb)) (price_amount (fact_value fb)) by obs)
      s)"
  unfolding store_ok_def order_ok_def budget_ok_def
    Invoice_def Bid_def Budget_def Budget_def Order_def Offer_def
  apply simp
  unfolding store_ok_def order_ok_def budget_ok_def
    facts_of_type_def bids_for_budget_def invoices_for_budget_def offers_for_budget_def 
    budget_matches_order_def budgets_for_order_def facts_of_type_def
    Invoice_def Bid_def Budget_def Budget_def Order_def Offer_def
    mk_Invoice_def mk_Bid_def mk_Budget_def mk_Budget_def mk_Order_def mk_Offer_def

  apply (simp only: Multiset.set_mset_filter
                    Multiset.sup_union_left1
                    Multiset.filter_mset_add_mset
                    Multiset.set_mset_sup
                    Set.mem_Collect_eq Set.ball_simps
                    Multiset.filter_sup_mset
                    HOL.conj_assoc
                    fact.simps Cancellation.iterate_add_distrib Multiset.repeat_mset_iterate_add Multiset.add_mset_replicate_mset_safe
                    fact_ctor.inject list.inject char.inject HOL.simp_thms if_False if_True
                     Set.Ball_def)
  apply (intro allI)
  apply (erule_tac x="x" in allE)
  apply simp
  apply (intro allI conjI impI; simp)
   apply (elim allE conjE impE; blast?)
   apply (simp add: add.assoc add.left_commute)
  apply (elim allE conjE impE; blast?)
  oops



lemma store_ok__auction_bid__ok:
    "store_ok s
 \<Longrightarrow> asub | s \<turnstile> auction_bid \<Down> fread | dspent | dnew | s' FIRE
 \<Longrightarrow> store_ok s'"
  oops

lemma store_ok__auction_accept__ok:
    "store_ok s
 \<Longrightarrow> asub | s \<turnstile> auction_accept \<Down> fread | dspent | dnew | s' FIRE
 \<Longrightarrow> store_ok s'"
  oops

lemma store_ok__broker_reserve__ok:
    "store_ok s
 \<Longrightarrow> asub | s \<turnstile> broker_reserve \<Down> fread | dspent | dnew | s' FIRE
 \<Longrightarrow> store_ok s'"
  oops
end