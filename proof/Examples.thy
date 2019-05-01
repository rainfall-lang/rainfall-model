(* Example programs and evaluations *)
theory Examples
  imports Dynamic
begin

section \<open>Coin transfer rule\<close>
(* This is the 'transfer' example from the paper.
   The rule is based on the desugared version from Figure 4 *)

definition "transfer_rn = rule_name ''transfer''"

(* Fact type payloads *)
record AcceptPayload =
  Accept_oid      :: nat
  Accept_accepter :: party

record OfferPayload =
  Offer_oid       :: nat
  Offer_terms     :: symbol
  Offer_giver     :: party
  Offer_receiver  :: party

record CoinPayload =
  Coin_issuer     :: party
  Coin_holder     :: party

declare AcceptPayload.make_def[simp]
declare OfferPayload.make_def[simp]
declare CoinPayload.make_def[simp]

datatype FactValue =
  AcceptV AcceptPayload | OfferV OfferPayload | CoinV CoinPayload

fun tk_AcceptV where
  "tk_AcceptV (AcceptV a) = a"
| "tk_AcceptV _           = undefined"
fun tk_OfferV where
  "tk_OfferV (OfferV a) = a"
| "tk_OfferV _          = undefined"
fun tk_CoinV where
  "tk_CoinV (CoinV a) = a"
| "tk_CoinV _         = undefined"


definition [simp]: "Accept = fact_ctor ''Accept''"
definition [simp]: "mk_Accept oid accepter by obs = \<lparr>fact_name = Accept, fact_value = AcceptV (AcceptPayload.make oid accepter), fact_by = by, fact_obs = obs, fact_rules = {transfer_rn}\<rparr>"
definition [simp]: "Offer  = fact_ctor ''Offer''"
definition [simp]: "mk_Offer oid terms giver receiver by obs = \<lparr>fact_name = Offer, fact_value = OfferV (OfferPayload.make oid terms giver receiver), fact_by = by, fact_obs = obs, fact_rules = {transfer_rn}\<rparr>"

definition [simp]: "Coin = fact_ctor ''Coin''"
definition [simp]: "mk_Coin issuer holder by obs = \<lparr>fact_name = Coin, fact_value = CoinV (CoinPayload.make issuer holder), fact_by = by, fact_obs = obs, fact_rules = {transfer_rn}\<rparr>"


(* Transfer rule *)
definition [simp]: "accept_v = fact_var ''accept''"
definition [simp]: "offer_v  = fact_var ''offer''"
definition [simp]: "coin_v   = fact_var ''coin''"

definition [simp]:
  "match_Accept = match
    accept_v
    (gather_when Accept (\<lambda>h. True))
    select_any
    (consume_weight (\<lambda>h. 1))
    (gain_auth (\<lambda>h. {Accept_accepter (tk_AcceptV (fact_value (h accept_v)))}))"

definition [simp]:
  "match_Offer = match
    offer_v
    (gather_when Offer
      (\<lambda>h. Accept_oid     (tk_AcceptV (fact_value (h accept_v))) = Offer_oid      (tk_OfferV (fact_value (h offer_v)))
        \<and> Accept_accepter (tk_AcceptV (fact_value (h accept_v))) = Offer_receiver (tk_OfferV (fact_value (h offer_v)))))
    select_any
    (consume_weight (\<lambda>h. 1))
    (gain_auth (\<lambda>h. {Offer_giver (tk_OfferV (fact_value (h offer_v)))}))"

definition [simp]:
  "match_Coin = match
    coin_v
    (gather_when Coin (\<lambda>h. Coin_holder (tk_CoinV (fact_value (h coin_v))) = Offer_giver (tk_OfferV (fact_value (h offer_v)))))
    select_any
    (consume_weight (\<lambda>h. 1))
    (gain_auth (\<lambda>h. {Coin_issuer (tk_CoinV (fact_value (h coin_v)))}))"

definition [simp]:
  "transfer_Say =
    (\<lambda>h. {# mk_Coin
              (Coin_issuer    (tk_CoinV (fact_value (h coin_v))))
              (Offer_receiver (tk_OfferV (fact_value (h offer_v))))
              {Coin_issuer    (tk_CoinV (fact_value (h coin_v))), Offer_receiver (tk_OfferV (fact_value (h offer_v)))}
              (fact_obs (h coin_v))
         #})"

definition [simp]:
  "transfer = rule transfer_rn [match_Accept, match_Offer, match_Coin] transfer_Say"

subsection \<open>Coin transfer scenario\<close>

(* The guitar purchase example from S2.1 *)
definition [simp]: "Alice    = party ''Alice''"
definition [simp]: "Bob      = party ''Bob''"
definition [simp]: "Mona     = party ''Mona''"
definition [simp]: "Isabelle = party ''Isabelle''"
definition [simp]: "oid      = (1234 :: nat)"
definition [simp]: "terms    = symbol ''To purchase a guitar''"

definition [simp]:
 "store0 = {#
    mk_Offer  oid terms Alice Bob {Alice}           {Mona, Bob},
    mk_Accept oid       Bob       {Bob}             {Mona, Alice},
    mk_Coin   Isabelle  Alice     {Isabelle, Alice} {Mona}
  #}"

definition [simp]:
 "store1 = {#
    mk_Coin   Isabelle  Bob       {Isabelle, Bob} {Mona}
  #}"

(* If we have an offer, acceptance and a coin, we can transfer the coin to the seller. *)
lemma "{Alice} | store0 \<turnstile> transfer \<Down> store0 | store0 | store1 | store1 FIRE"
  apply simp
  apply (intro EvFire.intros; simp?)
    apply (rule EvMatches.intros; simp?)
       apply (intro EvMatch.intros EvGather.intros EvConsume.intros EvSelect.intros EvGain.intros; (simp add: check_gather_def can_see_fact_def)?; simp?; simp?)
      apply (rule EvMatches.intros; simp?)
       apply (intro EvMatch.intros EvGather.intros EvConsume.intros EvSelect.intros EvGain.intros; (simp add: check_gather_def can_see_fact_def)?; simp?; simp?)
      apply (rule EvMatches.intros; simp?)
       apply (intro EvMatch.intros EvGather.intros EvConsume.intros EvSelect.intros EvGain.intros; (simp add: check_gather_def can_see_fact_def)?; simp?; simp?)
      apply (rule EvMatches.intros; simp?)
     apply simp
    apply simp
   apply (intro EvExec.intros)
   apply simp
  apply simp
  done


section \<open>Test find_firsts\<close>
(* A small test to make sure the 'minimum' in find_firsts works as expected *)

definition mk_vfact :: "string \<Rightarrow> nat \<Rightarrow> nat fact" where
  "mk_vfact nm v = \<lparr>fact_name=fact_ctor ''fact'', fact_value = v, fact_by = {party nm}, fact_obs = {}, fact_rules = {}\<rparr>"

definition facts where
  "facts = {# mk_vfact ''alice'' 0, mk_vfact ''bob'' 1, mk_vfact ''charlie'' 0#}"

definition get_fact_score where
  "get_fact_score = (\<lambda>s. fact_value (s (fact_var ''x'')))"

lemma "find_firsts facts (\<lambda>_. undefined) (fact_var ''x'') get_fact_score
    = {# mk_vfact ''alice'' 0, mk_vfact ''charlie'' 0 #}"
  by eval

end