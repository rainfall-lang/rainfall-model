(* Example programs and evaluations *)
theory Examples
  imports Dynamic
begin

section \<open>Coin transfer rule\<close>

definition "transfer_rn = rule_name ''transfer''"

(* Accept facts: constructor and accessor functions *)
definition mk_AcceptPayload where
  "mk_AcceptPayload oid accepter = vpair (vlit (lnat oid)) (vlit (lparty accepter))"

fun tk_AcceptPayload where
  "tk_AcceptPayload (vpair (vlit (lnat oid)) (vlit (lparty accepter))) = (oid, accepter)"
| "tk_AcceptPayload _ = undefined"

definition "Accept_oid      = fst o tk_AcceptPayload o fact_value"
definition "Accept_accepter = snd o tk_AcceptPayload o fact_value"

definition "Accept = fact_ctor ''Accept''"
definition "mk_Accept oid accepter by obs = \<lparr>fact_name = Accept, fact_value = mk_AcceptPayload oid accepter, fact_by = by, fact_obs = obs, fact_rules = {transfer_rn}\<rparr>"

(* Offer facts *)
definition mk_OfferPayload where
  "mk_OfferPayload oid terms giver receiver = vpair (vlit (lnat oid)) (vpair (vlit (lsymbol terms)) (vpair (vlit (lparty giver)) (vlit (lparty receiver))))"

fun tk_OfferPayload where
  "tk_OfferPayload (vpair (vlit (lnat oid)) (vpair (vlit (lsymbol terms)) (vpair (vlit (lparty giver)) (vlit (lparty receiver))))) = (oid, terms, giver, receiver)"
| "tk_OfferPayload _ = undefined"

definition "Offer_oid      =             fst o tk_OfferPayload o fact_value"
definition "Offer_terms    =       fst o snd o tk_OfferPayload o fact_value"
definition "Offer_giver    = fst o snd o snd o tk_OfferPayload o fact_value"
definition "Offer_receiver = snd o snd o snd o tk_OfferPayload o fact_value"

definition "Offer  = fact_ctor ''Offer''"
definition "mk_Offer oid terms giver receiver by obs = \<lparr>fact_name = Offer, fact_value = mk_OfferPayload oid terms giver receiver, fact_by = by, fact_obs = obs, fact_rules = {transfer_rn}\<rparr>"

(* Coin facts *)
definition mk_CoinPayload where
  "mk_CoinPayload issuer holder = vpair (vlit (lparty issuer)) (vlit (lparty holder))"

fun tk_CoinPayload where
  "tk_CoinPayload (vpair (vlit (lparty issuer)) (vlit (lparty holder))) = (issuer, holder)"
| "tk_CoinPayload _ = undefined"

definition "Coin_issuer = fst o tk_CoinPayload o fact_value"
definition "Coin_holder = snd o tk_CoinPayload o fact_value"

definition "Coin = fact_ctor ''Coin''"
definition "mk_Coin issuer holder by obs = \<lparr>fact_name = Coin, fact_value = mk_CoinPayload issuer holder, fact_by = by, fact_obs = obs, fact_rules = {transfer_rn}\<rparr>"

(* Transfer rule *)
definition "accept_v = fact_var ''accept''"
definition "offer_v  = fact_var ''offer''"
definition "coin_v   = fact_var ''coin''"

definition
  "match_Accept = match
    accept_v
    (gather_when Accept (\<lambda>h. True))
    select_any
    (consume_weight (\<lambda>h. 1))
    (gain_auth (\<lambda>h. {Accept_accepter (h accept_v)}))"

definition
  "match_Offer = match
    offer_v
    (gather_when Offer
      (\<lambda>h. Accept_oid     (h accept_v) = Offer_oid      (h offer_v)
        \<and> Accept_accepter (h accept_v) = Offer_receiver (h offer_v)))
    select_any
    (consume_weight (\<lambda>h. 1))
    (gain_auth (\<lambda>h. {Offer_giver (h offer_v)}))"

definition
  "match_Coin = match
    coin_v
    (gather_when Coin (\<lambda>h. Coin_holder (h coin_v) = Offer_giver (h offer_v)))
    select_any
    (consume_weight (\<lambda>h. 1))
    (gain_auth (\<lambda>h. {Coin_issuer (h coin_v)}))"

definition
  "transfer_Say =
    (\<lambda>h. {# mk_Coin
              (Coin_issuer    (h coin_v))
              (Offer_receiver (h offer_v))
              {Coin_issuer    (h coin_v), Offer_receiver (h offer_v)}
              (fact_obs (h coin_v))
         #})"

definition
  "transfer = rule transfer_rn [match_Accept, match_Offer, match_Coin] transfer_Say"

subsection \<open>Coin transfer scenario\<close>

definition "Alice    = party ''Alice''"
definition "Bob      = party ''Bob''"
definition "Mona     = party ''Mona''"
definition "Isabelle = party ''Isabelle''"
definition "oid      = (1234 :: nat)"
definition "terms    = symbol ''To purchase a guitar''"

definition "store0 = {#
    mk_Offer  oid terms Alice Bob {Bob}             {Mona, Alice},
    mk_Accept oid       Bob       {Alice}           {Mona, Bob},
    mk_Coin   Isabelle  Alice     {Isabelle, Alice} {Mona}
  #}"

definition "store1 = {#
    mk_Coin   Isabelle  Bob       {Isabelle, Bob} {Mona}
  #}"

(*
lemma "{Alice} | store0 \<turnstile> transfer \<Down> {#} | store1 | store0 | store1 FIRE"
  unfolding transfer_def match_Accept_def match_Offer_def match_Coin_def accept_v_def offer_v_def coin_v_def store0_def store1_def transfer_Say_def
  apply (intro EvFire.intros EvExec.intros; simp?)
  apply simp
  apply (intro EvMatch.intros)
  sledgehammer
*)

section \<open>Test find_firsts\<close>
(* A small test to make sure the 'minimum' in find_firsts works as expected *)

definition mk_vfact :: "string \<Rightarrow> val \<Rightarrow> fact" where
  "mk_vfact nm v = \<lparr>fact_name=fact_ctor ''fact'', fact_value = v, fact_by = {party nm}, fact_obs = {}, fact_rules = {}\<rparr>"

definition vnat :: "nat \<Rightarrow> val" where
  "vnat i = vlit (lnat i)"

definition facts where
  "facts = {# mk_vfact ''alice'' (vnat 0), mk_vfact ''bob'' (vnat 1), mk_vfact ''charlie'' (vnat 0)#}"

definition get_fact_score where
  "get_fact_score = (\<lambda>s. case fact_value (s (fact_var ''x'')) of vlit (lnat i) \<Rightarrow> i)"

lemma "find_firsts facts (\<lambda>_. undefined) (fact_var ''x'') get_fact_score
    = {# mk_vfact ''alice'' (vnat 0), mk_vfact ''charlie'' (vnat 0) #}"
  by eval

end