(* Example programs and evaluations *)
theory Examples
  imports Dynamic
begin

section \<open>Coin transfer rule\<close>
(* This is the 'transfer' example from the paper.
   The rule is based on the desugared version from Figure 4 *)

definition "transfer_rn = rule_name ''transfer''"

(* Accept facts: constructor and accessor functions *)
(* Put everything in the simpset using [simp], because we don't want to have to manually unfold it later *)
definition mk_AcceptPayload where [simp]:
  "mk_AcceptPayload oid accepter = vpair (vlit (lnat oid)) (vlit (lparty accepter))"

fun tk_AcceptPayload where
  "tk_AcceptPayload (vpair (vlit (lnat oid)) (vlit (lparty accepter))) = (oid, accepter)"
| "tk_AcceptPayload _ = undefined"

definition [simp]: "Accept_oid      = fst o tk_AcceptPayload o fact_value"
definition [simp]: "Accept_accepter = snd o tk_AcceptPayload o fact_value"

definition [simp]: "Accept = fact_ctor ''Accept''"
definition [simp]: "mk_Accept oid accepter by obs = \<lparr>fact_name = Accept, fact_value = mk_AcceptPayload oid accepter, fact_by = by, fact_obs = obs, fact_rules = {transfer_rn}\<rparr>"

(* Offer facts *)
definition mk_OfferPayload where [simp]:
  "mk_OfferPayload oid terms giver receiver = vpair (vlit (lnat oid)) (vpair (vlit (lsymbol terms)) (vpair (vlit (lparty giver)) (vlit (lparty receiver))))"

fun tk_OfferPayload where
  "tk_OfferPayload (vpair (vlit (lnat oid)) (vpair (vlit (lsymbol terms)) (vpair (vlit (lparty giver)) (vlit (lparty receiver))))) = (oid, terms, giver, receiver)"
| "tk_OfferPayload _ = undefined"

definition [simp]: "Offer_oid      =             fst o tk_OfferPayload o fact_value"
definition [simp]: "Offer_terms    =       fst o snd o tk_OfferPayload o fact_value"
definition [simp]: "Offer_giver    = fst o snd o snd o tk_OfferPayload o fact_value"
definition [simp]: "Offer_receiver = snd o snd o snd o tk_OfferPayload o fact_value"

definition [simp]: "Offer  = fact_ctor ''Offer''"
definition [simp]: "mk_Offer oid terms giver receiver by obs = \<lparr>fact_name = Offer, fact_value = mk_OfferPayload oid terms giver receiver, fact_by = by, fact_obs = obs, fact_rules = {transfer_rn}\<rparr>"

(* Coin facts *)
definition mk_CoinPayload where [simp]:
  "mk_CoinPayload issuer holder = vpair (vlit (lparty issuer)) (vlit (lparty holder))"

fun tk_CoinPayload where
  "tk_CoinPayload (vpair (vlit (lparty issuer)) (vlit (lparty holder))) = (issuer, holder)"
| "tk_CoinPayload _ = undefined"

definition [simp]: "Coin_issuer = fst o tk_CoinPayload o fact_value"
definition [simp]: "Coin_holder = snd o tk_CoinPayload o fact_value"

definition [simp]: "Coin = fact_ctor ''Coin''"
definition [simp]: "mk_Coin issuer holder by obs = \<lparr>fact_name = Coin, fact_value = mk_CoinPayload issuer holder, fact_by = by, fact_obs = obs, fact_rules = {transfer_rn}\<rparr>"

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
    (gain_auth (\<lambda>h. {Accept_accepter (h accept_v)}))"

definition [simp]:
  "match_Offer = match
    offer_v
    (gather_when Offer
      (\<lambda>h. Accept_oid     (h accept_v) = Offer_oid      (h offer_v)
        \<and> Accept_accepter (h accept_v) = Offer_receiver (h offer_v)))
    select_any
    (consume_weight (\<lambda>h. 1))
    (gain_auth (\<lambda>h. {Offer_giver (h offer_v)}))"

definition [simp]:
  "match_Coin = match
    coin_v
    (gather_when Coin (\<lambda>h. Coin_holder (h coin_v) = Offer_giver (h offer_v)))
    select_any
    (consume_weight (\<lambda>h. 1))
    (gain_auth (\<lambda>h. {Coin_issuer (h coin_v)}))"

definition [simp]:
  "transfer_Say =
    (\<lambda>h. {# mk_Coin
              (Coin_issuer    (h coin_v))
              (Offer_receiver (h offer_v))
              {Coin_issuer    (h coin_v), Offer_receiver (h offer_v)}
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