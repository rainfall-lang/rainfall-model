(* Dynamic semantics *)
theory Dynamic
  imports Main "HOL-Library.Multiset" "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools"
  Exp
begin

(* Get all the facts with a minimum value, according to some function *)
definition find_firsts :: "store \<Rightarrow> fact_env \<Rightarrow> fact_var \<Rightarrow> nat exp \<Rightarrow> store" where
"find_firsts fs env v x = (
       let score = (\<lambda>f. x (env (v := f)))
    in let v' = Min (score ` set_mset fs)
    in filter_mset (\<lambda>f. score f = v') fs)"

(* Dynamic semantics for select *)
inductive EvSelect :: "store \<Rightarrow> fact_env \<Rightarrow> fact_var \<Rightarrow> select \<Rightarrow> fact \<Rightarrow> bool" where
  EvAny: "f \<in># fs \<Longrightarrow> EvSelect fs _ _ select_any f"
 | EvFirst: "f \<in># find_firsts fs h v e \<Longrightarrow> EvSelect fs h v (select_first e) f"

definition can_see_fact :: "auth \<Rightarrow> fact \<Rightarrow> bool" where
"can_see_fact a f \<equiv> {} \<noteq> (a \<inter> (fact_by f \<union> fact_obs f))"

definition check_gather :: "auth \<Rightarrow> fact_env \<Rightarrow> fact_var \<Rightarrow> fact_ctor \<Rightarrow> bool exp \<Rightarrow> fact \<Rightarrow> bool" where
"check_gather Asub h v ctor pred f =
  (fact_name f = ctor \<and>
  can_see_fact Asub f \<and>
  pred (h(v := f)))"

inductive EvGather :: "auth \<Rightarrow> store \<Rightarrow> fact_env \<Rightarrow> fact_var \<Rightarrow> gather \<Rightarrow> store \<Rightarrow> bool" where
  EvGather: "fs = filter_mset (check_gather Asub h v ctor pred) s \<Longrightarrow> EvGather Asub s h v (gather_when ctor pred) fs"

inductive EvConsume :: "fact \<Rightarrow> store \<Rightarrow> fact_env \<Rightarrow> consume \<Rightarrow> nat \<Rightarrow> store \<Rightarrow> bool" where
  EvConsume: "w h = w_need \<Longrightarrow> count s f \<ge> w_need \<Longrightarrow> w_need > 0 \<Longrightarrow> s' = (s - replicate_mset w_need f) \<Longrightarrow> EvConsume f s h (consume_weight w) w_need s'"

inductive EvGain :: "fact \<Rightarrow> fact_env \<Rightarrow> gain \<Rightarrow> auth \<Rightarrow> bool" where
  EvGain: "t h = a \<Longrightarrow> a \<subseteq> fact_by f \<Longrightarrow> EvGain f h (gain_auth t) a"

inductive EvExec :: "fact_env \<Rightarrow> store exp \<Rightarrow> store \<Rightarrow> bool" where
  EvExec: "t h = s' \<Longrightarrow> EvExec h t s'"


inductive EvMatch :: "rule_name \<Rightarrow> auth \<Rightarrow> store \<Rightarrow> fact_env \<Rightarrow> match \<Rightarrow> auth \<Rightarrow> store \<Rightarrow> store \<Rightarrow> fact_env \<Rightarrow> bool" where
  EvMatch: "
    EvGather asub s h x gather fs \<Longrightarrow>
    EvSelect fs h x sel f \<Longrightarrow>
    h' = h(x := f) \<Longrightarrow>
    EvConsume f s h' con w s' \<Longrightarrow>
    EvGain f h' gain again \<Longrightarrow>
    rn \<in> fact_rules f \<Longrightarrow>
    fw = replicate_mset w f \<Longrightarrow>
    EvMatch rn asub s h (match x gather sel con gain) again fw s' h'"


inductive EvMatches :: "rule_name \<Rightarrow> auth \<Rightarrow> store \<Rightarrow> fact_env \<Rightarrow> match list \<Rightarrow> auth \<Rightarrow> store \<Rightarrow> fact_env \<Rightarrow> bool" where
  EvMatchNil: "EvMatches n a s h [] {} {#} h"
| EvMatchCons: "EvMatch n a s h m ag fw s' h' \<Longrightarrow>
    EvMatches n a s' h' ms ag' ds' h'' \<Longrightarrow>
    EvMatches n a s h (m # ms) (ag \<union> ag') (fw + ds') h''"

inductive EvFire :: "auth \<Rightarrow> store \<Rightarrow> rule \<Rightarrow> store \<Rightarrow> store \<Rightarrow> store \<Rightarrow> bool" where
  EvFire: "EvMatches rn asub s (\<lambda>_. undefined) matches ahas dspent h' \<Longrightarrow>
    EvExec h' say dnew \<Longrightarrow>
    s' = ((s - dspent) + dnew) \<Longrightarrow>
    (\<forall>f \<in># dnew. fact_by f \<subseteq> ahas) \<Longrightarrow>
    EvFire asub s (rule rn matches say) dspent dnew s'"

end