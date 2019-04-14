(* Sketch of rainfall with HOAS, simplified values *)
(* very rough, just to make sure I understand the semantics *)
theory Rainfall0
  imports Main "HOL-Library.Multiset" "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools"
begin

datatype party = party string
type_synonym auth = "party set"

datatype symbol = symbol string
datatype label = label string
datatype ctor_name = ctor_name string
datatype rule_name = rule_name string
datatype fact_var = fact_var string

(* Literals and values - these are just uninterpreted stuff to put in a fact *)
datatype lit =
    lnat nat
  | lbool bool
  | lunit
  | lparty party
  | lauth auth
  | lsymbol symbol
  | lrule rule_name

datatype val =
    vlit lit
  | vrecord "(label \<times> val) list"
  | vlist "val list"

record fact =
  fact_ctor :: ctor_name
  fact_value :: val
  fact_by :: auth
  fact_obs :: auth
  fact_rules :: "rule_name set"

(* HOAS for terms *)
type_synonym fact_env = "fact_var \<Rightarrow> fact"
type_synonym 'a trm = "fact_env \<Rightarrow> 'a"

(* Definitions of rules *)
(* gather should have list of terms - ignore for now *)
datatype gather = gather_when ctor_name "bool trm"
datatype select = select_any | select_first "nat trm"
(* ignore consume/retain for now *)
datatype consume = consume_weight "nat trm"
datatype gain = gain_auth "auth trm"

datatype match = match fact_var gather select consume gain

type_synonym store = "fact multiset"

(* ignore 'say' and factoids for now - just allow returning list of facts in term *)
datatype rule = rule rule_name "match list" "store trm"

(* Get all the facts with a minimum value, according to some function *)
definition find_firsts :: "store \<Rightarrow> fact_env \<Rightarrow> fact_var \<Rightarrow> nat trm \<Rightarrow> store" where
"find_firsts fs env v x = (
       let score = (\<lambda>f. x (env (v := f)))
    in let v' = Min (score ` set_mset fs)
    in filter_mset (\<lambda>f. score f = v') fs)"

lemma find_firsts_in_store: "f \<in># find_firsts s h v e \<Longrightarrow> f \<in># s"
  by (auto simp add: find_firsts_def)
lemma find_firsts_subset: "find_firsts s h v e \<subseteq># s"
  by (auto simp add: find_firsts_def)

lemma min_subset_min_finite: "finite xs \<Longrightarrow> f x = Min (f ` xs) \<Longrightarrow> xs' \<subseteq> xs \<Longrightarrow> x \<in> xs' \<Longrightarrow> f x = Min (f ` xs')"
(* TODO smt *)
  apply (rule_tac V="finite xs'" in revcut_rl)
  using finite_subset apply blast
  by (smt Min_eqI Min_le finite_imageI imageE image_eqI subsetCE)


lemma find_firsts_min_in_subset: "f \<in># find_firsts s h v e \<Longrightarrow> s' \<subseteq># s \<Longrightarrow> f \<in># s' \<Longrightarrow> f \<in># find_firsts s' h v e"
  apply (clarsimp simp add: find_firsts_def)
  using min_subset_min_finite
  by (metis set_mset_mono finite_set_mset)


(* Examples to make sure find_firsts works *)
definition mk_vfact :: "string \<Rightarrow> val \<Rightarrow> fact" where
"mk_vfact nm v = \<lparr>fact_ctor=ctor_name ''fact'', fact_value = v, fact_by = {party nm}, fact_obs = {}, fact_rules = {}\<rparr>"

definition vnat :: "nat \<Rightarrow> val" where
"vnat i = vlit (lnat i)"

lemma "find_firsts {# mk_vfact ''alice'' (vnat 0), mk_vfact ''bob'' (vnat 1), mk_vfact ''charlie'' (vnat 0)#}
   (\<lambda>_. undefined) (fact_var ''x'') (\<lambda>s. case fact_value (s (fact_var ''x'')) of vlit (lnat i) \<Rightarrow> i)
= {# \<lparr>fact_ctor = ctor_name ''fact'', fact_value = vlit (lnat 0), fact_by = {party ''alice''}, fact_obs = {}, fact_rules = {}\<rparr>,
  \<lparr>fact_ctor = ctor_name ''fact'', fact_value = vlit (lnat 0), fact_by = {party ''charlie''}, fact_obs = {},
     fact_rules = {}\<rparr>
  #}"
  by eval


(* Dynamic semantics for select *)
inductive EvSelect :: "store \<Rightarrow> fact_env \<Rightarrow> fact_var \<Rightarrow> select \<Rightarrow> fact \<Rightarrow> bool" where
  EvAny: "f \<in># fs \<Longrightarrow> EvSelect fs _ _ select_any f"
 | EvFirst: "f \<in># find_firsts fs h v e \<Longrightarrow> EvSelect fs h v (select_first e) f"

definition can_see_fact :: "auth \<Rightarrow> fact \<Rightarrow> bool" where
"can_see_fact a f \<equiv> {} \<noteq> (a \<inter> (fact_by f \<union> fact_obs f))"

definition check_gather :: "auth \<Rightarrow> fact_env \<Rightarrow> fact_var \<Rightarrow> ctor_name \<Rightarrow> bool trm \<Rightarrow> fact \<Rightarrow> bool" where
"check_gather Asub h v ctor pred f =
  (fact_ctor f = ctor \<and>
  can_see_fact Asub f \<and>
  pred (h(v := f)) = True)"

inductive EvGather :: "auth \<Rightarrow> store \<Rightarrow> fact_env \<Rightarrow> fact_var \<Rightarrow> gather \<Rightarrow> store \<Rightarrow> bool" where
  EvGather: "fs = filter_mset (check_gather Asub h v ctor pred) s \<Longrightarrow> EvGather Asub s h v (gather_when ctor pred) fs"

inductive EvConsume :: "fact \<Rightarrow> store \<Rightarrow> fact_env \<Rightarrow> consume \<Rightarrow> nat \<Rightarrow> store \<Rightarrow> bool" where
  EvConsume: "w h = w_need \<Longrightarrow> count s f \<ge> w_need \<Longrightarrow> w_need > 0 \<Longrightarrow> s' = (s - replicate_mset w_need f) \<Longrightarrow> EvConsume f s h (consume_weight w) w_need s'"

inductive EvGain :: "fact \<Rightarrow> fact_env \<Rightarrow> gain \<Rightarrow> auth \<Rightarrow> bool" where
  EvGain: "t h = a \<Longrightarrow> a \<subseteq> fact_by f \<Longrightarrow> EvGain f h (gain_auth t) a"

inductive EvExec :: "fact_env \<Rightarrow> store trm \<Rightarrow> store \<Rightarrow> bool" where
  EvExec: "t h = s' \<Longrightarrow> EvExec h t s'"


inductive EvMatch :: "rule_name \<Rightarrow> auth \<Rightarrow> store \<Rightarrow> fact_env \<Rightarrow> match \<Rightarrow> auth \<Rightarrow> store \<Rightarrow> store \<Rightarrow> fact_env \<Rightarrow> bool" where
  EvMatch: "
    EvGather asub s h x gather fs \<Longrightarrow>
    EvSelect fs h x sel f \<Longrightarrow>
    h' = h(x := vfact f) \<Longrightarrow>
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
    EvFire asub s (rule rn matches say) dspent dnew s'"

method elim_Ev = (elim EvFire.cases EvMatch.cases EvGather.cases EvSelect.cases EvConsume.cases EvGain.cases; clarsimp)
method intro_Ev = (intro EvMatches.intros EvMatch.intros EvGain.intros EvGather.intros EvSelect.intros EvConsume.intros)

(* trivial *)
lemma EvFire_new_is_added:
  "EvFire asub store rul dspent dnew store' \<Longrightarrow>
   dnew \<subseteq># store'"
  by elim_Ev

(* We only spend what we have - trivial *)
lemma EvMatches_spent_is_subset:
  "EvMatches rn asub store h matches ahas dspent h' \<Longrightarrow>
  dspent \<subseteq># store"
proof (induct rule: EvMatches.induct)
  case (EvMatchNil n a s h)
  then show ?case by auto
next
  case (EvMatchCons n a s h m ag fw s' h' ms ag' ds' h'')
  then show ?case
    apply elim_Ev
    by (simp add: add.commute count_le_replicate_mset_subset_eq subset_mset.le_diff_conv2)+
qed

lemma EvFire_spent_is_subset:
  "EvFire asub store rul dspent dnew store' \<Longrightarrow>
   dspent \<subseteq># store"
  apply (elim EvFire.cases; clarsimp)
  using EvMatches_spent_is_subset
  by simp

(* We only use what we spend *)
lemma frame_constriction_EvMatches:
  "EvMatches rn asub store h matches ahas dspent h' \<Longrightarrow>
   EvMatches rn asub dspent h matches ahas dspent h'"
proof (induct rule: EvMatches.induct)
  case (EvMatchNil n a s h)
  then show ?case
    using EvMatches.intros by simp
next
  case (EvMatchCons n a s h m ag fw s' h' ms ag' ds' h'')
  moreover have spent_smaller: "ds' \<subseteq># s'"
    using EvMatchCons EvMatches_spent_is_subset by auto
  ultimately show ?case
    apply elim_Ev
    apply (intro_Ev; (rule refl)?; simp)
    using EvMatchCons.hyps
     apply blast

    apply (intro_Ev; (rule refl)?; simp)
         apply (rule find_firsts_min_in_subset)
       apply assumption
      apply (metis add.commute count_le_replicate_mset_subset_eq filter_union_mset multiset_filter_mono subset_mset.le_diff_conv2)
     apply (metis count_filter_mset count_greater_zero_iff count_replicate_mset find_firsts_in_store union_iff)
    using EvMatchCons.hyps
     apply blast
    done
qed

lemma frame_constriction:
  "EvFire asub store rul dspent dnew store' \<Longrightarrow>
   EvFire asub dspent rul dspent dnew dnew"
  apply elim_Ev
  using frame_constriction_EvMatches EvFire.intros
  by fastforce

(* We only spend visible facts *)
lemma spend_only_accessible_EvMatches:
  "EvMatches rn asub store h matches ahas dspent h' \<Longrightarrow>
   (\<forall>f \<in># dspent. can_see_fact asub f)"
proof (induct rule: EvMatches.induct)
  case (EvMatchNil n a s h)
  then show ?case by simp
next
  case (EvMatchCons n a s h m ag fw s' h' ms ag' ds' h'')
  then show ?case
    apply elim_Ev
    using check_gather_def
     apply blast
    using check_gather_def find_firsts_in_store
    by (metis count_greater_zero_iff filter_mset.rep_eq neq0_conv)
qed

lemma spend_only_accessible:
  "EvFire asub store rul dspent dnew store' \<Longrightarrow>
   (\<forall>f \<in># dspent. can_see_fact asub f)"
  apply elim_Ev
  using spend_only_accessible_EvMatches by blast


(* We can always add new facts if they're not visible *)
lemma store_weaken_inaccessible_EvMatches:
  "EvMatches rn asub store h matches ahas dspent h' \<Longrightarrow>
   (\<forall>f \<in># others. \<not>(can_see_fact asub f)) \<Longrightarrow>
   EvMatches rn asub (store + others) h matches ahas dspent h'"
proof (induct rule: EvMatches.induct)
  case (EvMatchNil n a s h)
  then show ?case
    using EvMatches.EvMatchNil by blast
next
  case (EvMatchCons n a s h m ag fw s' h' ms ag' ds' h'')
  then show ?case
    apply elim_Ev
    apply (intro_Ev; (rule refl)?; simp?)
     apply (metis (no_types, lifting) EvMatchCons.hyps(3) add.commute add.left_commute add_diff_cancel_left' count_le_replicate_mset_subset_eq subset_mset.add_diff_inverse)
    (* SORRY: select_first case *)
    sorry
(*    by (metis (no_types, lifting) EvMatchCons.hyps(3) add.commute add.left_commute add_diff_cancel_left' count_le_replicate_mset_subset_eq subset_mset.add_diff_inverse)*)
qed


lemma store_weaken_inaccessible:
  "EvFire asub store rul dspent dnew store' \<Longrightarrow>
   (\<forall>f \<in># others. \<not>(can_see_fact asub f)) \<Longrightarrow>
   EvFire asub (store + others) rul dspent dnew (store' + others)"
  apply elim_Ev
  apply (intro EvFire.intros)
  using store_weaken_inaccessible_EvMatches apply blast
  apply blast
  using EvMatches_spent_is_subset by fastforce

(* auth of new facts is subset of auth of all spent facts *)
lemma new_auth_gained_from_spent:
  "EvFire asub store rul dspent dnew store' \<Longrightarrow>
   (\<forall>f \<in># dnew. fact_by f \<subseteq> {a. \<forall>d \<in># dspent. a \<in> fact_by d})"
  oops

(* Question: what do we know about observer sets (fact_obs)? *)

fun rule_only_any :: "rule \<Rightarrow> bool" where
"rule_only_any (rule _ matches _) = list_all (\<lambda>m. case m of match x gath sel con gain \<Rightarrow> sel = select_any) matches"

(* More permissions never stops a program from running *)
(* This probably isn't true for 'first' selectors, where adding more permissions could make a new minimum visible *)
(* But if the program only contains any selectors, it is true *)
lemma auth_weaken:
  "EvFire asub store rul dspent dnew store' \<Longrightarrow>
    rule_only_any rul \<Longrightarrow>
   EvFire (asub \<union> others) store rul dspent dnew store'"
  oops

(* We can always add new facts if the program only contains 'any' selectors *)
lemma store_weaken_if_any:
  "EvFire asub store rul dspent dnew store' \<Longrightarrow>
   rule_only_any rul \<Longrightarrow>
   EvFire asub (store \<union># others) rul dspent dnew store'"
  oops

end