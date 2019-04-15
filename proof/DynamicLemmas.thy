(* Proofs about the dynamic semantics *)
theory DynamicLemmas
  imports Main "HOL-Library.Multiset" "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools"
  Dynamic
begin


lemma find_firsts_in_store: "f \<in># find_firsts s h v e \<Longrightarrow> f \<in># s"
  by (auto simp add: find_firsts_def)
lemma find_firsts_subset: "find_firsts s h v e \<subseteq># s"
  by (auto simp add: find_firsts_def)

lemma min_subset_min_finite:
  assumes "finite xs"
      and "f x = Min (f ` xs)"
      and "xs' \<subseteq> xs"
      and "x \<in> xs'"
    shows "f x = Min (f ` xs')"
proof -
  have fin_all: "finite (f ` xs')"
    using assms finite_subset finite_imageI by blast+
  have x_min_xs': "\<forall>y \<in> xs'. f x \<le> f y"
    using assms fin_all by auto
  have fx_in_xs': "f x \<in> f ` xs'"
    using assms by blast
  have f_reverse: "\<forall>fx'. (\<exists>x'. x' \<in> xs' \<and> f x' = fx') \<or> fx' \<notin> f ` xs'"
    by blast
  show "f x = Min (f ` xs')"
    using fin_all fx_in_xs' x_min_xs' f_reverse
    by (metis (no_types) Min_eqI)
qed


lemma find_firsts_min_in_subset: "f \<in># find_firsts s h v e \<Longrightarrow> s' \<subseteq># s \<Longrightarrow> f \<in># s' \<Longrightarrow> f \<in># find_firsts s' h v e"
  apply (clarsimp simp add: find_firsts_def)
  using min_subset_min_finite
  by (metis set_mset_mono finite_set_mset)


method elim_Ev = (elim EvFire.cases EvMatch.cases EvGather.cases EvSelect.cases EvConsume.cases EvGain.cases; clarsimp)
method intro_Ev = (intro EvMatches.intros EvMatch.intros EvGain.intros EvGather.intros EvSelect.intros EvConsume.intros)

(* trivial *)
lemma EvFire_new_is_added:
  "asub | store \<turnstile> rul \<Down> dspent | dnew | store' FIRE \<Longrightarrow>
   dnew \<subseteq># store'"
  by elim_Ev

(* We only spend what we have - trivial *)
lemma EvMatches_spent_is_subset:
  "rn | asub | store | h \<turnstile> matches \<Down> ahas | dspent | h' MATCHES \<Longrightarrow>
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
  "asub | store \<turnstile> rul \<Down> dspent | dnew | store' FIRE \<Longrightarrow>
   dspent \<subseteq># store"
  apply (elim EvFire.cases; clarsimp)
  using EvMatches_spent_is_subset
  by simp

(* We only use what we spend *)
lemma frame_constriction_EvMatches:
  "rn | asub | store  | h \<turnstile> matches \<Down> ahas | dspent | h' MATCHES \<Longrightarrow>
   rn | asub | dspent | h \<turnstile> matches \<Down> ahas | dspent | h' MATCHES"
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
  "asub | store  \<turnstile> rul \<Down> dspent | dnew | store' FIRE \<Longrightarrow>
   asub | dspent \<turnstile> rul \<Down> dspent | dnew | dnew   FIRE"
  apply elim_Ev
  using frame_constriction_EvMatches EvFire.intros
  by fastforce

(* We only spend visible facts *)
lemma spend_only_accessible_EvMatches:
  "rn | asub | store  | h \<turnstile> matches \<Down> ahas | dspent | h' MATCHES  \<Longrightarrow>
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
  "asub | store \<turnstile> rul \<Down> dspent | dnew | store' FIRE \<Longrightarrow>
   (\<forall>f \<in># dspent. can_see_fact asub f)"
  apply elim_Ev
  using spend_only_accessible_EvMatches by blast

lemma check_gather_inaccessible_empty:
  " (\<forall>f \<in># others. \<not>(can_see_fact asub f)) \<Longrightarrow>
  filter_mset (check_gather asub env v ctor pred) others = {#}"
  apply (unfold check_gather_def)
  using set_mset_eq_empty_iff by fastforce

(* We can always add new facts if they're not visible *)
lemma store_weaken_inaccessible_EvMatches:
  "rn | asub | store            | h \<turnstile> matches \<Down> ahas | dspent | h' MATCHES  \<Longrightarrow>
   (\<forall>f \<in># others. \<not>(can_see_fact asub f)) \<Longrightarrow>
   rn | asub | (store + others) | h \<turnstile> matches \<Down> ahas | dspent | h' MATCHES"
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
    apply (intro_Ev; (rule refl)?; simp?)
     apply (subst check_gather_inaccessible_empty[where others=others]; simp)
    by (metis EvMatchCons.hyps(3) count_le_replicate_mset_subset_eq subset_mset.add_diff_assoc2)
qed

lemma store_weaken_inaccessible:
  "asub |  store           \<turnstile> rul \<Down> dspent | dnew |  store'           FIRE \<Longrightarrow>
   (\<forall>f \<in># others. \<not>(can_see_fact asub f)) \<Longrightarrow>
   asub | (store + others) \<turnstile> rul \<Down> dspent | dnew | (store' + others) FIRE"
  apply elim_Ev
  apply (intro EvFire.intros)
  using store_weaken_inaccessible_EvMatches apply blast
  apply blast
  using EvMatches_spent_is_subset by fastforce


(* auth of new facts is subset of auth of all spent facts *)
lemma new_auth_gained_from_spent_EvMatches:
  "rn | asub | store | h \<turnstile> matches \<Down> ahas | dspent | h' MATCHES  \<Longrightarrow>
  \<forall>a \<in> ahas. \<exists>d \<in># dspent. a \<in> fact_by d"
(* ahas \<subseteq> \<Union>(fact_by ` set_mset dspent) *)
proof (induct rule: EvMatches.induct)
  case (EvMatchNil n a s h)
  then show ?case by simp
next
  case (EvMatchCons n a s h m ag fw s' h' ms ag' ds' h'')
  then show ?case
    by (elim_Ev; blast)
qed


lemma new_auth_gained_from_spent:
  "asub | store \<turnstile> rul \<Down> dspent | dnew | store' FIRE \<Longrightarrow>
  \<forall>f \<in># dnew. \<forall>a \<in> fact_by f. \<exists>d \<in># dspent. a \<in> fact_by d"
  apply elim_Ev
  using new_auth_gained_from_spent_EvMatches
  by blast


(* Question: what do we know about observer sets (fact_obs)? *)

fun rule_only_any :: "rule \<Rightarrow> bool" where
"rule_only_any (rule _ matches _) = list_all (\<lambda>m. case m of match x gath sel con gain \<Rightarrow> sel = select_any) matches"

(* More permissions never stops a program from running *)
(* This probably isn't true for 'first' selectors, where adding more permissions could make a new minimum visible *)
(* But if the program only contains any selectors, it is true *)
lemma auth_weaken:
  "asub           | store \<turnstile> rul \<Down> dspent | dnew | store' FIRE \<Longrightarrow>
    rule_only_any rul \<Longrightarrow>
  (asub \<union> others) | store \<turnstile> rul \<Down> dspent | dnew | store' FIRE"
  oops

(* We can always add new facts if the program only contains 'any' selectors *)
lemma store_weaken_if_any:
  "asub |  store            \<turnstile> rul \<Down> dspent | dnew | store' FIRE \<Longrightarrow>
   rule_only_any rul \<Longrightarrow>
   asub | (store \<union># others) \<turnstile> rul \<Down> dspent | dnew | store' FIRE"
  oops

end