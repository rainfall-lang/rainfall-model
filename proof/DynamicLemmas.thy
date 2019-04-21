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

(* Invert single-constructor relations *)
method elim_Ev = (elim EvFire.cases EvMatch.cases EvGather.cases EvGain.cases; clarsimp)
method intro_Ev = (intro EvMatches.intros EvMatch.intros EvGain.intros EvGather.intros EvSelect.intros EvConsume.intros)

(* trivial *)
lemma EvFire_new_is_added:
  "asub | store \<turnstile> rul \<Down> dspent | dnew | store' FIRE \<Longrightarrow>
   dnew \<subseteq># store'"
  by elim_Ev

(*
(* We only spend what we have - trivial *)
lemma EvMatches_spent_is_subset:
  "rn | asub | store | h \<turnstile> matches \<Down> ahas | dspent | h' MATCHES \<Longrightarrow>
   store_of_used_facts dspent \<subseteq># store"
  unfolding store_of_used_facts_def
proof (induct rule: EvMatches.induct)
  case (EvMatchNil n a s h)
  then show ?case
    by (auto simp add: used_facts_empty_def)
next
  case (EvMatchCons n a s h m ag ds h' ms ag' ds' h'')
  then show ?case
    apply elim_Ev
    apply (elim EvConsume.cases)
     apply (simp add: used_facts_add_def used_facts_empty_def add.commute count_le_replicate_mset_subset_eq subset_mset.le_diff_conv2)
(*    sledgehammer
     apply (meson mset_subset_eq_exists_conv subset_mset.order_trans)
    by (simp add: used_facts_add_def)
qed
*)
    oops
*)

lemma EvFire_spent_is_subset:
  "asub | store \<turnstile> rul \<Down> dspent | dnew | store' FIRE \<Longrightarrow>
   store_of_used_facts dspent \<subseteq># store"
  by elim_Ev



(* We only use what we spend *)
lemma frame_constriction_EvMatches:
  "rn | asub | store  | h \<turnstile> matches \<Down> ahas | dspent | h' MATCHES \<Longrightarrow>
   store_of_used_facts dspent \<subseteq># ds' \<Longrightarrow> ds' \<subseteq># store \<Longrightarrow>
   rn | asub | ds' | h \<turnstile> matches \<Down> ahas | dspent | h' MATCHES"
unfolding store_of_used_facts_def
proof (induct arbitrary: ds' rule: EvMatches.induct)
  case (EvMatchNil n a s h)
  then show ?case
    using EvMatches.intros by simp
next
  case (EvMatchCons n a s h m ag ds h' ms ag' ds' h'')
  then show ?case
    apply -
    apply (unfold used_facts_add_def)
    apply (elim EvFire.cases EvMatch.cases EvGather.cases EvGain.cases; clarsimp)
    apply (elim EvConsume.cases EvSelect.cases; clarsimp)
       apply (intro_Ev; (rule refl)?; (simp add: used_facts_add_def)?)
        apply (metis count_inI count_le_replicate_mset_subset_eq le_zero_eq mset_subset_eq_add_left not_gr_zero subseteq_mset_def)
       apply (metis (no_types, lifting) EvMatchCons.hyps(3) mset_subset_eq_add_right subset_mset.sup.absorb_iff1 subset_mset.sup.bounded_iff)
      apply (intro_Ev; (rule refl)?; (simp add: used_facts_add_def)?)
       apply (rule find_firsts_min_in_subset)
         apply assumption
    using multiset_filter_mono
        apply blast
       apply (smt count_inI count_le_replicate_mset_subset_eq find_firsts_in_store le_zero_eq mem_Collect_eq mset_subset_eq_add_left not_gr_zero set_mset_filter subset_mset.order.trans)
    apply (metis (no_types, lifting) EvMatchCons.hyps(3) mset_subset_eq_add_right subset_mset.sup.absorb_iff1 subset_mset.sup.bounded_iff)
      apply (intro_Ev; (rule refl)?; (simp add: used_facts_add_def)?)
    apply (simp add: mset_subset_eqD)
    using EvMatchCons.hyps(3) subset_mset.sup.boundedI
    apply blast
      apply (intro_Ev; (rule refl)?; (simp add: used_facts_add_def)?)
       apply (rule find_firsts_min_in_subset)
         apply assumption
    using multiset_filter_mono
        apply blast
       apply (smt count_inI count_le_replicate_mset_subset_eq find_firsts_in_store le_zero_eq mem_Collect_eq mset_subset_eq_add_left not_gr_zero set_mset_filter subset_mset.order.trans)
    using EvMatchCons.hyps(3) subset_mset.le_supI by blast
qed

lemma frame_constriction:
  "asub | store  \<turnstile> rul \<Down> dspent | dnew | store' FIRE \<Longrightarrow>
   asub | store_of_used_facts dspent \<turnstile> rul \<Down> dspent | dnew | (dnew + (facts_retained dspent - facts_consumed dspent))   FIRE"
  apply elim_Ev
  using frame_constriction_EvMatches
  apply (intro EvFire.intros; blast?)
  apply (unfold store_of_used_facts_def)
  by (metis add.commute multi_union_self_other_eq subset_mset.add_diff_inverse subset_mset.sup.cobounded1 sup_subset_mset_def)

(* We only spend visible facts *)
lemma spend_only_accessible_EvMatches:
  "rn | asub | store  | h \<turnstile> matches \<Down> ahas | dspent | h' MATCHES  \<Longrightarrow>
   (\<forall>f \<in># store_of_used_facts dspent. can_see_fact asub f)"
proof (induct rule: EvMatches.induct)
  case (EvMatchNil n a s h)
  then show ?case
    by (simp add: store_of_used_facts_def used_facts_add_def used_facts_empty_def)
next
  case (EvMatchCons n a s h m ag fw s' h' ms ag' ds' h'')
  then show ?case
    apply elim_Ev
    apply (simp add: store_of_used_facts_def used_facts_add_def used_facts_empty_def)
    apply (elim EvSelect.cases;
           clarsimp)
     apply (elim EvConsume.cases;
            fastforce simp add: check_gather_def)
    by (elim EvConsume.cases;
        clarsimp;
        smt UnCI check_gather_def find_firsts_in_store mem_Collect_eq set_mset_filter)
qed

lemma spend_only_accessible:
  "asub | store \<turnstile> rul \<Down> dspent | dnew | store' FIRE \<Longrightarrow>
   (\<forall>f \<in># store_of_used_facts dspent. can_see_fact asub f)"
  by (elim EvFire.cases; force simp add: spend_only_accessible_EvMatches)


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
    apply (elim EvSelect.cases)
     apply (elim EvConsume.cases;
            clarsimp)
      apply (intro_Ev;
            (rule refl)?;
             simp?;
             argo EvMatchCons.hyps)+
    apply (intro_Ev;
          (rule refl)?;
          simp?)
     apply (subst check_gather_inaccessible_empty[where others=others];
            simp add: EvSelect.simps)
    using EvMatchCons.hyps by blast
qed

lemma store_weaken_inaccessible:
  "asub |  store           \<turnstile> rul \<Down> dspent | dnew |  store'           FIRE \<Longrightarrow>
   (\<forall>f \<in># others. \<not>(can_see_fact asub f)) \<Longrightarrow>
   asub | (store + others) \<turnstile> rul \<Down> dspent | dnew | (store' + others) FIRE"
  apply (elim EvFire.cases; clarsimp)
  apply (intro EvFire.intros)
  using store_weaken_inaccessible_EvMatches
      apply blast
     apply blast
    apply (simp add: subset_mset.add_increasing2)
   apply (metis ab_semigroup_add_class.add_ac(1) add.commute store_of_used_facts_def subset_mset.add_diff_assoc2 subset_mset.sup.bounded_iff)
  by blast


(* auth of new facts is subset of auth of all spent facts *)
lemma new_auth_gained_from_spent_EvMatches:
  "rn | asub | store | h \<turnstile> matches \<Down> ahas | dspent | h' MATCHES  \<Longrightarrow>
  \<forall>a \<in> ahas. \<exists>d \<in># store_of_used_facts dspent. a \<in> fact_by d"
proof (induct rule: EvMatches.induct)
  case (EvMatchNil n a s h)
  then show ?case by simp
next
  case (EvMatchCons n a s h m ag fw s' h' ms ag' ds' h'')
  then show ?case
    by (elim_Ev;
        elim EvSelect.cases;
        elim EvConsume.cases;
        clarsimp simp add: store_of_used_facts_def used_facts_add_def used_facts_empty_def;
        blast)
qed

lemma new_auth_gained_from_spent:
  "asub | store \<turnstile> rul \<Down> dspent | dnew | store' FIRE \<Longrightarrow>
  \<forall>f \<in># dnew. \<forall>a \<in> fact_by f. \<exists>d \<in># store_of_used_facts dspent. a \<in> fact_by d"
  using new_auth_gained_from_spent_EvMatches
  by (elim EvFire.cases; blast)



fun matches_only_any :: "match list \<Rightarrow> bool" where
"matches_only_any matches = list_all (\<lambda>m. case m of match x gath sel con gain \<Rightarrow> sel = select_any) matches"

fun rule_only_any :: "rule \<Rightarrow> bool" where
"rule_only_any (rule _ matches _) = matches_only_any matches"

(* More permissions never stops a program from running *)
(* This probably isn't true for 'first' selectors, where adding more permissions could make a new minimum visible *)
(* But if the program only contains any selectors, it is true *)
lemma auth_weaken_EvMatches:
  "rn |  asub           | store | h \<turnstile> matches \<Down> ahas | dspent | h' MATCHES  \<Longrightarrow>
    matches_only_any matches \<Longrightarrow>
   rn | (asub \<union> others) | store | h \<turnstile> matches \<Down> ahas | dspent | h' MATCHES"
proof (induct rule: EvMatches.induct)
case (EvMatchNil n a s h)
  then show ?case
    by (simp add: EvMatches.EvMatchNil)
next
  case (EvMatchCons n a s h m ag ds h' ms ag' ds' h'' ag'' ds'')
  then show ?case
    apply (elim_Ev)
    apply (elim EvSelect.cases; clarsimp)
     apply (intro_Ev; (rule refl)?; (simp add: check_gather_def can_see_fact_def)?)
    using EvMatchCons.hyps(3) matches_only_any.elims
    by blast+
qed

lemma auth_weaken:
  "asub           | store \<turnstile> rul \<Down> dspent | dnew | store' FIRE \<Longrightarrow>
    rule_only_any rul \<Longrightarrow>
  (asub \<union> others) | store \<turnstile> rul \<Down> dspent | dnew | store' FIRE"
  apply (elim EvFire.cases)
  using auth_weaken_EvMatches
  by (metis EvFire.intros diff_union_cancelL mset_subset_eq_exists_conv rule_only_any.simps union_commute)


(* We can always add new facts if the program only contains 'any' selectors *)
lemma store_weaken_if_any_EvMatches:
  "rn | asub |  store            | h \<turnstile> matches \<Down> ahas | dspent | h' MATCHES  \<Longrightarrow>
    matches_only_any matches \<Longrightarrow>
   rn | asub | (store + others) | h \<turnstile> matches \<Down> ahas | dspent | h' MATCHES"
proof (induct rule: EvMatches.induct)
case (EvMatchNil n a s h)
  then show ?case
    by (simp add: EvMatches.EvMatchNil)
next
  case (EvMatchCons n a s h m ag ds h' ms ag' ds' h'' ag'' ds'')
  then show ?case
    apply (elim_Ev; elim EvSelect.cases; clarsimp)
    apply (intro_Ev; (rule refl)?; simp?)
    using EvMatchCons.hyps(3) matches_only_any.elims
    by blast
qed

lemma store_weaken_if_any:
  "asub |  store            \<turnstile> rul \<Down> dspent | dnew | store' FIRE \<Longrightarrow>
   rule_only_any rul \<Longrightarrow>
   asub | (store + others) \<turnstile> rul \<Down> dspent | dnew | (store' + others) FIRE"
  apply (elim EvFire.cases EvExec.cases; clarsimp)
  apply (intro EvFire.intros EvExec.intros; (rule refl)?; assumption?)
    apply (simp add: store_weaken_if_any_EvMatches)
   apply (simp add: subset_mset.add_increasing2)
  by (metis add.commute add.left_commute store_of_used_facts_def subset_mset.add_diff_assoc subset_mset.dual_order.trans subset_mset.sup.cobounded1)

end