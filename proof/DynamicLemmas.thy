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
method elim_Ev = (elim EvFire.cases EvExec.cases EvMatch.cases EvGather.cases; clarsimp)
method intro_Ev = (intro EvMatches.intros EvExec.intros EvMatch.intros EvGain.intros EvGather.intros EvSelect.intros EvConsume.intros)

(* trivial *)
lemma new_is_added:
  "asub | store \<turnstile> rul \<Down> fread | dspent | dnew | store' FIRE \<Longrightarrow>
   dnew \<subseteq># store'"
  using mset_subset_eq_add_right
  by (elim EvFire.cases; blast)


(* We only spend what we have - trivial *)
lemma spent_is_subset:
  "asub | store \<turnstile> rul \<Down> fread | dspent | dnew | store' FIRE \<Longrightarrow>
   dspent \<subseteq># store"
  by elim_Ev


(* We only spend and read what we have - trivial *)
lemma spent_read_is_subset_EvMatches:
  "rn | asub | store | h \<turnstile> matches \<Down> fread | dspent | ahas | h' MATCHES \<Longrightarrow>
   fread \<subseteq># store"
proof (induct rule: EvMatches.induct)
  case (EvMatchCons n a s h m ag ds h' ms ag' ds' h'')
  then show ?case
    by (elim_Ev; metis EvSelect.cases find_firsts_in_store mset_subset_eqD multiset_filter_subset)
qed auto

lemma spent_read_is_subset:
  "asub | store \<turnstile> rul \<Down> fread | dspent | dnew | store' FIRE \<Longrightarrow>
   fread \<union># dspent \<subseteq># store"
  using spent_read_is_subset_EvMatches
  by elim_Ev


(* We only use what we spend *)
lemma frame_constriction_EvMatches:
  "rn | asub | store  | h \<turnstile> matches \<Down> fread | dspent | ahas | h' MATCHES \<Longrightarrow>
   fread \<union># dspent \<subseteq># ds' \<Longrightarrow> ds' \<subseteq># store \<Longrightarrow>
   rn | asub | ds' | h \<turnstile> matches \<Down> fread | dspent | ahas | h' MATCHES"
proof (induct arbitrary: ds' rule: EvMatches.induct)
  case (EvMatchCons n a s h m f w ag h' ms fs ds ag' h'' fs' ds' ag'')
  obtain x gather sel con gain where match_is:
    "m = match x gather sel con gain"
    using match.exhaust by blast
  from EvMatchCons match_is have IHrest:
    "n | a | ds' | h(x := f) \<turnstile> ms \<Down> fs | ds | ag' | h'' MATCHES"
    by (elim_Ev; metis EvMatchCons.hyps(3) mset_subset_eq_add_right subset_mset.sup.absorb_iff1 subset_mset.sup.bounded_iff)
  from EvMatchCons match_is  show ?case
    apply (elim_Ev)
    apply (elim EvSelect.cases; clarsimp)
     apply (intro_Ev; (rule refl)?; simp add: IHrest)
    apply (intro_Ev; (rule refl)?; (simp add: IHrest)?)
    apply (rule find_firsts_min_in_subset)
      apply assumption
    using multiset_filter_mono
     apply blast
    by (metis count_filter_mset find_firsts_in_store not_in_iff)
qed (auto intro: EvMatches.intros)

lemma frame_constriction:
  "asub | store  \<turnstile> rul \<Down> fread | dspent | dnew | store' FIRE \<Longrightarrow>
   asub | (fread \<union># dspent) \<turnstile> rul \<Down> fread | dspent | dnew | (dnew + (fread - dspent))   FIRE"
  apply (elim EvFire.cases; clarsimp)
  apply (intro EvFire.intros; assumption?)
    apply (rule frame_constriction_EvMatches; simp)
    apply (simp add: spent_read_is_subset_EvMatches)
  by (simp add: spent_read_is_subset_EvMatches subset_mset.sup_commute sup_subset_mset_def)+


(* We only spend visible facts *)
lemma spend_only_accessible_EvMatches:
  "rn | asub | store  | h \<turnstile> matches \<Down> fread | dspent | ahas | h' MATCHES  \<Longrightarrow>
   (\<forall>f \<in># fread \<union># dspent. can_see_fact asub f)"
proof (induct rule: EvMatches.induct)
  case (EvMatchCons n a s h m f w ag h' ms fs ds ag' h'' fs' ds' ag'')
  then show ?case
    apply (elim_Ev; elim EvSelect.cases)
    using check_gather_def find_firsts_def by auto
qed auto

lemma spend_only_accessible:
  "asub | store \<turnstile> rul \<Down> fread | dspent | dnew | store' FIRE \<Longrightarrow>
   (\<forall>f \<in># fread \<union># dspent. can_see_fact asub f)"
  by (elim EvFire.cases; force simp add: spend_only_accessible_EvMatches)


(* Helper lemma: if it's not visible, "check_gather" filters it out *)
lemma check_gather_inaccessible_empty:
  " (\<forall>f \<in># others. \<not>(can_see_fact asub f)) \<Longrightarrow>
  filter_mset (check_gather asub env v ctor pred) others = {#}"
  apply (unfold check_gather_def)
  using set_mset_eq_empty_iff by fastforce

(* We can always add new facts if they're not visible *)
lemma store_weaken_inaccessible_EvMatches:
  "rn | asub | store            | h \<turnstile> matches \<Down> fread | dspent | ahas | h' MATCHES  \<Longrightarrow>
   (\<forall>f \<in># others. \<not>(can_see_fact asub f)) \<Longrightarrow>
   rn | asub | (store + others) | h \<turnstile> matches \<Down> fread | dspent | ahas | h' MATCHES"
proof (induct rule: EvMatches.induct)
  case (EvMatchNil n a s h)
  then show ?case
    using EvMatches.EvMatchNil by blast
next
  case (EvMatchCons n a s h m f w ag h' ms fs ds ag' h'' fs' ds' ag'')
  then show ?case
    apply (elim_Ev; elim EvSelect.cases)
     apply (intro_Ev; (rule refl)?; (simp add: fun_upd_def)?)
     apply (subst check_gather_inaccessible_empty[where others=others];
            simp add: EvSelect.simps)
    apply (intro_Ev; (rule refl)?; (simp add: fun_upd_def)?)
    by (subst check_gather_inaccessible_empty[where others=others];
            simp add: EvSelect.simps)
qed

lemma store_weaken_inaccessible:
  "asub |  store           \<turnstile> rul \<Down> fread | dspent | dnew |  store'           FIRE \<Longrightarrow>
   (\<forall>f \<in># others. \<not>(can_see_fact asub f)) \<Longrightarrow>
   asub | (store + others) \<turnstile> rul \<Down> fread | dspent | dnew | (store' + others) FIRE"
  apply (elim EvFire.cases; clarsimp)
  apply (intro EvFire.intros)
  using store_weaken_inaccessible_EvMatches
      apply blast
     apply blast
    apply (simp add: subset_mset.add_increasing2)
   apply (metis ab_semigroup_add_class.add_ac(1) add.commute  subset_mset.add_diff_assoc2)
  by blast


(* auth of new facts is subset of auth of all spent facts *)
lemma new_auth_gained_from_spent_EvMatches:
  "rn | asub | store | h \<turnstile> matches \<Down> fread | dspent | ahas | h' MATCHES  \<Longrightarrow>
  \<forall>a \<in> ahas. \<exists>d \<in># fread \<union># dspent. a \<in> fact_by d"
proof (induct rule: EvMatches.induct)
  case (EvMatchCons n a s h m ag fw s' h' ms ag' ds' h'')
  then show ?case
    by (elim_Ev;
        elim EvGain.cases;
        clarsimp;
        blast)
qed auto

lemma new_auth_gained_from_spent:
  "asub | store \<turnstile> rul \<Down> fread | dspent | dnew | store' FIRE \<Longrightarrow>
  \<forall>f \<in># dnew. \<forall>a \<in> fact_by f. \<exists>d \<in># fread \<union># dspent. a \<in> fact_by d"
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
  "rn |  asub           | store | h \<turnstile> matches \<Down> fread | dspent | ahas | h' MATCHES  \<Longrightarrow>
    matches_only_any matches \<Longrightarrow>
   rn | (asub \<union> others) | store | h \<turnstile> matches \<Down> fread | dspent | ahas | h' MATCHES"
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
  "asub           | store \<turnstile> rul \<Down> fread | dspent | dnew | store' FIRE \<Longrightarrow>
    rule_only_any rul \<Longrightarrow>
  (asub \<union> others) | store \<turnstile> rul \<Down> fread | dspent | dnew | store' FIRE"
  apply (elim EvFire.cases)
  using auth_weaken_EvMatches
  by (metis EvFire.intros diff_union_cancelL mset_subset_eq_exists_conv rule_only_any.simps union_commute)


(* We can always add new facts if the program only contains 'any' selectors *)
lemma store_weaken_if_any_EvMatches:
  "rn | asub |  store           | h \<turnstile> matches \<Down> fread | dspent | ahas | h' MATCHES  \<Longrightarrow>
    matches_only_any matches \<Longrightarrow>
   rn | asub | (store + others) | h \<turnstile> matches \<Down> fread | dspent | ahas | h' MATCHES"
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
  "asub |  store           \<turnstile> rul \<Down> fread | dspent | dnew | store' FIRE \<Longrightarrow>
   rule_only_any rul \<Longrightarrow>
   asub | (store + others) \<turnstile> rul \<Down> fread | dspent | dnew | (store' + others) FIRE"
  apply (elim EvFire.cases EvExec.cases; clarsimp)
  apply (intro EvFire.intros EvExec.intros; (rule refl)?; assumption?)
    apply (simp add: store_weaken_if_any_EvMatches)
   apply (simp add: subset_mset.add_increasing2)
  by (metis add.commute add.left_commute  subset_mset.add_diff_assoc)

end