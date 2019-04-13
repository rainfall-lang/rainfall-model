(* Sketch of rainfall with HOAS *)
(* very rough, just to make sure I understand the semantics *)
theory Rainfall0
  imports Main "HOL-Library.Multiset"
begin

datatype party = party string
type_synonym auth = "party set"

datatype symbol = symbol string
datatype label = label string
datatype ctor_name = ctor_name string
datatype rule_name = rule_name string
datatype term_var = term_var string

(* Recursive knot - Isabelle doesn't support mutual recursion between datatypes and records *)
record 'a fact_info =
  fact_ctor :: ctor_name
  fact_value :: 'a
  fact_by :: auth
  fact_obs :: auth
  fact_rules :: "rule_name set"
(* Declare fact_info as a bounded natural functor so we can use it recursively in values *)
copy_bnf ('a,'b) fact_info_ext

(* Literals - changed LRules to single rule name, list in value *)
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
  | vfact "val fact_info"
type_synonym fact = "val fact_info"

(* HOAS for terms *)
type_synonym term_heap = "term_var \<Rightarrow> val"
type_synonym trm = "term_heap \<Rightarrow> val"

(* Definitions of rules *)
(* gather should have list of terms - ignore for now *)
datatype gather = gather_when ctor_name trm
datatype select = select_any | select_first trm
(* ignore consume/retain for now *)
datatype consume = consume_weight trm
datatype gain = gain_auth trm

datatype match = match term_var gather select consume gain

(* ignore 'say' and factoids for now - just allow returning list of facts in term *)
datatype rule = rule rule_name "match list" "trm"


(* Store operations *)
type_synonym factoid = "(fact \<times> nat)"
type_synonym store = "fact multiset"

definition store_of_factoid :: "factoid \<Rightarrow> store" where
"store_of_factoid fw = replicate_mset (snd fw) (fst fw)"


(* Sorting by term: only support comparison on nats for now *)
fun nat_of_val :: "val \<Rightarrow> nat" where
  "nat_of_val (vlit (lnat n)) = n"
| "nat_of_val _               = undefined"

(* Get all the facts with a minimum value, according to some function *)
fun find_firsts :: "fact list \<Rightarrow> term_heap \<Rightarrow> term_var \<Rightarrow> trm \<Rightarrow> fact list" where
  "find_firsts [] _ _ _ = []"
| "find_firsts fs h v e =
     (let d = map (\<lambda>f. (nat_of_val (e (h (v := vfact f))), f)) fs
   in let v' = min_list (map fst d)
   in map snd (filter (\<lambda>(v,f). v = v') d))"

(* Examples to make sure find_firsts works *)
definition mk_vfact :: "string \<Rightarrow> val \<Rightarrow> val fact_info" where
"mk_vfact nm v = \<lparr>fact_ctor=ctor_name ''fact'', fact_value = v, fact_by = {party nm}, fact_obs = {}, fact_rules = {}\<rparr>"

definition vnat :: "nat \<Rightarrow> val" where
"vnat i = vlit (lnat i)"

lemma "find_firsts [mk_vfact ''alice'' (vnat 0), mk_vfact ''bob'' (vnat 1), mk_vfact ''charlie'' (vnat 0)] (\<lambda>_. undefined) (term_var ''x'') (\<lambda>s. case s (term_var ''x'') of vfact f \<Rightarrow> fact_value f)
= [\<lparr>fact_ctor = ctor_name ''fact'', fact_value = vlit (lnat 0), fact_by = {party ''alice''}, fact_obs = {}, fact_rules = {}\<rparr>,
  \<lparr>fact_ctor = ctor_name ''fact'', fact_value = vlit (lnat 0), fact_by = {party ''charlie''}, fact_obs = {},
     fact_rules = {}\<rparr>]"
  by eval


(* Dynamic semantics for select *)
inductive EvSelect :: "fact list \<Rightarrow> term_heap \<Rightarrow> term_var \<Rightarrow> select \<Rightarrow> fact \<Rightarrow> bool" where
  EvAny: "f \<in> set fs \<Longrightarrow> EvSelect fs _ _ select_any f"
| EvFirst: "f \<in> set (find_firsts fs h v e) \<Longrightarrow> EvSelect fs h v (select_first e) f"

find_consts "'a multiset" "'a list"

definition can_see_fact :: "auth \<Rightarrow> fact \<Rightarrow> bool" where
"can_see_fact a f \<equiv> {} \<noteq> (a \<inter> (fact_by f \<union> fact_obs f))"

definition check_gather :: "auth \<Rightarrow> term_heap \<Rightarrow> term_var \<Rightarrow> ctor_name \<Rightarrow> trm \<Rightarrow> fact \<Rightarrow> bool" where
"check_gather Asub h v ctor pred f =
  (fact_ctor f = ctor \<and>
  can_see_fact Asub f \<and>
  pred (h(v := vfact f)) = vlit (lbool True))"

inductive EvGather :: "auth \<Rightarrow> store \<Rightarrow> term_heap \<Rightarrow> term_var \<Rightarrow> gather \<Rightarrow> fact list \<Rightarrow> bool" where
  EvGather: "fs = fold_mset (\<lambda>f s. if check_gather Asub h v ctor pred f then (f # s) else s) [] s \<Longrightarrow> EvGather Asub s h v (gather_when ctor pred) fs"

inductive EvConsume :: "fact \<Rightarrow> store \<Rightarrow> term_heap \<Rightarrow> consume \<Rightarrow> nat \<Rightarrow> store \<Rightarrow> bool" where
  EvConsume: "w h = vlit (lnat w_need) \<Longrightarrow> count s f \<ge> w_need \<Longrightarrow> s' = (s - replicate_mset w_need f) \<Longrightarrow> EvConsume f s h (consume_weight w) w_need s'"

inductive EvGain :: "fact \<Rightarrow> term_heap \<Rightarrow> gain \<Rightarrow> auth \<Rightarrow> bool" where
  EvGain: "t h = vlit (lauth a) \<Longrightarrow> a \<subseteq> fact_by f \<Longrightarrow> EvGain f h (gain_auth t) a"

inductive EvExec :: "term_heap \<Rightarrow> trm \<Rightarrow> store \<Rightarrow> bool" where
  EvExec: "t h = vlist fvs \<Longrightarrow> fs = map (\<lambda>vf. case vf of vfact f \<Rightarrow> f) fvs \<Longrightarrow> EvExec h t (mset fs)"


inductive EvMatch :: "rule_name \<Rightarrow> auth \<Rightarrow> store \<Rightarrow> term_heap \<Rightarrow> match \<Rightarrow> auth \<Rightarrow> factoid \<Rightarrow> store \<Rightarrow> term_heap \<Rightarrow> bool" where
  EvMatch: "
    EvGather asub s h x gather fs \<Longrightarrow>
    EvSelect fs h x sel f \<Longrightarrow>
    h' = h(x := vfact f) \<Longrightarrow>
    EvConsume f s h' con w s' \<Longrightarrow>
    EvGain f h' gain again \<Longrightarrow>
    rn \<in> fact_rules f \<Longrightarrow>
    EvMatch rn asub s h (match x gather sel con gain) again (f,w) s' h'"


inductive EvMatches :: "rule_name \<Rightarrow> auth \<Rightarrow> store \<Rightarrow> term_heap \<Rightarrow> match list \<Rightarrow> auth \<Rightarrow> store \<Rightarrow> term_heap \<Rightarrow> bool" where
  EvMatchNil: "EvMatches n a s h [] {} {#} h"
| EvMatchCons: "EvMatch n a s h m ag fw s' h' \<Longrightarrow>
    EvMatches n a s' h' ms ag' ds' h'' \<Longrightarrow>
    EvMatches n a s h (m # ms) (ag \<union> ag') (store_of_factoid fw \<union># ds') h''"

inductive EvFire :: "auth \<Rightarrow> store \<Rightarrow> rule \<Rightarrow> store \<Rightarrow> store \<Rightarrow> store \<Rightarrow> bool" where
  EvFire: "EvMatches rn asub s (\<lambda>_. undefined) matches ahas dspent h' \<Longrightarrow>
    EvExec h' say dnew \<Longrightarrow>
    s' = ((s - dspent) \<union># dnew) \<Longrightarrow>
    EvFire asub s (rule rn matches say) dspent dnew s'"


lemma frame_constriction_EvMatches:
  "EvMatches rn asub store h matches ahas dspent h' \<Longrightarrow>
   EvMatches rn asub dspent h matches ahas dspent h'"
proof (induct rule: EvMatches.induct)
  case (EvMatchNil n a s h)
  then show ?case
    using EvMatches.intros by simp
next
  case (EvMatchCons n a s h m ag fw s' h' ms ag' ds' h'')
  then show ?case
    apply (intro EvMatches.intros)
     apply (cases m; clarsimp)
    apply (erule EvMatch.cases; clarsimp)
     apply (intro EvMatch.intros)
          apply auto
     apply (erule EvGather.cases; clarsimp; intro EvGather.intros)
    sledgehammer
    oops

lemma frame_constriction:
  "EvFire asub store rul dspent dnew store' \<Longrightarrow>
   EvFire asub dspent rul dspent dnew dnew"
  oops

(* We can always add new facts if they're not visible *)
lemma spend_only_accessible:
  "EvFire asub store rul dspent dnew store' \<Longrightarrow>
   (\<forall>f \<in># dspent. can_see_fact asub f)"
  oops

(* We can always add new facts if they're not visible *)
lemma store_weaken_inaccessible:
  "EvFire asub store rul dspent dnew store' \<Longrightarrow>
   (\<forall>f \<in># others. \<not>(can_see_fact asub f)) \<Longrightarrow>
   EvFire asub (store \<union># others) rul dspent dnew store'"
  oops

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