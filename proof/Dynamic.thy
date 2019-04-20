(* Dynamic semantics *)
theory Dynamic
  imports Main "HOL-Library.Multiset" "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools"
  Exp
begin

definition can_see_fact :: "auth \<Rightarrow> fact \<Rightarrow> bool" where
"can_see_fact a f \<equiv> {} \<noteq> (a \<inter> (fact_by f \<union> fact_obs f))"

definition check_gather :: "auth \<Rightarrow> fact_env \<Rightarrow> fact_var \<Rightarrow> fact_ctor \<Rightarrow> bool exp \<Rightarrow> fact \<Rightarrow> bool" where
"check_gather Asub h v ctor pred f =
  (fact_name f = ctor \<and>
  can_see_fact Asub f \<and>
  pred (h(v := f)))"

inductive EvGather :: "auth \<Rightarrow> store \<Rightarrow> fact_env \<Rightarrow> fact_var \<Rightarrow> gather \<Rightarrow> store \<Rightarrow> bool"
    ("_ | _ | _ | _ \<turnstile> _ \<Down> _ GATHER" [900,900,900,900,900,900] 1000) where
(* For the notation, require parentheses for almost anything other than function application.
   This should hopefully keep the grammar unambiguous. *)
  EvGather: "fs = filter_mset (check_gather Asub h v ctor pred) s \<Longrightarrow>
    Asub | s | h | v \<turnstile> gather_when ctor pred \<Down> fs GATHER"


(* Get all the facts with a minimum value, according to some function *)
definition find_firsts :: "store \<Rightarrow> fact_env \<Rightarrow> fact_var \<Rightarrow> nat exp \<Rightarrow> store" where
"find_firsts fs env v x = (
       let score = (\<lambda>f. x (env (v := f)))
    in let v' = Min (score ` set_mset fs)
    in filter_mset (\<lambda>f. score f = v') fs)"

(* Dynamic semantics for select *)
inductive EvSelect :: "store \<Rightarrow> fact_env \<Rightarrow> fact_var \<Rightarrow> select \<Rightarrow> fact \<Rightarrow> bool"
    ("_ | _ | _ \<turnstile> _ \<Down> _ SELECT" [900,900,900,900,900] 1000) where
  EvAny: "f \<in># fs \<Longrightarrow>
     fs | _ | _ \<turnstile> select_any \<Down> f SELECT"
| EvFirst: "f \<in># find_firsts fs h v e \<Longrightarrow>
     fs | h | v \<turnstile> select_first e \<Down> f SELECT"


(* Keep track of which facts are spent, and which are not spent but required for execution *)
record used_facts =
  facts_consumed :: "fact multiset"
  facts_retained :: "fact multiset"

definition used_facts_empty :: "used_facts" where
"used_facts_empty = \<lparr>facts_consumed = {#}, facts_retained = {#}\<rparr>"

(* Add two used_facts together: add weights for consumed facts (+), and take maximum weight of retained facts (\<union>#) *)
definition used_facts_add :: "used_facts \<Rightarrow> used_facts \<Rightarrow> used_facts" where
"used_facts_add a b = \<lparr>facts_consumed = facts_consumed a + facts_consumed b, facts_retained = facts_retained a \<union># facts_retained b\<rparr>"

(* The smallest store required to execute: take maximum of consumed and retained weights *)
definition store_of_used_facts :: "used_facts \<Rightarrow> store" where
"store_of_used_facts dspent = (facts_consumed dspent \<union># facts_retained dspent)"

inductive EvConsume :: "fact \<Rightarrow> fact_env \<Rightarrow> consume \<Rightarrow> used_facts \<Rightarrow> bool"
    ("_ | _ \<turnstile> _ \<Down> _ CONSUME" [900,900,900,900] 1000) where
  EvConsume: "w h = w_need \<Longrightarrow>
              w_need > 0   \<Longrightarrow>
              c = \<lparr> facts_consumed = replicate_mset w_need f, facts_retained = {#} \<rparr> \<Longrightarrow>
    f | h \<turnstile> consume_weight w \<Down> c CONSUME"
| EvRetain:  "w h = w_need \<Longrightarrow>
              w_need > 0   \<Longrightarrow>
              c = \<lparr> facts_consumed = {#}, facts_retained = replicate_mset w_need f \<rparr> \<Longrightarrow>
    f | h \<turnstile> consume_retain w \<Down> c CONSUME"


inductive EvGain :: "fact \<Rightarrow> fact_env \<Rightarrow> gain \<Rightarrow> auth \<Rightarrow> bool"
    ("_ | _ \<turnstile> _ \<Down> _ GAIN" [900,900,900,900] 1000) where
  EvGain: "t h = a \<Longrightarrow>
           a \<subseteq> fact_by f \<Longrightarrow>
   f | h \<turnstile> gain_auth t \<Down> a GAIN"

inductive EvExec :: "fact_env \<Rightarrow> store exp \<Rightarrow> store \<Rightarrow> bool"
    ("_ \<turnstile> _ \<Down> _ EXEC" [900,900,900] 1000) where
  EvExec: "t h = s' \<Longrightarrow>
   h \<turnstile> t \<Down> s' EXEC"


inductive EvMatch :: "rule_name \<Rightarrow> auth \<Rightarrow> store \<Rightarrow> fact_env \<Rightarrow> match \<Rightarrow> auth \<Rightarrow> used_facts \<Rightarrow> fact_env \<Rightarrow> bool"
    ("_ | _ | _ | _ \<turnstile> _ \<Down> _ | _ | _ MATCH" [900,900,900,900,900,900,900,900] 1000) where
  EvMatch: "
       asub | s | h | x  \<turnstile> gather \<Down> fs     GATHER  \<Longrightarrow>
             fs | h | x  \<turnstile> sel    \<Down> f      SELECT  \<Longrightarrow>
             f  |     h' \<turnstile> con    \<Down> c      CONSUME \<Longrightarrow>
             f  |     h' \<turnstile> gain   \<Down> again  GAIN    \<Longrightarrow>
    h' = h(x := f)                                 \<Longrightarrow>
    rn \<in> fact_rules f                              \<Longrightarrow>
    rn | asub | s | h \<turnstile> match x gather sel con gain \<Down> again | c | h' MATCH"


inductive EvMatches :: "rule_name \<Rightarrow> auth \<Rightarrow> store \<Rightarrow> fact_env \<Rightarrow> match list \<Rightarrow> auth \<Rightarrow> used_facts \<Rightarrow> fact_env \<Rightarrow> bool"
    ("_ | _ | _ | _ \<turnstile> _ \<Down> _ | _ | _ MATCHES" [900,900,900,900,900,900,900,900] 1000) where
  EvMatchNil:
    "n | a | s | h \<turnstile> [] \<Down> {} | used_facts_empty | h MATCHES"
  | EvMatchCons: "
    n | a | s | h  \<turnstile>      m   \<Down>  ag        | ds                    | h'  MATCH   \<Longrightarrow>
    n | a | s | h' \<turnstile>      ms  \<Down>  ag'       | ds'                   | h'' MATCHES \<Longrightarrow>
    n | a | s | h  \<turnstile> (m # ms) \<Down> (ag \<union> ag') | used_facts_add ds ds' | h'' MATCHES"

inductive EvFire :: "auth \<Rightarrow> store \<Rightarrow> rule \<Rightarrow> used_facts \<Rightarrow> store \<Rightarrow> store \<Rightarrow> bool"
    ("_ | _ \<turnstile> _ \<Down> _ | _ | _ FIRE" [900,900,900,900,900,900] 1000) where
  EvFire: "
    rn | asub | s | (\<lambda>_. undefined) \<turnstile> matches \<Down> ahas | dspent | h' MATCHES \<Longrightarrow>
                                 h' \<turnstile> say     \<Down> dnew               EXEC    \<Longrightarrow>
    store_of_used_facts dspent \<subseteq># s                                        \<Longrightarrow>
    s' = ((s - facts_consumed dspent) + dnew)                              \<Longrightarrow>
    (\<forall>f \<in># dnew. fact_by f \<subseteq> ahas)                                         \<Longrightarrow>
               asub | s \<turnstile> rule rn matches say \<Down> dspent | dnew | s' FIRE"

end