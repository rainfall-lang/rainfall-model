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

inductive EvConsume :: "fact \<Rightarrow> fact_env \<Rightarrow> consume \<Rightarrow> nat \<Rightarrow> bool"
    ("_ | _ \<turnstile> _ \<Down> _ CONSUME" [900,900,900,900] 1000) where
  EvConsume: "w h = w_need \<Longrightarrow>
    f | h \<turnstile> consume_weight w \<Down> w_need CONSUME"


inductive EvGain :: "fact \<Rightarrow> fact_env \<Rightarrow> gain \<Rightarrow> auth \<Rightarrow> bool"
    ("_ | _ \<turnstile> _ \<Down> _ GAIN" [900,900,900,900] 1000) where
  EvGain: "t h = a \<Longrightarrow>
           a \<subseteq> fact_by f \<Longrightarrow>
   f | h \<turnstile> gain_auth t \<Down> a GAIN"

inductive EvExec :: "fact_env \<Rightarrow> store exp \<Rightarrow> store \<Rightarrow> bool"
    ("_ \<turnstile> _ \<Down> _ EXEC" [900,900,900] 1000) where
  EvExec: "t h = s' \<Longrightarrow>
   h \<turnstile> t \<Down> s' EXEC"


inductive EvMatch :: "rule_name \<Rightarrow> auth \<Rightarrow> store \<Rightarrow> fact_env \<Rightarrow> match \<Rightarrow> factoid \<Rightarrow> auth \<Rightarrow> fact_env \<Rightarrow> bool"
    ("_ | _ | _ | _ \<turnstile> _ \<Down> _ | _ | _ MATCH" [900,900,900,900,900,900,900,900] 1000) where
  EvMatch: "
       asub | s | h | x  \<turnstile> gather \<Down> fs     GATHER  \<Longrightarrow>
             fs | h | x  \<turnstile> sel    \<Down> f      SELECT  \<Longrightarrow>
             f  |     h' \<turnstile> con    \<Down> w      CONSUME \<Longrightarrow>
             f  |     h' \<turnstile> gain   \<Down> again  GAIN    \<Longrightarrow>
    h' = h(x := f)                                 \<Longrightarrow>
    rn \<in> fact_rules f                              \<Longrightarrow>
    rn | asub | s | h \<turnstile> match x gather sel con gain \<Down> (f,w) | again | h' MATCH"


inductive EvMatches :: "rule_name \<Rightarrow> auth \<Rightarrow> store \<Rightarrow> fact_env \<Rightarrow> match list \<Rightarrow> fact set \<Rightarrow> store \<Rightarrow> auth \<Rightarrow> fact_env \<Rightarrow> bool"
    ("_ | _ | _ | _ \<turnstile> _ \<Down> _ | _ | _ | _ MATCHES" [900,900,900,900,900,900,900,900,900] 1000) where
  EvMatchNil:
    "n | a | s | h \<turnstile> [] \<Down> {} | {#} | {} | h MATCHES"
  | EvMatchCons: "
    n | a | s | h  \<turnstile>      m   \<Down>   (f,w)  | ag  | h'  MATCH   \<Longrightarrow>
    n | a | s | h' \<turnstile>      ms  \<Down>  fs | ds | ag' | h'' MATCHES \<Longrightarrow>
    fs'  = {f} \<union> fs                                          \<Longrightarrow>
    ds'  = replicate_mset w f \<union># ds                          \<Longrightarrow>
    ag'' = ag \<union> ag'                                          \<Longrightarrow>
    n | a | s | h  \<turnstile> (m # ms) \<Down> fs' | ds' | ag'' |  h'' MATCHES"

inductive EvFire :: "auth \<Rightarrow> store \<Rightarrow> rule \<Rightarrow> fact set \<Rightarrow> store \<Rightarrow> store \<Rightarrow> store \<Rightarrow> bool"
    ("_ | _ \<turnstile> _ \<Down> _ | _ | _ | _ FIRE" [900,900,900,900,900,900,900] 1000) where
  EvFire: "
    rn | asub | s | (\<lambda>_. undefined) \<turnstile> matches \<Down> fread | dspent | ahas | h' MATCHES \<Longrightarrow>
                                 h' \<turnstile> say     \<Down> dnew                       EXEC    \<Longrightarrow>
    dspent \<subseteq># s                                                                    \<Longrightarrow>
    s' = ((s - dspent) + dnew)                                                     \<Longrightarrow>
    (\<forall>f \<in># dnew. fact_by f \<subseteq> ahas)                                                 \<Longrightarrow>
               asub | s \<turnstile> rule rn matches say \<Down> fread | dspent | dnew | s' FIRE"

end