(* Dynamic semantics *)
theory Dynamic
  imports Main "HOL-Library.Multiset" "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools"
  Exp
begin

(* Check if authority has enough permissions to see the fact *)
definition can_see_fact :: "auth \<Rightarrow> 'f fact \<Rightarrow> bool" where
"can_see_fact a f \<equiv> {} \<noteq> (a \<inter> (fact_by f \<union> fact_obs f))"

(* Predicate for gathering facts, as in set comprehension in EvGather rule in paper *)
definition check_gather :: "auth \<Rightarrow> 'f fact_env \<Rightarrow> fact_var \<Rightarrow> fact_ctor \<Rightarrow> ('f,bool) exp \<Rightarrow> 'f fact \<Rightarrow> bool" where
"check_gather Asub h v ctor pred f =
  (fact_name f = ctor \<and>
  can_see_fact Asub f \<and>
  pred (h(v := f)))"

inductive EvGather :: "auth \<Rightarrow> 'f store \<Rightarrow> 'f fact_env \<Rightarrow> fact_var \<Rightarrow> 'f gather \<Rightarrow> 'f store \<Rightarrow> bool"
    ("_ | _ | _ | _ \<turnstile> _ \<Down> _ GATHER" [900,900,900,900,900,900] 1000) where
(* For the notation, require parentheses for almost anything other than function application.
   This should hopefully keep the grammar unambiguous. *)
  EvGather: "fs = filter_mset (check_gather Asub h v ctor pred) s \<Longrightarrow>
    Asub | s | h | v \<turnstile> gather_when ctor pred \<Down> fs GATHER"


(* Get all the facts with a minimum value according to some scoring function *)
definition find_firsts :: "'f store \<Rightarrow> 'f fact_env \<Rightarrow> fact_var \<Rightarrow> ('f,nat) exp \<Rightarrow> 'f store" where
"find_firsts fs env v x = (
       let score = (\<lambda>f. x (env (v := f)))
    in let v' = Min (score ` set_mset fs)
    in filter_mset (\<lambda>f. score f = v') fs)"

(* Dynamic semantics for select *)
inductive EvSelect :: "'f store \<Rightarrow> 'f fact_env \<Rightarrow> fact_var \<Rightarrow> 'f select \<Rightarrow> 'f fact \<Rightarrow> bool"
    ("_ | _ | _ \<turnstile> _ \<Down> _ SELECT" [900,900,900,900,900] 1000) where
  EvAny: "f \<in># fs \<Longrightarrow>
     fs | _ | _ \<turnstile> select_any \<Down> f SELECT"
| EvFirst: "f \<in># find_firsts fs h v e \<Longrightarrow>
     fs | h | v \<turnstile> select_first e \<Down> f SELECT"

inductive EvConsume :: "rule_name \<Rightarrow> 'f fact \<Rightarrow> 'f fact_env \<Rightarrow> 'f consume \<Rightarrow> nat \<Rightarrow> bool"
    ("_ | _ | _ \<turnstile> _ \<Down> _ CONSUME" [900,900,900,900,900] 1000) where
  EvConsumeNone:
   "w h = 0 \<Longrightarrow>
    n | f | h \<turnstile> consume_weight w \<Down> 0 CONSUME"
| EvConsumeSome:
   "w h = w_need \<Longrightarrow>
    w_need > 0 \<Longrightarrow>
    n \<in> fact_rules f \<Longrightarrow>
    n | f | h \<turnstile> consume_weight w \<Down> w_need CONSUME"


inductive EvGain :: "rule_name \<Rightarrow> 'f fact \<Rightarrow> 'f fact_env \<Rightarrow> 'f gain \<Rightarrow> auth \<Rightarrow> bool"
    ("_ | _ | _ \<turnstile> _ \<Down> _ GAIN" [900,900,900,900,900] 1000) where
  EvGainNone:
  "t h = {} \<Longrightarrow>
   n | f | h \<turnstile> gain_auth t \<Down> {} GAIN"
| EvGainSome:
  "t h = a \<Longrightarrow>
   a \<subseteq> fact_by f \<Longrightarrow>
   n \<in> fact_rules f \<Longrightarrow>
   n | f | h \<turnstile> gain_auth t \<Down> a GAIN"

inductive EvExec :: "'f fact_env \<Rightarrow> ('f, 'f store) exp \<Rightarrow> 'f store \<Rightarrow> bool"
    ("_ \<turnstile> _ \<Down> _ EXEC" [900,900,900] 1000) where
  EvExec: "t h = s' \<Longrightarrow>
   h \<turnstile> t \<Down> s' EXEC"


inductive EvMatch :: "rule_name \<Rightarrow> auth \<Rightarrow> 'f store \<Rightarrow> 'f fact_env \<Rightarrow> 'f match \<Rightarrow> 'f factoid \<Rightarrow> auth \<Rightarrow> 'f fact_env \<Rightarrow> bool"
    ("_ | _ | _ | _ \<turnstile> _ \<Down> _ | _ | _ MATCH" [900,900,900,900,900,900,900,900] 1000) where
  EvMatch: "
       asub | s | h | x  \<turnstile> gather \<Down> fs     GATHER  \<Longrightarrow>
             fs | h | x  \<turnstile> sel    \<Down> f      SELECT  \<Longrightarrow>
         rn | f |     h' \<turnstile> con    \<Down> w      CONSUME \<Longrightarrow>
         rn | f |     h' \<turnstile> gain   \<Down> again  GAIN    \<Longrightarrow>
    h' = h(x := f)                                 \<Longrightarrow>
    rn | asub | s | h \<turnstile> match x gather sel con gain \<Down> (f,w) | again | h' MATCH"

(* rn | asub | s | h \<turnstile> ms \<Down> fread | dspent | ahas | h' MATCHES
  In the paper fread is a set, but we use a multiset here because reasoning about converting sets
  to multisets requires lots of little conversion lemmas that aren't in the standard library.
*)
inductive EvMatches :: "rule_name \<Rightarrow> auth \<Rightarrow> 'f store \<Rightarrow> 'f fact_env \<Rightarrow> 'f match list \<Rightarrow> 'f store \<Rightarrow> 'f store \<Rightarrow> auth \<Rightarrow> 'f fact_env \<Rightarrow> bool"
    ("_ | _ | _ | _ \<turnstile> _ \<Down> _ | _ | _ | _ MATCHES" [900,900,900,900,900,900,900,900,900] 1000) where
  EvMatchNil:
    "n | a | s | h \<turnstile> [] \<Down> {#} | {#} | {} | h MATCHES"
  | EvMatchCons: "
    n | a | s | h  \<turnstile>      m   \<Down>   (f,w)  | ag  | h'  MATCH   \<Longrightarrow>
    n | a | s | h' \<turnstile>      ms  \<Down>  fs | ds | ag' | h'' MATCHES \<Longrightarrow>
    fs'  = {#f#} \<union># fs                                       \<Longrightarrow>
    ds'  = replicate_mset w f + ds                           \<Longrightarrow>
    ag'' = ag \<union> ag'                                          \<Longrightarrow>
    n | a | s | h  \<turnstile> (m # ms) \<Down> fs' | ds' | ag'' |  h'' MATCHES"

inductive EvFire :: "auth \<Rightarrow> 'f store \<Rightarrow> 'f rule \<Rightarrow> 'f store \<Rightarrow> 'f store \<Rightarrow> 'f store \<Rightarrow> 'f store \<Rightarrow> bool"
    ("_ | _ \<turnstile> _ \<Down> _ | _ | _ | _ FIRE" [900,900,900,900,900,900,900] 1000) where
  EvFire: "
    rn | asub | s | (\<lambda>_. undefined) \<turnstile> matches \<Down> fread | dspent | ahas | h' MATCHES \<Longrightarrow>
                                 h' \<turnstile> say     \<Down> dnew                       EXEC    \<Longrightarrow>
    dspent \<subseteq># s                                                                    \<Longrightarrow>
    s' = ((s - dspent) + dnew)                                                     \<Longrightarrow>
    (\<forall>f \<in># dnew. fact_by f \<subseteq> ahas)                                                 \<Longrightarrow>
               asub | s \<turnstile> rule rn matches say \<Down> fread | dspent | dnew | s' FIRE"

end