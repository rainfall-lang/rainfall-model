(* Expressions and rules *)
theory Exp
  imports Main "HOL-Library.Multiset" "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools"
  Base
begin

(* As the term language is standard, we use a HOAS representation with a heap that maps variable names to facts *)
datatype     fact_var = fact_var string
(* The fact heap is parameterised by the type of fact payloads. *)
type_synonym 'f fact_env = "fact_var \<Rightarrow> 'f fact"
(* Expressions are parameterised by the type of fact payloads and result type. *)
type_synonym ('f,'r) exp   = "'f fact_env \<Rightarrow> 'r"

(* Matches: there are four parts to a match: gather, select, consume, and gain. *)

(* Gather: filter input facts according to constructor name and a boolean expression.
   In the paper, this is a list of expressions, but here we just join multiple expressions with conjunction *)
datatype 'f gather = gather_when fact_ctor "('f,bool) exp"

(* Select: gathering can return many input facts, and select specifies which of these facts to choose *)
datatype 'f select = select_any | select_first "('f,nat) exp"

(* Consume: how many instances of a certain fact do we need? *)
datatype 'f consume = consume_weight "('f,nat) exp"

(* Gain: extract authority from a fact *)
datatype 'f gain = gain_auth "('f,auth) exp"

(* Match puts these four components together, along with a name to bind the fact *)
datatype 'f match = match fact_var "'f gather" "'f select" "'f consume" "'f gain"

(* A rule has a rule name, a list of matches, and a 'say' expression to return the new facts *)
datatype 'f rule = rule rule_name "'f match list" "('f, 'f store) exp"

end