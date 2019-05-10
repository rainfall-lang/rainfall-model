(* Expressions and rules *)
theory Exp
  imports Main "HOL-Library.Multiset"
  Base
begin

(* As the term language is standard, we use a HOAS representation with a heap that maps variable names to facts *)
datatype     fact_var = fact_var string
type_synonym fact_env = "fact_var \<Rightarrow> fact"
type_synonym 'a exp   = "fact_env \<Rightarrow> 'a"

(* Matches: there are four parts to a match: gather, select, consume, and gain. *)

(* Gather: filter input facts according to constructor name and a boolean expression.
   In the paper, this is a list of expressions, but here we just join multiple expressions with conjunction *)
datatype gather = gather_when fact_ctor "bool exp"

(* Select: gathering can return many input facts, and select specifies which of these facts to choose *)
datatype select = select_any | select_first "nat exp"

(* Consume: how many instances of a certain fact do we need? *)
datatype consume = consume_weight "nat exp"

(* Gain: extract authority from a fact *)
datatype gain = gain_auth "auth exp"

(* Match puts these four components together, along with a name to bind the fact *)
datatype match = match fact_var gather select consume gain

(* A rule has a rule name, a list of matches, and a 'say' expression to return the new facts *)
datatype rule = rule rule_name "match list" "store exp"

end