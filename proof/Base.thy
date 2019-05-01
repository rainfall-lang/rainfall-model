(* Base types *)
theory Base
  imports Main "HOL-Library.Multiset" "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools"
begin

(* A party is a participant, and auth is a set of participant authorities *)
datatype party      = party string
type_synonym auth   = "party set"

datatype symbol     = symbol string
datatype rule_name  = rule_name string

(* Facts are parameterised by the value type *)
datatype fact_ctor = fact_ctor string
record 'a fact =
  fact_name  :: fact_ctor
  fact_value :: 'a
  fact_by    :: auth
  fact_obs   :: auth
  fact_rules :: "rule_name set"

(* All facts in the same store have the same value type.
   For a fully shallow embedding, it might be convenient to have a separate store for each different fact type.
   Then each different fact ctor could have a different type of values *)
type_synonym 'a store = "'a fact multiset"
type_synonym 'a factoid = "'a fact \<times> nat"

end