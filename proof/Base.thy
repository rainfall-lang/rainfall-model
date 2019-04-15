(* Base types *)
theory Base
  imports Main "HOL-Library.Multiset" "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools"
begin

(* A party is a participant, and auth is a set of participant authorities *)
datatype party      = party string
type_synonym auth   = "party set"

datatype symbol     = symbol string
datatype rule_name  = rule_name string

(* Literals and values that can be stored in a fact *)
datatype lit =
    lnat nat
  | lbool bool
  | lunit
  | lparty party
  | lauth auth
  | lsymbol symbol
  | lrule rule_name

datatype field_name = field_name string
datatype val =
    vlit lit
  | vrecord "(field_name \<times> val) list"
  | vlist "val list"

(* Facts *)
datatype fact_ctor = fact_ctor string
record fact =
  fact_name  :: fact_ctor
  fact_value :: val
  fact_by    :: auth
  fact_obs   :: auth
  fact_rules :: "rule_name set"

type_synonym store = "fact multiset"

end