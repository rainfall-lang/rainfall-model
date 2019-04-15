(* Example programs and evaluations *)
theory Examples
  imports Dynamic
begin


(* Examples to make sure find_firsts works *)
definition mk_vfact :: "string \<Rightarrow> val \<Rightarrow> fact" where
"mk_vfact nm v = \<lparr>fact_name=fact_ctor ''fact'', fact_value = v, fact_by = {party nm}, fact_obs = {}, fact_rules = {}\<rparr>"

definition vnat :: "nat \<Rightarrow> val" where
"vnat i = vlit (lnat i)"

lemma "find_firsts {# mk_vfact ''alice'' (vnat 0), mk_vfact ''bob'' (vnat 1), mk_vfact ''charlie'' (vnat 0)#}
   (\<lambda>_. undefined) (fact_var ''x'') (\<lambda>s. case fact_value (s (fact_var ''x'')) of vlit (lnat i) \<Rightarrow> i)
= {# \<lparr>fact_name = fact_ctor ''fact'', fact_value = vlit (lnat 0), fact_by = {party ''alice''}, fact_obs = {}, fact_rules = {}\<rparr>,
  \<lparr>fact_name = fact_ctor ''fact'', fact_value = vlit (lnat 0), fact_by = {party ''charlie''}, fact_obs = {},
     fact_rules = {}\<rparr>
  #}"
  by eval


end