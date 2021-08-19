theory Mini_SepLogic
imports Sep_Generic_Wp
begin

record state = counter:: nat
type_synonym state_abstract = "nat tsa_opt"

definition \<alpha> :: "state \<Rightarrow> state_abstract" where
  "\<alpha> s \<equiv> TRIV (counter s)"

type_synonym state_assn = "state_abstract \<Rightarrow> bool"

definition counter_assn :: "nat \<Rightarrow> state_assn" where
  "counter_assn v \<equiv> EXACT (TRIV v)"

lemma counter_is: "(counter_assn v ** F) (\<alpha> s) \<longleftrightarrow> counter s = v \<and> F 0"
  unfolding counter_assn_def \<alpha>_def
  apply standard
   apply (erule sep_conjE)
   apply (metis EXACT_def TRIV_disj_simps(1) tsa_opt.inject unique_zero_simps(2) zero_tsa_opt_def)
  apply (rule sep_conjI[of _  _  _ 0])
  by auto

type_synonym op = "state \<Rightarrow> (nat \<times> state)"

definition op_inc :: op where
  "op_inc s \<equiv> (counter s, counter_update ((+) 1) s)"

definition op_seq :: "op \<Rightarrow> op \<Rightarrow> op" where
  "op_seq o1 o2 s \<equiv> case o1 s of (r1, s1') \<Rightarrow> o2 s1'"

notation op_seq ("_ ; _")

definition wp :: "'e \<Rightarrow> op \<Rightarrow> (nat \<Rightarrow> state \<Rightarrow> bool) \<Rightarrow> state \<Rightarrow> bool" where
  "wp e c Q s \<equiv> case c s of (r, s') \<Rightarrow> Q r s'"

interpretation generic_wp wp
  unfolding wp_def
  by standard auto

lemma seq_decomp[vcg_decomp_rules]:
  assumes "wp e o1 (\<lambda>r1. wp e o2 Q) s"
  shows "wp e (op_seq o1 o2) Q s"
  using assms unfolding wp_def op_seq_def
  by auto

abbreviation "I\<^sub>c s \<equiv> counter s > 23"

lemma ht_inc[vcg_rules]:
  "htriple e \<alpha> I\<^sub>c
  (counter_assn c)
  (op_inc)
  (\<lambda>r. \<up>(r = c) ** counter_assn (c+1))"
  apply (rule htripleI)
  unfolding wp_def op_inc_def
  by (auto simp: counter_is pred_lift_extract_simps(2))

lemma ht_incinc:
  "htriple e \<alpha> I\<^sub>c
  (counter_assn 41)
  (op_inc; op_inc)
  (\<lambda>r. \<up>(r = 42) ** counter_assn (43))"
  by vcg

end