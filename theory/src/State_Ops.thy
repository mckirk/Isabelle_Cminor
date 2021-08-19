theory State_Ops
imports Sep_Generic_Wp
begin

section \<open>Generic State Ops\<close>

datatype ('c, 'r) state_op =
    Read "'c \<Rightarrow> 'r" | Update "'c \<Rightarrow> 'c"
  | Maybe "'r option" | ReadMaybe "'c \<Rightarrow> 'r option" | UpdateMaybe "'c \<Rightarrow> 'c option"
  | ReadUpdate "'c \<Rightarrow> 'c \<times> 'r"

definition "r_dummy \<equiv> undefined"

fun wp_stateop where
  "wp_stateop (Read f) Q s = Q (f s) s"
| "wp_stateop (Update f) Q s = Q r_dummy (f s)"
| "wp_stateop (Maybe opt) Q s = (case opt of Some r \<Rightarrow> Q r s | None \<Rightarrow> False)"
| "wp_stateop (ReadMaybe f) Q s = (case f s of Some r \<Rightarrow> Q r s | None \<Rightarrow> False)"
| "wp_stateop (UpdateMaybe f) Q s = (case f s of Some s' \<Rightarrow> Q r_dummy s' | None \<Rightarrow> False)"
| "wp_stateop (ReadUpdate f) Q s = (case f s of (s', r) \<Rightarrow> Q r s')"

lemma wp_stateopI:
  "\<And>f. Q (f s) s \<Longrightarrow> wp_stateop (Read f) Q s"
  "\<And>f. Q r_dummy (f s) \<Longrightarrow> wp_stateop (Update f) Q s"
  "\<And>opt r. opt = Some r \<Longrightarrow> Q r s \<Longrightarrow> wp_stateop (Maybe opt) Q s"
  "\<And>f r. f s = Some r \<Longrightarrow> Q r s \<Longrightarrow> wp_stateop (ReadMaybe f) Q s"
  "\<And>f s'. f s = Some s' \<Longrightarrow> Q r_dummy s' \<Longrightarrow> wp_stateop (UpdateMaybe f) Q s"
  "\<And>f s' r. f s = (s', r) \<Longrightarrow> Q r s' \<Longrightarrow> wp_stateop (ReadUpdate f) Q s"
  by (auto)

lemma wp_stateopE[elim!]:
  assumes "wp_stateop c Q s"
  obtains
    ("Read") f r where "c = Read f" and "r = f s" and "Q r s"
  | ("Update") f s' where "c = Update f" and "s' = f s" and "Q r_dummy s'"
  | ("Maybe") opt r where "c = Maybe opt" and "opt = Some r" and "Q r s"
  | ("ReadMaybe") f r where "c = ReadMaybe f" and "f s = Some r" and "Q r s"
  | ("UpdateMaybe") f s' where "c = UpdateMaybe f" and "f s = Some s'" and "Q r_dummy s'"
  | ("ReadUpdate") f s' r where "c = ReadUpdate f" and "f s = (s', r)" and "Q r s'"
  apply (rule wp_stateop.elims(2)[OF assms])
  by (auto split: option.splits)

interpretation state_op: generic_wp "\<lambda>_. wp_stateop"
  apply standard
  subgoal for e c Q Q'
    apply (cases c; standard+)
    by (auto split: option.splits)
  done

abbreviation "state_ht \<equiv> state_op.htriple ()"

lemmas state_htI = state_op.htripleI

inductive readonly_op where
  "readonly_op (Read f)" | "readonly_op (Maybe opt)" | "readonly_op (ReadMaybe f)"
declare readonly_op.cases[elim]
declare readonly_op.intros[intro]

inductive_simps [iff]: "readonly_op (Read f)"
inductive_simps [iff]: "readonly_op (Maybe opt)"
inductive_simps [iff]: "readonly_op (ReadMaybe f)"

lemma wp_readonly_op:
  "readonly_op c \<Longrightarrow> wp_stateop c Q s \<longleftrightarrow> wp_stateop c (\<lambda>r _. Q r s) s"
  apply (erule readonly_op.cases)
  by auto

end