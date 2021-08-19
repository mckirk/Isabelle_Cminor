theory Smallstep
imports Events Globalenvs Integers
begin

(** Tools for small-step operational semantics *)

(** This module defines generic operations and theorems over
  the one-step transition relations that are used to specify
  operational semantics in small-step style. *)

locale smallstep =
  fixes step :: "'s \<Rightarrow> trace \<Rightarrow> 's \<Rightarrow> bool"
begin

inductive star :: "'s \<Rightarrow> trace \<Rightarrow> 's \<Rightarrow> bool" where
  star_refl: "star s E0 s"
| star_step: "step s1 t1 s2 \<Longrightarrow> star s2 t2 s3 \<Longrightarrow> t = List.append t1 t2 \<Longrightarrow>
      star s1 t s3"

lemma star_one: "step s1 t s2 \<Longrightarrow> star s1 t s2"
  by (metis (full_types) append_Nil2 star.simps)

lemma star_trans: "star s1 t1 s2 \<Longrightarrow> star s2 t2 s3 \<Longrightarrow> star s1 (List.append t1 t2) s3"
  apply (induction rule: star.induct)
  apply simp
  by (simp add: smallstep.star_step)+

lemma star_trans2: "star s1 t1 s2 \<Longrightarrow> star s2 t2 s3 \<Longrightarrow> star s3 t3 s4 \<Longrightarrow> star s1 (t1 @ t2 @ t3) s4"
  by (simp add: star_trans)

lemma star_destruct:
  assumes "star s1 t s2"
  shows "s1 \<noteq> s2 \<Longrightarrow> \<exists> s1' t1 t2. (step s1 t1 s1' \<and> star s1' t2 s2 \<and> t = t1 @ t2)"
  by (metis assms star.cases)

end


(* more lemmas for our deterministic case; CompCert doesn't have this *)
locale smallstep_determ = smallstep step
  for step :: "'s \<Rightarrow> trace \<Rightarrow> 's \<Rightarrow> bool" +
  assumes determ: "step s t1 s1' \<Longrightarrow> step s t2 s2' \<Longrightarrow> (t1 = t2 \<and> s1' = s2')"
begin

(* if there's a step from s1 to s2 and s3 \<noteq> s1,
  then reaching s3 from s1 is equivalent to reaching s3 from s2 *)
lemma star_step_subst:
  assumes "step s1 t1 s2"
  shows "s1 \<noteq> s3 \<Longrightarrow> t = List.append t1 t2 \<Longrightarrow>
      star s1 t s3 = star s2 t2 s3"
  apply standard
   apply (metis assms determ same_append_eq star_destruct)
  using assms star_step by auto
end

end