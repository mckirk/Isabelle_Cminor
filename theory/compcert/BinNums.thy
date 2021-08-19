theory BinNums imports Main "Word_Lib.Bits_Int" begin

section \<open>Positive\<close>

type_synonym positive = num

instantiation num :: semiring_numeral
begin
definition "one_num \<equiv> Num.One"
instance
  apply standard
proof -
  fix a b c :: num
  show "a * b * c = a * (b * c)"
    by (metis (no_types, lifting) mult_numeral_left_semiring_numeral numeral_eq_iff numeral_times_numeral)

  show "1 * a = a"
    by (simp add: one_num_def)

  show "a * 1 = a"
    by (simp add: one_num_def)

  show "a + b + c = a + (b + c)"
  proof -
    have "numeral (a + b + c) = (numeral a::nat) + (numeral b + numeral c)"
      by (metis (full_types) group_cancel.add1 numeral_plus_numeral)
    then show ?thesis
      by auto
  qed

  show "a + b = b + a"
  proof -
    have "(numeral (a + b)::nat) = numeral (b + a)"
      by (metis add.commute numeral_plus_numeral)
    then show ?thesis
      by force
  qed

  show "(a + b) * c = a * c + b * c"
    unfolding times_num_def
    by (metis add_mult_distrib nat_of_num_mult nat_of_num_numeral num_eq_iff numeral_plus_numeral times_num_def)

  show "a * (b + c) = a * b + a * c"
    unfolding times_num_def
    by (metis distrib_left_numeral nat_of_num_mult nat_of_num_numeral numeral_plus_numeral plus_num_def times_num_def)
qed
end

instantiation num :: strict_ordered_ab_semigroup_add
begin
instance proof (standard, goal_cases)
  case (1 a b c)
  then show ?case
    unfolding less_eq_num_def
    by (simp add: nat_of_num_add)
next
  case (2 a b c d)
  then show ?case
    unfolding less_num_def
    by (simp add: nat_of_num_add)
  qed
end

instantiation num :: order_bot
begin
definition "bot_num \<equiv> (1::num)"
instance
  apply standard
  unfolding bot_num_def one_num_def
  by (simp)
end

lemma [simp]: "(p::positive) + p' \<le> p = False"
  by (smt (verit) add_cancel_left_right add_less_same_cancel1 antisym_conv2 less_add_same_cancel1 nat_1_add_1 not_numeral_less_one numeral_le_iff numeral_plus_numeral one_less_numeral_iff order.strict_trans semiring_norm(76))
lemma [simp]: "(p::positive) + p' \<le> p' = False"
proof -
  have "\<forall>n. \<not> num.One + n \<le> n"
    by (metis (no_types) add_le_same_cancel2 not_one_le_zero numeral_le_iff one_plus_numeral)
  then show ?thesis
    by (meson add_mono semiring_norm(68))
qed

lemma pos_geq_1[iff]: "b \<ge> 1" for b :: positive
  by (simp add: one_num_def)

lemma pos_lt_1[simp]: "b < 1 = False" for b :: positive
  by (simp add: one_num_def)

lemma pos_less_plus[iff]: "p < p + 1" for p :: positive
  unfolding one_num_def less_num_def
  by (simp add: nat_of_num_add)

lemma pos_less_trans: "p < p' \<Longrightarrow> p < p' + 1" for p :: positive
  unfolding one_num_def less_num_def
  by (simp add: nat_of_num_add)

lemma pos_larger: "p + 1 \<le> p' \<Longrightarrow> p \<le> p'" for p :: positive
  by (meson leD leI pos_less_trans)

lemma pos_less_pos_plus1: "(p' < p + 1) = (p' = p \<or> p' < p)"  for p :: positive
  unfolding plus_num_def less_num_def
  by (smt (verit, del_insts) int_eq_iff_numeral int_ops(2) nat_of_num_inverse nat_of_num_numeral nat_of_num_pos num_of_nat_inverse numerals(1) of_nat_add of_nat_less_iff one_num_def)


section \<open>Z\<close>

type_synonym Z = int

end