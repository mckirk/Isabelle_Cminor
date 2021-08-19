theory Floats
  imports Main IEEE_Floating_Point.FP64 FP32 Integers
begin

(* use IEEE_Floating_Point for float types *)

lemma "is_single (f::float32 itself)"
  unfolding is_single_def wordlength_def by simp
lemma "is_double (f::float64 itself)"
  unfolding is_double_def wordlength_def by simp

abbreviation "Float32_repr i \<equiv> float_of_fp32 (word_of_int i)"
abbreviation "Float64_repr i \<equiv> float_of_fp64 (word_of_int i)"

instantiation float :: (len, len) equal
begin

lift_definition equal_float :: "('a, 'b) IEEE.float \<Rightarrow> ('a, 'b) IEEE.float \<Rightarrow> bool" is
  "(=)"
  done

instance
  apply standard
  apply transfer
  by simp
end

locale FloatOps =
  fixes ft :: "('a,'b) float itself"
begin
abbreviation add :: "('a,'b) float \<Rightarrow> ('a,'b) float \<Rightarrow> ('a,'b) float" where
  "add \<equiv> (+)"
abbreviation sub :: "('a,'b) float \<Rightarrow> ('a,'b) float \<Rightarrow> ('a,'b) float" where
  "sub \<equiv> (-)"
abbreviation mul :: "('a,'b) float \<Rightarrow> ('a,'b) float \<Rightarrow> ('a,'b) float" where
  "mul \<equiv> (*)"
abbreviation div' :: "('a,'b) float \<Rightarrow> ('a,'b) float \<Rightarrow> ('a,'b) float" where
  "div' \<equiv> (/)"

abbreviation cmp :: "comparison \<Rightarrow> ('a,'b) float \<Rightarrow> ('a,'b) float \<Rightarrow> bool" where
  "cmp \<equiv> do_cmp"
end

interpretation Float : FloatOps "TYPE(float64)" .
interpretation Float32 : FloatOps "TYPE(float32)" .

end