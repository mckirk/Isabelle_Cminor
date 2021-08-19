theory FP32
imports
  IEEE_Floating_Point.IEEE
  Word_Lib.Word_32
begin

(*
  this file is essentially a version of FP64 with all
  bit lengths adjusted for 32 bits
*)

section \<open>Concrete encodings\<close>

text \<open>Floating point operations defined as operations on words.
  Called ''fixed precision'' (fp) word in HOL4.\<close>

type_synonym float32 = "(8,23)float"
type_synonym fp32 = "32 word"

lift_definition fp32_of_float :: "float32 \<Rightarrow> fp32" is
  "\<lambda>(s::1 word, e::8 word, f::23 word). word_cat s (word_cat e f::31 word)" .

lift_definition float_of_fp32 :: "fp32 \<Rightarrow> float32" is
  "\<lambda>x. apsnd word_split (word_split x::1 word * 31 word)" .

definition "rel_fp32 \<equiv> (\<lambda>x (y::word32). x = float_of_fp32 y)"

definition eq_fp32::"float32 \<Rightarrow> float32 \<Rightarrow> bool" where [simp]: "eq_fp32 \<equiv> (=)"

lemma float_of_fp32_inverse[simp]: "fp32_of_float (float_of_fp32 a) = a"
  by (auto
      simp: fp32_of_float_def float_of_fp32_def Abs_float_inverse apsnd_def map_prod_def word_size
      dest!: word_cat_split_alt[rotated]
      split: prod.splits)

lemma float_of_fp32_inj_iff[simp]: "fp32_of_float r = fp32_of_float s \<longleftrightarrow> r = s"
  using Rep_float_inject
  by (force simp: fp32_of_float_def word_cat_inj word_size split: prod.splits)

lemma fp32_of_float_inverse[simp]: "float_of_fp32 (fp32_of_float a) = a"
  using float_of_fp32_inj_iff float_of_fp32_inverse by blast

lemma Quotientfp: "Quotient eq_fp32 fp32_of_float float_of_fp32 rel_fp32"
  \<comment>\<open>\<^term>\<open>eq_fp32\<close> is a workaround to prevent a (failing -- TODO: why?)
      code setup in \<open>setup_lifting\<close>.\<close>
  by (force intro!: QuotientI simp: rel_fp32_def)

setup_lifting Quotientfp

lift_definition fp32_lessThan::"fp32 \<Rightarrow> fp32 \<Rightarrow> bool" is
  "flt::float32\<Rightarrow>float32\<Rightarrow>bool" by simp

lift_definition fp32_lessEqual::"fp32 \<Rightarrow> fp32 \<Rightarrow> bool" is
  "fle::float32\<Rightarrow>float32\<Rightarrow>bool" by simp

lift_definition fp32_greaterThan::"fp32 \<Rightarrow> fp32 \<Rightarrow> bool" is
  "fgt::float32\<Rightarrow>float32\<Rightarrow>bool" by simp

lift_definition fp32_greaterEqual::"fp32 \<Rightarrow> fp32 \<Rightarrow> bool" is
  "fge::float32\<Rightarrow>float32\<Rightarrow>bool" by simp

lift_definition fp32_equal::"fp32 \<Rightarrow> fp32 \<Rightarrow> bool" is
  "feq::float32\<Rightarrow>float32\<Rightarrow>bool" by simp

lift_definition fp32_abs::"fp32 \<Rightarrow> fp32" is
  "abs::float32\<Rightarrow>float32" by simp

lift_definition fp32_negate::"fp32 \<Rightarrow> fp32" is
  "uminus::float32\<Rightarrow>float32" by simp

lift_definition fp32_sqrt::"roundmode \<Rightarrow> fp32 \<Rightarrow> fp32" is
  "fsqrt::roundmode\<Rightarrow>float32\<Rightarrow>float32" by simp

lift_definition fp32_add::"roundmode \<Rightarrow> fp32 \<Rightarrow> fp32 \<Rightarrow> fp32" is
  "fadd::roundmode\<Rightarrow>float32\<Rightarrow>float32\<Rightarrow>float32" by simp

lift_definition fp32_sub::"roundmode \<Rightarrow> fp32 \<Rightarrow> fp32 \<Rightarrow> fp32" is
  "fsub::roundmode\<Rightarrow>float32\<Rightarrow>float32\<Rightarrow>float32" by simp

lift_definition fp32_mul::"roundmode \<Rightarrow> fp32 \<Rightarrow> fp32 \<Rightarrow> fp32" is
  "fmul::roundmode\<Rightarrow>float32\<Rightarrow>float32\<Rightarrow>float32" by simp

lift_definition fp32_div::"roundmode \<Rightarrow> fp32 \<Rightarrow> fp32 \<Rightarrow> fp32" is
  "fdiv::roundmode\<Rightarrow>float32\<Rightarrow>float32\<Rightarrow>float32" by simp

lift_definition fp32_mul_add::"roundmode \<Rightarrow> fp32 \<Rightarrow> fp32 \<Rightarrow> fp32 \<Rightarrow> fp32" is
  "fmul_add::roundmode\<Rightarrow>float32\<Rightarrow>float32\<Rightarrow>float32\<Rightarrow>float32" by simp

end