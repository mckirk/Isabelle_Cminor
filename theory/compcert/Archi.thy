theory Archi 
  imports Main "HOL-Library.Type_Length"
begin

(** Architecture-dependent parameters for x86 in 64-bit mode *)

definition "big_endian \<equiv> False"
definition "ptr64 \<equiv> True"

lemma [simp]: "ptr64" unfolding ptr64_def by simp

type_synonym ptrsize = 64

definition arch_max_size :: int where "arch_max_size \<equiv> 2^(LENGTH(ptrsize))"

end