theory Integers
  imports
Main Archi "Word_Lib.Bitwise" "Word_Lib.Bits_Int"
begin

(** * Comparisons *)

datatype comparison =
    Ceq (* same *)
  | Cne (* different *)
  | Clt (* less than *)
  | Cle (* less than or equal *)
  | Cgt (* greater than *)
  | Cge (* greater than or equal *)

fun do_cmp :: "comparison \<Rightarrow> 'a::ord \<Rightarrow> 'a \<Rightarrow> bool" where
  "do_cmp Ceq x y = (x = y)"
| "do_cmp Cne x y = (x \<noteq> y)"
| "do_cmp Clt x y = (x < y)"
| "do_cmp Cle x y = (x \<le> y)"
| "do_cmp Cgt x y = (x > y)"
| "do_cmp Cge x y = (x \<ge> y)"

(*
  from here on out, the formalization diverges from CompCert
  to make use of the already existing Word_Lib
*)

type_synonym m_byte = "8 word"
type_synonym m_short = "16 word"
type_synonym m_int = "32 word"
type_synonym m_int64 = "64 word"
type_synonym m_ptrofs = "ptrsize word"

locale Make =
  fixes wt :: "'w::len itself"
begin
definition "wordsize \<equiv> LENGTH('w)"
definition "zwordsize \<equiv> int wordsize"

definition modulus :: int where "modulus \<equiv> 2 ^ wordsize"
definition "half_modulus \<equiv> modulus div 2"
definition "max_unsigned \<equiv> modulus - 1"
definition "max_signed \<equiv> half_modulus - 1"
definition "min_signed \<equiv> -half_modulus"

(** The [unsigned] and [signed] functions return the Coq integer corresponding
  to the given machine integer, interpreted as unsigned or signed
  respectively. *)

abbreviation unsigned :: "'w word \<Rightarrow> int" where
  "unsigned \<equiv> uint"
abbreviation signed :: "'w word \<Rightarrow> int" where
  "signed \<equiv> sint"

(** Conversely, [repr] takes a Coq integer and returns the corresponding
  machine integer.  The argument is treated modulo [modulus]. *)

abbreviation repr :: "int \<Rightarrow> 'w word" where
  "repr \<equiv> word_of_int"

definition "iwordsize \<equiv> repr zwordsize"
definition "zero \<equiv> 0"
definition "mone \<equiv> repr (-1)"

lemma repr_mod: "repr (i mod 2 ^ x) = repr i" if "x \<ge> LENGTH('w)"
  unfolding repr_def
  using that
  by transfer (metis bintrunc_bintrunc_ge no_bintr_alt1)

lemma unsigned_ge_neg[iff]: "i \<le> 0 \<Longrightarrow> i \<le> unsigned w"
  using dual_order.trans by auto

(** * Arithmetic and logical operations over machine integers *)

fun eq :: "'w word \<Rightarrow> 'w word \<Rightarrow> bool" where
  "eq x y = ((unsigned x) = (unsigned y))"

fun lt :: "'w word \<Rightarrow> 'w word \<Rightarrow> bool" where
  "lt x y = ((signed x) < (signed y))"

fun ltu :: "'w word \<Rightarrow> 'w word \<Rightarrow> bool" where
  "ltu x y = ((unsigned x) < (unsigned y))"

fun neg :: "'w word \<Rightarrow> 'w word" where
  "neg x = repr (- unsigned x)"

fun add :: "'w word \<Rightarrow> 'w word \<Rightarrow> 'w word" where
  "add x y = repr (unsigned x + unsigned y)"

fun sub :: "'w word \<Rightarrow> 'w word \<Rightarrow> 'w word" where
  "sub x y = repr (unsigned x - unsigned y)"

fun mul :: "'w word \<Rightarrow> 'w word \<Rightarrow> 'w word" where
  "mul x y = repr (unsigned x * unsigned y)"

fun divs :: "'w word \<Rightarrow> 'w word \<Rightarrow> 'w word" where
  "divs x y = repr ((signed x) div (signed y))"

fun mods :: "'w word \<Rightarrow> 'w word \<Rightarrow> 'w word" where
  "mods x y = repr ((signed x) mod (signed y))"

fun divu :: "'w word \<Rightarrow> 'w word \<Rightarrow> 'w word" where
  "divu x y = repr (unsigned x div unsigned y)"

fun modu :: "'w word \<Rightarrow> 'w word \<Rightarrow> 'w word" where
  "modu x y = repr ((unsigned x) mod (unsigned y))"

(** Bitwise boolean operations. *)

abbreviation and' :: "'w word \<Rightarrow> 'w word \<Rightarrow> 'w word" where
  "and' x y \<equiv> x AND y"

abbreviation or :: "'w word \<Rightarrow> 'w word \<Rightarrow> 'w word" where
  "or x y \<equiv> x OR y"

abbreviation xor :: "'w word \<Rightarrow> 'w word \<Rightarrow> 'w word" where
  "xor x y \<equiv> x XOR y"

abbreviation not :: "'w word \<Rightarrow> 'w word" where
  "not \<equiv> NOT"

(** Shifts and rotates. *)

fun shl :: "'w word \<Rightarrow> 'w word \<Rightarrow> 'w word" where
  "shl x y = x << (nat (uint y))"

fun shru :: "'w word \<Rightarrow> 'w word \<Rightarrow> 'w word" where
  "shru x y = x >> (nat (uint y))"

fun shr :: "'w word \<Rightarrow> 'w word \<Rightarrow> 'w word" where
  "shr x y = x >>> (nat (uint y))" (* Standard shr is signed in CompCert *)

fun rol :: "'w word \<Rightarrow> 'w word \<Rightarrow> 'w word" where
  "rol x y =
  (let n = nat ((unsigned y) mod zwordsize) in
  repr (((unsigned x) << n) OR ((unsigned x) >> (nat zwordsize - n))))"

fun ror :: "'w word \<Rightarrow> 'w word \<Rightarrow> 'w word" where
  "ror x y =
  (let n = nat ((unsigned y) mod zwordsize) in
  repr (((unsigned x) >> n) OR ((unsigned x) << (nat zwordsize - n))))"

(** Zero and sign extensions *)

fun zero_ext :: "'from::len itself \<Rightarrow> 'w word \<Rightarrow> 'w word" where
  "zero_ext from x = ucast (ucast x :: 'from word)"

fun sign_ext :: "'from::len itself \<Rightarrow> 'w word \<Rightarrow> 'w word" where
  "sign_ext from x = scast (ucast x :: 'from word)"

(** Comparisons *)

fun cmp :: "comparison \<Rightarrow> 'w word \<Rightarrow> 'w word \<Rightarrow> bool" where
  "cmp Ceq x y = eq x y"
| "cmp Cne x y = (\<not>eq x y)"
| "cmp Clt x y = lt x y"
| "cmp Cle x y = (\<not>lt y x)"
| "cmp Cgt x y = lt y x"
| "cmp Cge x y = (\<not>lt x y)"

fun cmpu :: "comparison \<Rightarrow> 'w word \<Rightarrow> 'w word \<Rightarrow> bool" where
  "cmpu Ceq x y = eq x y"
| "cmpu Cne x y = (\<not>eq x y)"
| "cmpu Clt x y = ltu x y"
| "cmpu Cle x y = (\<not>ltu y x)"
| "cmpu Cgt x y = ltu y x"
| "cmpu Cge x y = (\<not>ltu x y)"

end

global_interpretation Byte : Make "TYPE(8)"
  done
global_interpretation Short : Make "TYPE(16)"
  done
global_interpretation Int : Make "TYPE(32)"
  done

locale Make64 = Make "TYPE(64)"
begin
definition "iwordsize' \<equiv> Int.repr zwordsize"

(** Shifts with amount given as a 32-bit integer *)

fun shl' :: "64 word \<Rightarrow> 32 word \<Rightarrow> 64 word" where
  "shl' x y = x << (nat (Int.unsigned y))"

fun shru' :: "64 word \<Rightarrow> 32 word \<Rightarrow> 64 word" where
  "shru' x y = x >> (nat (Int.unsigned y))"

fun shr' :: "64 word \<Rightarrow> 32 word \<Rightarrow> 64 word" where
  "shr' x y = x >>> (nat (Int.unsigned y))"

fun rol' :: "64 word \<Rightarrow> 32 word \<Rightarrow> 64 word" where
  "rol' x y =
  (let n = nat ((Int.unsigned y) mod zwordsize) in
  repr (((unsigned x) << n) OR ((unsigned x) >> (nat zwordsize - n))))"

fun ror' :: "64 word \<Rightarrow> 32 word \<Rightarrow> 64 word" where
  "ror' x y =
  (let n = nat ((Int.unsigned y) mod zwordsize) in
  repr (((unsigned x) >> n) OR ((unsigned x) << (nat zwordsize - n))))"

(** Decomposing 64-bit ints as pairs of 32-bit ints *)

fun loword :: "64 word \<Rightarrow> 32 word" where
  "loword n = Int.repr (unsigned n)"

fun hiword :: "64 word \<Rightarrow> 32 word" where
  "hiword n = Int.repr (unsigned (shru n (repr Int.zwordsize)))"

fun ofwords :: "32 word \<Rightarrow> 32 word \<Rightarrow> 64 word" where
  "ofwords hi lo = or (shl (repr (Int.unsigned hi)) (repr Int.zwordsize)) (repr (Int.unsigned lo))"
end

global_interpretation Int64 : Make64
  done


locale Ptrofs' = u: Make "TYPE(ptrsize)"
begin
(* need to redefine so its visible on the outside ... *)
abbreviation unsigned :: "ptrsize word \<Rightarrow> int"
  where "unsigned \<equiv> u.unsigned"
abbreviation repr :: "int \<Rightarrow> ptrsize word"
  where "repr \<equiv> u.repr"

abbreviation "add \<equiv> u.add"
abbreviation "sub \<equiv> u.sub"

abbreviation "cmp \<equiv> u.cmp"
abbreviation "cmpu \<equiv> u.cmpu"

fun to_int where "to_int x = Int.repr (unsigned x)"
fun of_int where "of_int i = repr (Int.unsigned i)"
fun to_int64 where "to_int64 x = Int64.repr (unsigned x)"
fun of_int64 where "of_int64 i = repr (Int64.unsigned i)"
end

global_interpretation Ptrofs : Ptrofs' .

lemma word_mod[simp]: "x = 2^LENGTH('w::len) \<Longrightarrow> word_of_int (i mod x) = (word_of_int i :: ('w word))"
  using word_uint.Abs_norm by simp

end