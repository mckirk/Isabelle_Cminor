theory Values imports
Main Archi AST BinNums Integers Floats
begin

(** This module defines the type of values that is used in the dynamic
  semantics of all our intermediate languages. *)

type_synonym block = positive

(** A value is either:
- a machine integer;
- a floating-point number;
- a pointer: a pair of a memory address and an integer offset with respect
  to this address;
- the [Vundef] value denoting an arbitrary bit pattern, such as the
  value of an uninitialized variable.
*)

datatype val =
    Vundef
  | Vint m_int
  | Vlong m_int64
  | Vfloat float64
  | Vsingle float32
  | Vptr block m_ptrofs

definition "Vtrue \<equiv> Vint 1"
definition "Vfalse \<equiv> Vint 0"

definition "Vnullptr \<equiv> Vlong 0"  (* only valid on 64-bit arch *)

definition Vptrofs :: "m_ptrofs \<Rightarrow> val" where
  "Vptrofs n \<equiv> Vlong n" (* only valid on 64-bit arch *)

lemma vptrofs_equ[iff]: "Vptrofs n = Vptrofs n' \<longleftrightarrow> n = n'"
  unfolding Vptrofs_def by simp

section \<open>Operations over values\<close>

(** The module [Val] defines a number of arithmetic and logical operations
  over type [val].  Most of these operations are straightforward extensions
  of the corresponding integer or floating-point operations. *)

locale Val'
begin

fun has_type :: "val \<Rightarrow> type \<Rightarrow> bool" where
  "has_type v t =
  (case (v, t) of
    (Vundef, _) \<Rightarrow> True
  | (Vint _, Tint) \<Rightarrow> True
  | (Vlong _, Tlong) \<Rightarrow> True
  | (Vfloat _, Tfloat) \<Rightarrow> True
  | (Vsingle _, Tsingle) \<Rightarrow> True
  | (Vptr _ _, Tint) \<Rightarrow> Archi.ptr64 = False
  | (Vptr _ _, Tlong) \<Rightarrow> Archi.ptr64 = True
  | (Vint _, Tany32) \<Rightarrow> True
  | (Vsingle _, Tany32) \<Rightarrow> True
  | (Vptr _ _, Tany32) \<Rightarrow> Archi.ptr64 = False
  | (_, Tany64) \<Rightarrow> True
  | (_, _) \<Rightarrow> False
  )"

fun has_rettype :: "val \<Rightarrow> rettype \<Rightarrow> bool" where
  "has_rettype v (Tret t) = has_type v t"
| "has_rettype (Vint n) Tint8signed = (n = Int.sign_ext TYPE(8) n)"
| "has_rettype (Vint n) Tint8unsigned = (n = Int.zero_ext TYPE(8) n)"
| "has_rettype (Vint n) Tint16signed = (n = Int.sign_ext TYPE(16) n)"
| "has_rettype (Vint n) Tint16unsigned = (n = Int.zero_ext TYPE(16) n)"
| "has_rettype Vundef _ = True"
| "has_rettype _ _ = False"

(** Truth values.  Non-zero integers are treated as [True].
  The integer 0 (also used to represent the null pointer) is [False].
  Other values are neither true nor false. *)

fun bool_to_val where
  "bool_to_val False = Vfalse"
| "bool_to_val True = Vtrue"

inductive bool_of_val :: "val \<Rightarrow> bool \<Rightarrow> bool" where
  bool_of_val_int: "(n \<noteq> 0) = b \<Longrightarrow> bool_of_val (Vint n) b"

lemma bool_of_val_one: "bool_of_val v False \<Longrightarrow> bool_of_val v True \<Longrightarrow> P"
  by (metis bool_of_val.cases val.inject(1))

fun bool_of_val_func :: "val \<Rightarrow> bool option" where
  "bool_of_val_func (Vint n) = (if n = 0 then Some False else Some True)"
| "bool_of_val_func _ = None"

(** Arithmetic operations *)

fun neg :: "val \<Rightarrow> val" where
  "neg (Vint n) = Vint (- n)"
| "neg _ = Vundef"

fun negf :: "val \<Rightarrow> val" where
  "negf (Vfloat f) = Vfloat (- f)"
| "negf _ = Vundef"

fun absf :: "val \<Rightarrow> val" where
  "absf (Vfloat f) = Vfloat (abs f)"
| "absf _ = Vundef"

fun negfs :: "val \<Rightarrow> val" where
  "negfs (Vsingle f) = Vsingle (- f)"
| "negfs _ = Vundef"

fun absfs :: "val \<Rightarrow> val" where
  "absfs (Vsingle f) = Vsingle (abs f)"
| "absfs _ = Vundef"

(* fun intoffloat :: "val \<Rightarrow> (val option)" where
  "intoffloat (Vfloat f) = map_option Vint (Float.to_int f)"
| "intoffloat _ = None"

fun intuoffloat :: "val \<Rightarrow> (val option)" where
  "intuoffloat (Vfloat f) = map_option Vint (Float.to_intu f)"
| "intuoffloat _ = None"

fun floatofint :: "val \<Rightarrow> (val option)" where
  "floatofint (Vint n) = Some (Vfloat (Float.of_int n))"
| "floatofint _ = None"

fun floatofintu :: "val \<Rightarrow> (val option)" where
  "floatofintu (Vint n) = Some (Vfloat (Float.of_intu n))"
| "floatofintu _ = None"

fun intofsingle :: "val \<Rightarrow> (val option)" where
  "intofsingle (Vsingle f) = map_option Vint (Float32.to_int f)"
| "intofsingle _ = None"

fun intuofsingle :: "val \<Rightarrow> (val option)" where
  "intuofsingle (Vsingle f) = map_option Vint (Float32.to_intu f)"
| "intuofsingle _ = None"

fun singleofint :: "val \<Rightarrow> (val option)" where
  "singleofint (Vint n) = Some (Vsingle (Float32.of_int n))"
| "singleofint _ = None"

fun singleofintu :: "val \<Rightarrow> (val option)" where
  "singleofintu (Vint n) = Some (Vsingle (Float32.of_intu n))"
| "singleofintu _ = None" *)

fun negint :: "val \<Rightarrow> val" where
  "negint (Vint n) = Vint (- n)"
| "negint _ = Vundef"

fun notint :: "val \<Rightarrow> val" where
  "notint (Vint n) = Vint (not n)"
| "notint _ = Vundef"

fun of_bool :: "bool \<Rightarrow> val"  where
  "of_bool True = Vtrue"
| "of_bool False = Vfalse"

fun boolval :: "val \<Rightarrow> val" where
  "boolval (Vint n) = of_bool (n \<noteq> 0)"
| "boolval (Vptr b ofs) = Vtrue"
| "boolval _ = Vundef"

fun notbool :: "val \<Rightarrow> val" where
  "notbool (Vint n) = of_bool (n = 0)"
| "notbool (Vptr b ofs) = Vfalse"
| "notbool _ = Vundef"

fun zero_ext :: "'l::len itself \<Rightarrow> val \<Rightarrow> val" where
  "zero_ext nbits (Vint n) = Vint(Int.zero_ext nbits n)"
| "zero_ext nbits _ = Vundef"

fun sign_ext :: "'l::len itself \<Rightarrow> val \<Rightarrow> val" where
  "sign_ext nbits (Vint n) = Vint(Int.sign_ext nbits n)"
| "sign_ext nbits _ = Vundef"

(* fun singleoffloat :: "val \<Rightarrow> val" where
  "singleoffloat (Vfloat f) = Vsingle (Float.to_single f)"
| "singleoffloat _ = Vundef"

fun floatofsingle :: "val \<Rightarrow> val" where
  "floatofsingle (Vsingle f) = Vfloat (Float.of_single f)"
| "floatofsingle _ = Vundef" *)

fun add :: "val \<Rightarrow> val \<Rightarrow> val" where
  "add (Vint n1) (Vint n2) = Vint(Int.add n1 n2)"
| "add (Vptr b1 ofs1) (Vint n2) = (if Archi.ptr64 then Vundef else Vptr b1 (Ptrofs.add ofs1 (Ptrofs.of_int n2)))"
| "add (Vint n1) (Vptr b2 ofs2) = (if Archi.ptr64 then Vundef else Vptr b2 (Ptrofs.add ofs2 (Ptrofs.of_int n1)))"
| "add _ _ = Vundef"

fun sub :: "val \<Rightarrow> val \<Rightarrow> val" where
  "sub v1 v2 =
  (case (v1, v2) of
    (Vint n1, Vint n2) \<Rightarrow> Vint (Int.sub n1 n2)
  | (Vptr b1 ofs1, Vint n2) \<Rightarrow> if Archi.ptr64 then Vundef else Vptr b1 (Ptrofs.sub ofs1 (Ptrofs.of_int n2))
  | (Vptr b1 ofs1, Vptr b2 ofs2) \<Rightarrow>
      if Archi.ptr64 then Vundef else
      if b1 = b2 then Vint(Ptrofs.to_int (Ptrofs.sub ofs1 ofs2)) else Vundef
  | (_, _) \<Rightarrow> Vundef
  )"

fun mul :: "val \<Rightarrow> val \<Rightarrow> val" where
  "mul (Vint n1) (Vint n2) = Vint(Int.mul n1 n2)"
| "mul _ _ = Vundef"

(* fun mulhs :: "val \<Rightarrow> val \<Rightarrow> val" where
  "mulhs (Vint n1) (Vint n2) = Vint(Int.mulhs n1 n2)"
| "mulhs _ _ = Vundef"

fun mulhu :: "val \<Rightarrow> val \<Rightarrow> val" where
  "mulhu (Vint n1) (Vint n2) = Vint(Int.mulhu n1 n2)"
| "mulhu _ _ = Vundef" *)

fun divs :: "val \<Rightarrow> val \<Rightarrow> (val option)" where
  "divs v1 v2 =
  (case (v1, v2) of
    (Vint n1, Vint n2) \<Rightarrow>
      if n2 = 0
      \<or> n1 = (Int.repr Int.min_signed) \<and> n2 = Int.mone
      then None
      else Some(Vint(Int.divs n1 n2))
  | (_, _) \<Rightarrow> None
  )"

fun mods :: "val \<Rightarrow> val \<Rightarrow> (val option)" where
  "mods v1 v2 =
  (case (v1, v2) of
    (Vint n1, Vint n2) \<Rightarrow>
      if n2 = 0
      \<or> n1 = (Int.repr Int.min_signed) \<and> n2 = Int.mone
      then None
      else Some(Vint(Int.mods n1 n2))
  | (_, _) \<Rightarrow> None
  )"

fun divu :: "val \<Rightarrow> val \<Rightarrow> (val option)" where
  "divu (Vint n1) (Vint n2) = (if n2 = 0 then None else Some(Vint(Int.divu n1 n2)))"
| "divu _ _ = None"

fun modu :: "val \<Rightarrow> val \<Rightarrow> (val option)" where
  "modu (Vint n1) (Vint n2) = (if n2 = 0 then None else Some(Vint(Int.modu n1 n2)))"
| "modu _ _ = None"

(* fun add_carry :: "val \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val" where
  "add_carry (Vint n1) (Vint n2) (Vint c) = Vint(Int.add_carry n1 n2 c)"
| "add_carry _ _ _ = Vundef"

fun sub_overflow :: "val \<Rightarrow> val \<Rightarrow> val" where
  "sub_overflow (Vint n1) (Vint n2) = Vint(Int.sub_overflow n1 n2 Int.zero)"
| "sub_overflow _ _ = Vundef"

fun negative :: "val \<Rightarrow> val" where
  "negative (Vint n) = Vint (Int.negative n)"
| "negative _ = Vundef" *)

fun and' :: "val \<Rightarrow> val \<Rightarrow> val" where
  "and' (Vint n1) (Vint n2) = Vint(Int.and' n1 n2)"
| "and' _ _ = Vundef"

fun or :: "val \<Rightarrow> val \<Rightarrow> val" where
  "or (Vint n1) (Vint n2) = Vint(Int.or n1 n2)"
| "or _ _ = Vundef"

fun xor' :: "val \<Rightarrow> val \<Rightarrow> val" where
  "xor' (Vint n1) (Vint n2) = Vint(Int.xor n1 n2)"
| "xor' _ _ = Vundef"

fun shl :: "val \<Rightarrow> val \<Rightarrow> val" where
  "shl v1 v2 =
  (case (v1, v2) of
    (Vint n1, Vint n2) \<Rightarrow>
     if Int.ltu n2 Int.iwordsize
     then Vint(Int.shl n1 n2)
     else Vundef
  | (_, _) \<Rightarrow> Vundef
  )"

fun shr :: "val \<Rightarrow> val \<Rightarrow> val" where
  "shr v1 v2 =
  (case (v1, v2) of
    (Vint n1, Vint n2) \<Rightarrow>
     if Int.ltu n2 Int.iwordsize
     then Vint(Int.shr n1 n2)
     else Vundef
  | (_, _) \<Rightarrow> Vundef
  )"

(* fun shr_carry :: "val \<Rightarrow> val \<Rightarrow> val" where
  "shr_carry v1 v2 =
  (case v1, v2 of
    Vint n1, Vint n2 \<Rightarrow>
     if Int.ltu n2 Int.iwordsize
     then Vint(Int.shr_carry n1 n2)
     else Vundef
  | _, _ \<Rightarrow> Vundef
  )" *)

(* fun shrx :: "val \<Rightarrow> val \<Rightarrow> (val option)" where
  "shrx v1 v2 =
  (case v1, v2 of
    Vint n1, Vint n2 \<Rightarrow>
     if Int.ltu n2 (Int.repr 31)
     then Some(Vint(Int.shrx n1 n2))
     else None
  | _, _ \<Rightarrow> None
  )" *)

fun shru :: "val \<Rightarrow> val \<Rightarrow> val" where
  "shru v1 v2 =
  (case (v1, v2) of
    (Vint n1, Vint n2) \<Rightarrow>
     if Int.ltu n2 Int.iwordsize
     then Vint(Int.shru n1 n2)
     else Vundef
  | (_, _) \<Rightarrow> Vundef
  )"

fun rol :: "val \<Rightarrow> val \<Rightarrow> val" where
  "rol (Vint n1) (Vint n2) = Vint(Int.rol n1 n2)"
| "rol _ _ = Vundef"

(* fun rolm :: "val \<Rightarrow> int \<Rightarrow> int \<Rightarrow> val" where
  "rolm (Vint n) amount mask = Vint(Int.rolm n amount mask)"
| "rolm _ amount mask = Vundef" *)

fun ror :: "val \<Rightarrow> val \<Rightarrow> val" where
  "ror (Vint n1) (Vint n2) = Vint(Int.ror n1 n2)"
| "ror _ _ = Vundef"

fun addf :: "val \<Rightarrow> val \<Rightarrow> val" where
  "addf (Vfloat f1) (Vfloat f2) = Vfloat(Float.add f1 f2)"
| "addf _ _ = Vundef"

fun subf :: "val \<Rightarrow> val \<Rightarrow> val" where
  "subf (Vfloat f1) (Vfloat f2) = Vfloat(Float.sub f1 f2)"
| "subf _ _ = Vundef"

fun mulf :: "val \<Rightarrow> val \<Rightarrow> val" where
  "mulf (Vfloat f1) (Vfloat f2) = Vfloat(Float.mul f1 f2)"
| "mulf _ _ = Vundef"

fun divf :: "val \<Rightarrow> val \<Rightarrow> val" where
  "divf (Vfloat f1) (Vfloat f2) = Vfloat(Float.div' f1 f2)"
| "divf _ _ = Vundef"

(* fun floatofwords :: "val \<Rightarrow> val \<Rightarrow> val" where
  "floatofwords (Vint n1) (Vint n2) = Vfloat (Float.from_words n1 n2)"
| "floatofwords _ _ = Vundef" *)

fun addfs :: "val \<Rightarrow> val \<Rightarrow> val" where
  "addfs (Vsingle f1) (Vsingle f2) = Vsingle(Float32.add f1 f2)"
| "addfs _ _ = Vundef"

fun subfs :: "val \<Rightarrow> val \<Rightarrow> val" where
  "subfs (Vsingle f1) (Vsingle f2) = Vsingle(Float32.sub f1 f2)"
| "subfs _ _ = Vundef"

fun mulfs :: "val \<Rightarrow> val \<Rightarrow> val" where
  "mulfs (Vsingle f1) (Vsingle f2) = Vsingle(Float32.mul f1 f2)"
| "mulfs _ _ = Vundef"

fun divfs :: "val \<Rightarrow> val \<Rightarrow> val" where
  "divfs (Vsingle f1) (Vsingle f2) = Vsingle(Float32.div' f1 f2)"
| "divfs _ _ = Vundef"

(** Operations on 64-bit integers *)

fun longofwords :: "val \<Rightarrow> val \<Rightarrow> val" where
  "longofwords (Vint n1) (Vint n2) = Vlong (Int64.ofwords n1 n2)"
| "longofwords _ _ = Vundef"

fun loword :: "val \<Rightarrow> val" where
  "loword (Vlong n) = Vint (Int64.loword n)"
| "loword _ = Vundef"

fun hiword :: "val \<Rightarrow> val" where
  "hiword (Vlong n) = Vint (Int64.hiword n)"
| "hiword _ = Vundef"

fun negl :: "val \<Rightarrow> val" where
  "negl (Vlong n) = Vlong (Int64.neg n)"
| "negl _ = Vundef"

fun notl :: "val \<Rightarrow> val" where
  "notl (Vlong n) = Vlong (Int64.not n)"
| "notl _ = Vundef"

fun longofint :: "val \<Rightarrow> val" where
  "longofint (Vint n) = Vlong (Int64.repr (Int.signed n))"
| "longofint _ = Vundef"

fun longofintu :: "val \<Rightarrow> val" where
  "longofintu (Vint n) = Vlong (Int64.repr (Int.unsigned n))"
| "longofintu _ = Vundef"

(* fun longoffloat :: "val \<Rightarrow> (val option)" where
  "longoffloat (Vfloat f) = map_option Vlong (Float.to_long f)"
| "longoffloat _ = None"

fun longuoffloat :: "val \<Rightarrow> (val option)" where
  "longuoffloat (Vfloat f) = map_option Vlong (Float.to_longu f)"
| "longuoffloat _ = None"

fun longofsingle :: "val \<Rightarrow> (val option)" where
  "longofsingle (Vsingle f) = map_option Vlong (Float32.to_long f)"
| "longofsingle _ = None"

fun longuofsingle :: "val \<Rightarrow> (val option)" where
  "longuofsingle (Vsingle f) = map_option Vlong (Float32.to_longu f)"
| "longuofsingle _ = None"

fun floatoflong :: "val \<Rightarrow> (val option)" where
  "floatoflong (Vlong n) = Some (Vfloat (Float.of_long n))"
| "floatoflong _ = None"

fun floatoflongu :: "val \<Rightarrow> (val option)" where
  "floatoflongu (Vlong n) = Some (Vfloat (Float.of_longu n))"
| "floatoflongu _ = None"

fun singleoflong :: "val \<Rightarrow> (val option)" where
  "singleoflong (Vlong n) = Some (Vsingle (Float32.of_long n))"
| "singleoflong _ = None"

fun singleoflongu :: "val \<Rightarrow> (val option)" where
  "singleoflongu (Vlong n) = Some (Vsingle (Float32.of_longu n))"
| "singleoflongu _ = None" *)

fun addl :: "val \<Rightarrow> val \<Rightarrow> val" where
  "addl (Vlong n1) (Vlong n2) = Vlong(Int64.add n1 n2)"
| "addl (Vptr b1 ofs1) (Vlong n2) = (if Archi.ptr64 then Vptr b1 (Ptrofs.add ofs1 (Ptrofs.of_int64 n2)) else Vundef)"
| "addl (Vlong n1) (Vptr b2 ofs2) = (if Archi.ptr64 then Vptr b2 (Ptrofs.add ofs2 (Ptrofs.of_int64 n1)) else Vundef)"
| "addl _ _ = Vundef"

fun subl :: "val \<Rightarrow> val \<Rightarrow> val" where
  "subl v1 v2 =
  (case (v1, v2) of
    (Vlong n1, Vlong n2) \<Rightarrow> Vlong(Int64.sub n1 n2)
  | (Vptr b1 ofs1, Vlong n2) \<Rightarrow>
      if Archi.ptr64 then Vptr b1 (Ptrofs.sub ofs1 (Ptrofs.of_int64 n2)) else Vundef
  | (Vptr b1 ofs1, Vptr b2 ofs2) \<Rightarrow>
      if \<not>Archi.ptr64 then Vundef else
      if b1 = b2 then Vlong(Ptrofs.to_int64 (Ptrofs.sub ofs1 ofs2)) else Vundef
  | (_, _) \<Rightarrow> Vundef
  )"

fun mull :: "val \<Rightarrow> val \<Rightarrow> val" where
  "mull (Vlong n1) (Vlong n2) = Vlong(Int64.mul n1 n2)"
| "mull _ _ = Vundef"

(* fun mull' :: "val \<Rightarrow> val \<Rightarrow> val" where
  "mull' (Vint n1) (Vint n2) = Vlong(Int64.mul' n1 n2)"
| "mull' _ _ = Vundef"

fun mullhs :: "val \<Rightarrow> val \<Rightarrow> val" where
  "mullhs (Vlong n1) (Vlong n2) = Vlong(Int64.mulhs n1 n2)"
| "mullhs _ _ = Vundef"

fun mullhu :: "val \<Rightarrow> val \<Rightarrow> val" where
  "mullhu (Vlong n1) (Vlong n2) = Vlong(Int64.mulhu n1 n2)"
| "mullhu _ _ = Vundef" *)

fun divls :: "val \<Rightarrow> val \<Rightarrow> (val option)" where
  "divls v1 v2 =
  (case (v1, v2) of
    (Vlong n1, Vlong n2) \<Rightarrow>
      if Int64.eq n2 Int64.zero
      \<or> Int64.eq n1 (Int64.repr Int64.min_signed) \<and> Int64.eq n2 Int64.mone
      then None
      else Some(Vlong(Int64.divs n1 n2))
  | (_, _) \<Rightarrow> None
  )"

fun modls :: "val \<Rightarrow> val \<Rightarrow> (val option)" where
  "modls v1 v2 =
  (case (v1, v2) of
    (Vlong n1, Vlong n2) \<Rightarrow>
      if Int64.eq n2 Int64.zero
      \<or> Int64.eq n1 (Int64.repr Int64.min_signed) \<and> Int64.eq n2 Int64.mone
      then None
      else Some(Vlong(Int64.mods n1 n2))
  | (_, _) \<Rightarrow> None
  )"

fun divlu :: "val \<Rightarrow> val \<Rightarrow> (val option)" where
  "divlu (Vlong n1) (Vlong n2) = (if Int64.eq n2 Int64.zero then None else Some(Vlong(Int64.divu n1 n2)))"
| "divlu _ _ = None"

fun modlu :: "val \<Rightarrow> val \<Rightarrow> (val option)" where
  "modlu (Vlong n1) (Vlong n2) = (if Int64.eq n2 Int64.zero then None else Some(Vlong(Int64.modu n1 n2)))"
| "modlu _ _ = None"

(* fun addl_carry :: "val \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val" where
  "addl_carry (Vlong n1) (Vlong n2) (Vlong c) = Vlong(Int64.add_carry n1 n2 c)"
| "addl_carry _ _ _ = Vundef"

fun subl_overflow :: "val \<Rightarrow> val \<Rightarrow> val" where
  "subl_overflow (Vlong n1) (Vlong n2) = Vint (Int.repr (Int64.unsigned (Int64.sub_overflow n1 n2 Int64.zero)))"
| "subl_overflow _ _ = Vundef"

fun negativel :: "val \<Rightarrow> val" where
  "negativel (Vlong n) = Vint (Int.repr (Int64.unsigned (Int64.negative n)))"
| "negativel _ = Vundef" *)

fun andl :: "val \<Rightarrow> val \<Rightarrow> val" where
  "andl (Vlong n1) (Vlong n2) = Vlong(Int64.and' n1 n2)"
| "andl _ _ = Vundef"

fun orl :: "val \<Rightarrow> val \<Rightarrow> val" where
  "orl (Vlong n1) (Vlong n2) = Vlong(Int64.or n1 n2)"
| "orl _ _ = Vundef"

fun xorl :: "val \<Rightarrow> val \<Rightarrow> val" where
  "xorl (Vlong n1) (Vlong n2) = Vlong(Int64.xor n1 n2)"
| "xorl _ _ = Vundef"

fun shll :: "val \<Rightarrow> val \<Rightarrow> val" where
  "shll v1 v2 =
  (case (v1, v2) of
    (Vlong n1, Vint n2) \<Rightarrow>
     if Int.ltu n2 Int64.iwordsize'
     then Vlong(Int64.shl' n1 n2)
     else Vundef
  | (_, _) \<Rightarrow> Vundef
  )"

fun shrl :: "val \<Rightarrow> val \<Rightarrow> val" where
  "shrl v1 v2 =
  (case (v1, v2) of
    (Vlong n1, Vint n2) \<Rightarrow>
     if Int.ltu n2 Int64.iwordsize'
     then Vlong(Int64.shr' n1 n2)
     else Vundef
  | (_, _) \<Rightarrow> Vundef
  )"

fun shrlu :: "val \<Rightarrow> val \<Rightarrow> val" where
  "shrlu v1 v2 =
  (case (v1, v2) of
    (Vlong n1, Vint n2) \<Rightarrow>
     if Int.ltu n2 Int64.iwordsize'
     then Vlong(Int64.shru' n1 n2)
     else Vundef
  | (_, _) \<Rightarrow> Vundef
  )"

(* fun shrxl :: "val \<Rightarrow> val \<Rightarrow> (val option)" where
  "shrxl v1 v2 =
  (case v1, v2 of
    Vlong n1, Vint n2 \<Rightarrow>
     if Int.ltu n2 (Int.repr 63)
     then Some(Vlong(Int64.shrx' n1 n2))
     else None
  | _, _ \<Rightarrow> None
  )"

fun shrl_carry :: "val \<Rightarrow> val \<Rightarrow> val" where
  "shrl_carry v1 v2 =
  (case v1, v2 of
    Vlong n1, Vint n2 \<Rightarrow>
     if Int.ltu n2 Int64.iwordsize'
     then Vlong(Int64.shr_carry' n1 n2)
     else Vundef
  | _, _ \<Rightarrow> Vundef
  )" *)

fun roll :: "val \<Rightarrow> val \<Rightarrow> val" where
  "roll (Vlong n1) (Vint n2) = Vlong(Int64.rol n1 (Int64.repr (Int.unsigned n2)))"
| "roll _ _ = Vundef"

fun rorl :: "val \<Rightarrow> val \<Rightarrow> val" where
  "rorl (Vlong n1) (Vint n2) = Vlong(Int64.ror n1 (Int64.repr (Int.unsigned n2)))"
| "rorl _ _ = Vundef"

(* fun rolml :: "val \<Rightarrow> int \<Rightarrow> int64 \<Rightarrow> val" where
  "rolml (Vlong n) amount mask = Vlong(Int64.rolm n (Int64.repr (Int.unsigned amount)) mask)"
| "rolml _ amount mask = Vundef" *)

fun zero_ext_l :: "'l::len itself \<Rightarrow> val \<Rightarrow> val" where
  "zero_ext_l nbits (Vlong n) = Vlong(Int64.zero_ext nbits n)"
| "zero_ext_l nbits _ = Vundef"

fun sign_ext_l :: "'l::len itself \<Rightarrow> val \<Rightarrow> val" where
  "sign_ext_l nbits (Vlong n) = Vlong(Int64.sign_ext nbits n)"
| "sign_ext_l nbits _ = Vundef"

section \<open>Comparisons\<close>

fun cmp_bool :: "comparison \<Rightarrow> val \<Rightarrow> val \<Rightarrow> (bool option)" where
  "cmp_bool c (Vint n1) (Vint n2) = Some (Int.cmp c n1 n2)"
| "cmp_bool c _ _ = None"

fun cmp_different_blocks :: "comparison \<Rightarrow> (bool option)" where
  "cmp_different_blocks Ceq = Some False"
| "cmp_different_blocks Cne = Some True"
| "cmp_different_blocks _ = None"

fun cmpf_bool :: "comparison \<Rightarrow> val \<Rightarrow> val \<Rightarrow> (bool option)" where
  "cmpf_bool c (Vfloat f1) (Vfloat f2) = Some (Float.cmp c f1 f2)"
| "cmpf_bool c _ _ = None"

fun cmpfs_bool :: "comparison \<Rightarrow> val \<Rightarrow> val \<Rightarrow> (bool option)" where
  "cmpfs_bool c (Vsingle f1) (Vsingle f2) = Some (Float32.cmp c f1 f2)"
| "cmpfs_bool c _ _ = None"

fun cmpl_bool :: "comparison \<Rightarrow> val \<Rightarrow> val \<Rightarrow> (bool option)" where
  "cmpl_bool c (Vlong n1) (Vlong n2) = Some (Int64.cmp c n1 n2)"
| "cmpl_bool c _ _ = None"

fun of_optbool :: "(bool option) \<Rightarrow> val" where
  "of_optbool (Some True) = Vtrue"
| "of_optbool (Some False) = Vfalse"
| "of_optbool None = Vundef"

fun cmp :: "comparison \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val" where
  "cmp c v1 v2 = of_optbool (cmp_bool c v1 v2)"

fun cmpf :: "comparison \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val" where
  "cmpf c v1 v2 = of_optbool (cmpf_bool c v1 v2)"

fun cmpfs :: "comparison \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val" where
  "cmpfs c v1 v2 = of_optbool (cmpfs_bool c v1 v2)"

fun cmpl :: "comparison \<Rightarrow> val \<Rightarrow> val \<Rightarrow> (val option)" where
  "cmpl c v1 v2 = map_option of_bool (cmpl_bool c v1 v2)"

context
  fixes valid_ptr :: "block \<Rightarrow> Z \<Rightarrow> bool"
begin

definition "weak_valid_ptr b ofs \<equiv> valid_ptr b ofs \<or> valid_ptr b (ofs - 1)"

fun cmpu_bool :: "comparison \<Rightarrow> val \<Rightarrow> val \<Rightarrow> (bool option)" where
  "cmpu_bool c v1 v2 =
  (case (v1, v2) of
    (Vint n1, Vint n2) \<Rightarrow>
      Some (Int.cmpu c n1 n2)
  | (Vint n1, Vptr b2 ofs2) \<Rightarrow>
      if Archi.ptr64 then None else
      if Int.eq n1 Int.zero \<and> weak_valid_ptr b2 (Ptrofs.unsigned ofs2)
      then cmp_different_blocks c
      else None
  | (Vptr b1 ofs1, Vptr b2 ofs2) \<Rightarrow>
      if Archi.ptr64 then None else
      if b1 = b2 then
        if weak_valid_ptr b1 (Ptrofs.unsigned ofs1)
           \<and> weak_valid_ptr b2 (Ptrofs.unsigned ofs2)
        then Some (Ptrofs.cmpu c ofs1 ofs2)
        else None
      else
        if valid_ptr b1 (Ptrofs.unsigned ofs1)
           \<and> valid_ptr b2 (Ptrofs.unsigned ofs2)
        then cmp_different_blocks c
        else None
  | (Vptr b1 ofs1, Vint n2) \<Rightarrow>
      if Archi.ptr64 then None else
      if Int.eq n2 Int.zero \<and> weak_valid_ptr b1 (Ptrofs.unsigned ofs1)
      then cmp_different_blocks c
      else None
  | (_, _) \<Rightarrow> None
  )"

fun cmpu :: "comparison \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val" where
  "cmpu c v1 v2 = of_optbool (cmpu_bool c v1 v2)"

fun cmplu_bool :: "comparison \<Rightarrow> val \<Rightarrow> val \<Rightarrow> (bool option)" where
  "cmplu_bool c v1 v2 =
  (case (v1, v2) of
    (Vlong n1, Vlong n2) \<Rightarrow> Some (Int64.cmpu c n1 n2)
  | (Vlong n1, Vptr b2 ofs2) \<Rightarrow>
      if \<not>Archi.ptr64 then None else
      if Int64.eq n1 Int64.zero \<and> weak_valid_ptr b2 (Ptrofs.unsigned ofs2)
      then cmp_different_blocks c
      else None
  | (Vptr b1 ofs1, Vptr b2 ofs2) \<Rightarrow>
      if \<not>Archi.ptr64 then None else
      if b1 = b2 then
        if weak_valid_ptr b1 (Ptrofs.unsigned ofs1)
           \<and> weak_valid_ptr b2 (Ptrofs.unsigned ofs2)
        then Some (Ptrofs.cmpu c ofs1 ofs2)
        else None
      else
        if valid_ptr b1 (Ptrofs.unsigned ofs1)
           \<and> valid_ptr b2 (Ptrofs.unsigned ofs2)
        then cmp_different_blocks c
        else None
  | (Vptr b1 ofs1, Vlong n2) \<Rightarrow>
      if \<not>Archi.ptr64 then None else
      if Int64.eq n2 Int64.zero \<and> weak_valid_ptr b1 (Ptrofs.unsigned ofs1)
      then cmp_different_blocks c
      else None
  | (_, _) \<Rightarrow> None
  )"

fun cmplu :: "comparison \<Rightarrow> val \<Rightarrow> val \<Rightarrow> (val option)" where
  "cmplu c v1 v2 = map_option of_bool (cmplu_bool c v1 v2)"
end

(** Add the given offset to the given pointer. *)

fun offset_ptr :: "val \<Rightarrow> m_ptrofs \<Rightarrow> val" where
  "offset_ptr (Vptr b ofs) delta = Vptr b (ofs + delta)"
| "offset_ptr _ delta = Vundef"

(** [load_result] reflects the effect of storing a value with a given
  memory chunk, then reading it back with the same chunk.  Depending
  on the chunk and the type of the value, some normalization occurs.
  For instance, consider storing the integer value [0xFFF] on 1 byte
  at a given address, and reading it back.  If it is read back with
  chunk [Mint8unsigned], zero-extension must be performed, resulting
  in [0xFF].  If it is read back as a [Mint8signed], sign-extension is
  performed and [0xFFFFFFFF] is returned. *)

fun load_result :: "memory_chunk \<Rightarrow> val \<Rightarrow> val" where
  "load_result Mint8signed (Vint n) = Vint (Int.sign_ext TYPE(8) n)"
| "load_result Mint8unsigned (Vint n) = Vint (Int.zero_ext TYPE(8) n)"
| "load_result Mint16signed (Vint n) = Vint (Int.sign_ext TYPE(16) n)"
| "load_result Mint16unsigned (Vint n) = Vint (Int.zero_ext TYPE(16) n)"
| "load_result Mint32 (Vint n) = Vint n"
| "load_result Mint32 (Vptr b ofs) = (if Archi.ptr64 then Vundef else Vptr b ofs)"
| "load_result Mint64 (Vlong n) = Vlong n"
| "load_result Mint64 (Vptr b ofs) = (if Archi.ptr64 then Vptr b ofs else Vundef)"
| "load_result Mfloat32 (Vsingle f) = Vsingle f"
| "load_result Mfloat64 (Vfloat f) = Vfloat f"
| "load_result Many32 (Vint n) = Vint n"
| "load_result Many32 (Vsingle f) = Vsingle f"
| "load_result Many32 (Vptr b ofs) = (if Archi.ptr64 then Vundef else Vptr b ofs)"
| "load_result Many64 v = v"
| "load_result _ _ = Vundef"

(** The ``is less defined'' relation between values.
    A value is less defined than itself, and [Vundef] is
    less defined than any value. *)

inductive lessdef :: "val \<Rightarrow> val \<Rightarrow> bool" where
    lessdef_refl: "lessdef v v"
  | lessdef_undef: "lessdef Vundef v"

inductive lessdef_list :: "val list \<Rightarrow> val list \<Rightarrow> bool" where
    lessdef_list_nil:
      "lessdef_list [] []"
  | lessdef_list_cons:
      "lessdef v1 v2 \<Longrightarrow> lessdef_list vl1 vl2 \<Longrightarrow>
      lessdef_list (v1 # vl1) (v2 # vl2)"

section \<open>Values and memory injections\<close>

(** A memory injection [f] is a function from addresses to either [None]
  or [Some] of an address and an offset.  It defines a correspondence
  between the blocks of two memory states [m1] and [m2]:
- if [f b = None], the block [b] of [m1] has no equivalent in [m2];
- if [f b = Some(b', ofs)], the block [b] of [m2] corresponds to
  a sub-block at offset [ofs] of the block [b'] in [m2].
*)

type_synonym meminj = "block \<Rightarrow> (block * Z) option"

(** A memory injection defines a relation between values that is the
  identity relation, except for pointer values which are shifted
  as prescribed by the memory injection.  Moreover, [Vundef] values
  inject into any other value. *)

inductive inject :: "meminj \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool" where
    inject_int:
      "inject mi (Vint i) (Vint i)"
  | inject_long:
      "inject mi (Vlong i) (Vlong i)"
  | inject_float:
      "inject mi (Vfloat f) (Vfloat f)"
  | inject_single:
      "inject mi (Vsingle f) (Vsingle f)"
  | inject_ptr:
      "mi b1 = Some (b2, delta) \<Longrightarrow>
      ofs2 = ofs1 + (Int64.repr delta) \<Longrightarrow>
      inject mi (Vptr b1 ofs1) (Vptr b2 ofs2)"
  | val_inject_undef:
      "inject mi Vundef v"

inductive inject_list :: "meminj \<Rightarrow> val list \<Rightarrow> val list \<Rightarrow> bool" where
    inject_list_nil:
      "inject_list mi [] []"
  | inject_list_cons:
      "inject mi v v' \<Longrightarrow> inject_list mi vl vl' \<Longrightarrow>
      inject_list mi (v # vl) (v' # vl')"

end (* locale Val' *)

interpretation Val: Val' .

type_synonym meminj = Val.meminj

(** Monotone evolution of a memory injection. *)

definition inject_incr :: "meminj \<Rightarrow> meminj \<Rightarrow> bool" where
  "inject_incr f1 f2 \<equiv> \<forall> b b' delta. f1 b = Some(b', delta) \<longrightarrow> f2 b = Some(b', delta)"

(** The identity injection gives rise to the "less defined than" relation. *)

definition inject_id :: meminj where
  "inject_id b \<equiv> Some (b, 0)"


end