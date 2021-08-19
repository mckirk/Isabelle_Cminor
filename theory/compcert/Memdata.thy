theory Memdata
  imports Main Integers Values AST Archi
begin

(** In-memory representation of values. *)

section \<open>Properties of memory chunks\<close>

(** Memory reads and writes are performed by quantities called memory chunks,
  encoding the type, size and signedness of the chunk being addressed.
  The following functions extract the size information from a chunk. *)

fun size_chunk_nat :: "memory_chunk \<Rightarrow> nat" where
  "size_chunk_nat Mint8signed = 1"
| "size_chunk_nat Mint8unsigned = 1"
| "size_chunk_nat Mint16signed = 2"
| "size_chunk_nat Mint16unsigned = 2"
| "size_chunk_nat Mint32 = 4"
| "size_chunk_nat Mint64 = 8"
| "size_chunk_nat Mfloat32 = 4"
| "size_chunk_nat Mfloat64 = 8"
| "size_chunk_nat Many32 = 4"
| "size_chunk_nat Many64 = 8"

lemma size_chunk_nat_pos[iff]: "0 < size_chunk_nat chunk"
  by (cases chunk) auto

fun size_chunk :: "memory_chunk \<Rightarrow> Z" where
  "size_chunk chunk = int (size_chunk_nat chunk)"

(** Memory reads and writes must respect alignment constraints:
  the byte offset of the location being addressed should be an exact
  multiple of the natural alignment for the chunk being addressed.
  This natural alignment is defined by the following
  [align_chunk] function.  Some target architectures
  (e.g. PowerPC and x86) have no alignment constraints, which we could
  reflect by taking [align_chunk chunk = 1].  However, other architectures
  have stronger alignment requirements.  The following definition is
  appropriate for PowerPC, ARM and x86. *)

fun align_chunk :: "memory_chunk \<Rightarrow> Z" where
  "align_chunk Mint8signed = 1"
| "align_chunk Mint8unsigned = 1"
| "align_chunk Mint16signed = 2"
| "align_chunk Mint16unsigned = 2"
| "align_chunk Mint32 = 4"
| "align_chunk Mint64 = 8"
| "align_chunk Mfloat32 = 4"
| "align_chunk Mfloat64 = 4"
| "align_chunk Many32 = 4"
| "align_chunk Many64 = 4"

lemma align_dvd_size[iff]: "align_chunk chunk dvd int (size_chunk_nat chunk)"
  apply (cases chunk)
  by auto

lemma align_dvd_size_mult: "align_chunk chunk dvd i*size_chunk chunk"
  apply (cases chunk)
  by auto

datatype quantity = Q32 | Q64

fun size_quantity_nat :: "quantity \<Rightarrow> nat" where
  "size_quantity_nat Q32 = 4" | "size_quantity_nat Q64 = 8"

lemma [iff]: "size_quantity_nat q = 4 \<longleftrightarrow> q = Q32"
  by (auto elim: size_quantity_nat.elims)
lemma [iff]: "size_quantity_nat q = 8 \<longleftrightarrow> q = Q64"
  by (auto elim: size_quantity_nat.elims)

lemma [iff]: "(0::nat) < size_quantity_nat q"
  apply (cases q)
  by auto

lemma size_quantity_nat_set: "size_quantity_nat q \<in> {4,8}"
  apply (cases q)
  by auto

section \<open>Memory values\<close>

(** A ``memory value'' is a byte-sized quantity that describes the current
  content of a memory cell.  It can be either:
- a concrete 8-bit integer;
- a byte-sized fragment of an opaque value;
- the special constant [Undef] that represents uninitialized memory.
*)

(** Values stored in memory cells. *)

datatype memval =
    Undef
  | Byte m_byte
  | Fragment val quantity nat

subsection \<open>Encoding and decoding integers\<close>

(** We define functions to convert between integers and lists of bytes
  of a given length *)

fun bytes_of_int :: "nat \<Rightarrow> int \<Rightarrow> (m_byte list)" where
  "bytes_of_int 0 _ = []"
| "bytes_of_int (Suc m) x = Byte.repr x # bytes_of_int m (x div 256)"

fun int_of_bytes :: "(m_byte list) \<Rightarrow> int" where
  "int_of_bytes [] = 0"
| "int_of_bytes (b # l') = Byte.unsigned b + int_of_bytes l' * 256"

lemma int_to_bytes_to_int[simp]: "int_of_bytes (bytes_of_int n x) = (x mod (2 ^ (8 * n)))"
proof (induction n x rule: bytes_of_int.induct)
  case (1 uu)
  then show ?case
    by auto
next
  case (2 m x)

  note steps =
    mod_div_mult_eq[of "x mod 2 ^ (8 + 8 * m)" "256", symmetric]
    mod_exp_eq[of x "8 + 8 * m" "8", simplified]
    div_exp_mod_exp_eq[of x 8 "8 * m", simplified]

  show ?case
    apply (simp add: 2)
    apply (subst steps(1))
    apply (subst steps(2))
    apply (subst steps(3))
    by (simp add: take_bit_eq_mod)
qed

lemma length_bytes_of_int[simp]: "length (bytes_of_int sz i) = sz"
  apply (induction sz i rule: bytes_of_int.induct)
  by (auto)

lemma bytes_of_int_truncate: "x = (2 ^ (8*sz)) \<Longrightarrow> bytes_of_int sz (i mod x) = bytes_of_int sz i"
  apply (induction sz i arbitrary: x rule: bytes_of_int.induct)
   apply (auto simp add: Byte.repr_mod)
  subgoal for m x
    using div_exp_mod_exp_eq[of x 8 "8*m"]
    by auto
  done

declare bytes_of_int.simps[simp del] int_of_bytes.simps[simp del]

definition rev_if_be :: "(m_byte list) \<Rightarrow> (m_byte list)" where
  "rev_if_be l = (if Archi.big_endian then List.rev l else l)"

(* only valid for 64bit *)
lemma [simp]: "rev_if_be l = l" using rev_if_be_def Archi.big_endian_def by auto

definition encode_int :: "nat \<Rightarrow> int \<Rightarrow> (m_byte list)" where
  "encode_int sz x = rev_if_be (bytes_of_int sz x)"

lemma encode_int_length[simp]:
  "length (encode_int sz x) = sz"
  unfolding encode_int_def by simp

lemma encode_int_truncate: "x = (2 ^ (8*sz)) \<Longrightarrow> encode_int sz (i mod x) = encode_int sz i"
  unfolding encode_int_def
  using bytes_of_int_truncate by simp

lemma encode_int_truncate':
  assumes "LENGTH('w::len) = 8*sz"
  shows "(encode_int sz (uint (UCAST('x::len \<rightarrow> 'w) i))) = (encode_int sz (uint i))"
  apply (simp add: unsigned_ucast_eq take_bit_eq_mod)
  using assms(1) encode_int_truncate
  by simp

definition decode_int :: "(m_byte list) \<Rightarrow> int" where
  "decode_int b = int_of_bytes (rev_if_be b)"

lemma encode_decode_int[simp]: "decode_int (encode_int sz x) = (x mod (2 ^ (8 * sz)))"
  unfolding encode_int_def decode_int_def
  using int_to_bytes_to_int
  by auto

subsection \<open>Encoding and decoding values\<close>

definition inj_bytes :: "(m_byte list) \<Rightarrow> (memval list)" where
  "inj_bytes bl = List.map Byte bl"

lemma inj_bytes_length[simp]:
  "length (inj_bytes bl) = length bl"
  unfolding inj_bytes_def by simp

lemma inj_bytes_valid[iff]:
  "Undef \<notin> set (inj_bytes bl)"
  unfolding inj_bytes_def
  by auto

fun proj_bytes :: "(memval list) \<Rightarrow> ((m_byte list) option)" where
  "proj_bytes [] = Some []"
| "proj_bytes (Byte b # vl) = (case proj_bytes vl of None \<Rightarrow> None | Some bl \<Rightarrow> Some(b # bl))"
| "proj_bytes _ = None"

lemma proj_inj_bytes[simp]: "proj_bytes (inj_bytes bs) = Some bs"
  unfolding inj_bytes_def
  by (induction bs) auto

lemma proj_bytes_undef[simp]: "proj_bytes (replicate l Undef) = None" if "l > 0"
  using that
  by (cases l) auto

fun inj_value_rec :: "nat \<Rightarrow> val \<Rightarrow> quantity \<Rightarrow> (memval list)" where
  "inj_value_rec 0 v q = []"
| "inj_value_rec (Suc m) v q = Fragment v q m # inj_value_rec m v q"

lemma inj_value_rec_n: "n > 0 \<Longrightarrow> inj_value_rec n v q = Fragment v q (n-1) # inj_value_rec (n-1) v q"
  by (metis Suc_diff_1 inj_value_rec.simps(2))

lemma inj_value_rec_length[simp]: "length (inj_value_rec s v q) = s"
  apply (induction s)
  by auto

lemma inj_value_rec_valid[iff]:
  "Undef \<notin> set (inj_value_rec s v q)"
  apply (induction s)
  by auto

definition inj_value :: "quantity \<Rightarrow> val \<Rightarrow> (memval list)" where
  "inj_value q v = inj_value_rec (size_quantity_nat q) v q"

lemma inj_value_first: "inj_value q v = Fragment v q (size_quantity_nat q - 1) # inj_value_rec (size_quantity_nat q - 1) v q"
  unfolding inj_value_def
  using inj_value_rec_n by simp

lemma inj_value_length[simp]: "length (inj_value q v) = size_quantity_nat q"
  unfolding inj_value_def
  by simp

lemma inj_value_valid[iff]:
  "Undef \<notin> set (inj_value q v)"
  unfolding inj_value_def
  by simp

fun check_value :: "nat \<Rightarrow> val \<Rightarrow> quantity \<Rightarrow> (memval list) \<Rightarrow> bool" where
  "check_value 0 v q [] = True"
| "check_value (Suc m) v q (Fragment v' q' m' # vl') =
    (v = v' \<and> q = q' \<and> m = m' \<and> check_value m v q vl')"
| "check_value _ v q _ = False"

lemma check_inj_value[simp]: "check_value sz v q (inj_value_rec sz v q) = True"
  apply (induction sz v q rule: inj_value_rec.induct)
  by auto

definition proj_value :: "quantity \<Rightarrow> (memval list) \<Rightarrow> val" where
  "proj_value q vl = (case vl of 
    (Fragment v q' n # vl') \<Rightarrow> (if check_value (size_quantity_nat q) v q vl then v else Vundef)
  | _ \<Rightarrow> Vundef)"

lemma proj_inj_value[simp]: "proj_value q (inj_value q v) = v"
  unfolding inj_value_def proj_value_def
  apply (subst (2) inj_value_rec_n)
   apply (cases q)
  by auto

lemma proj_bytes_inj_value[simp]: "proj_bytes (inj_value v q) = None"
  unfolding inj_value_def
  apply (subst inj_value_rec_n)
  by auto

lemma proj_value_undef[simp]: "proj_value x (Undef # l) = Vundef"
  unfolding proj_value_def by simp

lemma proj_value_undef'[simp]: "proj_value q (replicate l Undef) = Vundef"
  unfolding proj_value_def
  by (cases l) auto

fun encode_val :: "memory_chunk \<Rightarrow> val \<Rightarrow> (memval list)" where
  "encode_val chunk v =
  (case (v, chunk) of
    (Vint n, Mint8signed) \<Rightarrow> inj_bytes (encode_int 1 (uint n))
  | (Vint n, Mint8unsigned) \<Rightarrow> inj_bytes (encode_int 1 (uint n))
  | (Vint n, Mint16signed) \<Rightarrow> inj_bytes (encode_int 2 (uint n))
  | (Vint n, Mint16unsigned) \<Rightarrow> inj_bytes (encode_int 2 (uint n))
  | (Vint n, Mint32) \<Rightarrow> inj_bytes (encode_int 4 (uint n))
  | (Vptr b ofs, Mint32) \<Rightarrow> if Archi.ptr64 then replicate 4 Undef else inj_value Q32 v
  | (Vlong n, Mint64) \<Rightarrow> inj_bytes (encode_int 8 (uint n))
  | (Vptr b ofs, Mint64) \<Rightarrow> if Archi.ptr64 then inj_value Q64 v else replicate 8 Undef
  | (Vsingle n, Mfloat32) \<Rightarrow> inj_bytes (encode_int 4 (uint (fp32_of_float n)))
  | (Vfloat n, Mfloat64) \<Rightarrow> inj_bytes (encode_int 8 (uint (fp64_of_float n)))
  | (_, Many32) \<Rightarrow> inj_value Q32 v
  | (_, Many64) \<Rightarrow> inj_value Q64 v
  | (_, _) \<Rightarrow> replicate (size_chunk_nat chunk) Undef
  )"

lemma encode_val_length[simp]:
  "length (encode_val chunk v) = size_chunk_nat chunk"
  apply (cases chunk; cases v)
  by auto

lemma encode_val_length'[simp]: "int (length (encode_val chunk v)) = size_chunk chunk"
  using encode_val_length by auto

fun decode_val :: "memory_chunk \<Rightarrow> (memval list) \<Rightarrow> val" where
  "decode_val chunk vl =
  (case proj_bytes vl of
    Some bl \<Rightarrow>
      (case chunk of
        Mint8signed \<Rightarrow> Vint(scast (Byte.repr (decode_int bl)))
      | Mint8unsigned \<Rightarrow> Vint(ucast (Byte.repr (decode_int bl)))
      | Mint16signed \<Rightarrow> Vint(scast (Short.repr (decode_int bl)))
      | Mint16unsigned \<Rightarrow> Vint(ucast (Short.repr (decode_int bl)))
      | Mint32 \<Rightarrow> Vint(Int.repr(decode_int bl))
      | Mint64 \<Rightarrow> Vlong(Int64.repr(decode_int bl))
      | Mfloat32 \<Rightarrow> Vsingle(Float32_repr (decode_int bl))
      | Mfloat64 \<Rightarrow> Vfloat(Float64_repr (decode_int bl))
      | Many32 \<Rightarrow> Vundef
      | Many64 \<Rightarrow> Vundef
      )
  | None \<Rightarrow>
      (case chunk of
        Mint32 \<Rightarrow> if Archi.ptr64 then Vundef else Val.load_result chunk (proj_value Q32 vl)
      | Many32 \<Rightarrow> Val.load_result chunk (proj_value Q32 vl)
      | Mint64 \<Rightarrow> if Archi.ptr64 then Val.load_result chunk (proj_value Q64 vl) else Vundef
      | Many64 \<Rightarrow> Val.load_result chunk (proj_value Q64 vl)
      | _ \<Rightarrow> Vundef
      )
  )"

lemma load_result[simp]:
  "decode_val chunk (encode_val chunk v) = Val.load_result chunk v"
  apply (cases chunk; cases v)
  by (auto)

section \<open>Compatibility with memory injections\<close>

(** Relating two memory values according to a memory injection. *)

inductive memval_inject :: "meminj \<Rightarrow> memval \<Rightarrow> memval \<Rightarrow> bool" where
    memval_inject_byte:
      "memval_inject f (Byte n) (Byte n)"
  | memval_inject_frag:
      "Val.inject f v1 v2 \<Longrightarrow>
      memval_inject f (Fragment v1 q n) (Fragment v2 q n)"
    | memval_inject_undef:
      "memval_inject f Undef mv"

lemmas encode_simps = encode_val.simps decode_val.simps

declare encode_simps[simp del]

end