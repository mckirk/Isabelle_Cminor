theory Chunkvals
imports "../compcert/Memory"
begin

function length_to_quant :: "'a list \<Rightarrow> quantity option" where
  "length l = 4 \<Longrightarrow> length_to_quant l = Some Q32"
| "length l = 8 \<Longrightarrow> length_to_quant l = Some Q64"
| "length l \<notin> {4,8} \<Longrightarrow> length_to_quant l = None"
  by auto
termination
  apply standard
  by auto

lemma length_to_quant_inj_value[simp]: "length_to_quant (inj_value q v) = Some q"
  apply (cases q)
  by auto

datatype chunkval =
  CVword8 "8 word" | CVword16 "16 word" | CVword32 "32 word" | CVword64 "64 word"
| CVfragments val quantity | CVundef positive

fun size_chunkval_nat :: "chunkval \<Rightarrow> nat" where
  "size_chunkval_nat (CVword8 _) = 1"
| "size_chunkval_nat (CVword16 _) = 2"
| "size_chunkval_nat (CVword32 _) = 4"
| "size_chunkval_nat (CVword64 _) = 8"
| "size_chunkval_nat (CVfragments _ q) = size_quantity_nat q"
| "size_chunkval_nat (CVundef l) = nat_of_num l"

lemma size_chunkval_nat_g0[iff]:
  "0 < size_chunkval_nat cv"
  apply (cases cv)
  by (auto simp add: nat_of_num_pos)

inductive chunk_fits_chunkval where
  "chunk_fits_chunkval Mint8signed (CVword8 _)"
| "chunk_fits_chunkval Mint8unsigned (CVword8 _)"
| "chunk_fits_chunkval Mint16signed (CVword16 _)"
| "chunk_fits_chunkval Mint16unsigned (CVword16 _)"
| "chunk_fits_chunkval Mint32 (CVword32 _)"
| "chunk_fits_chunkval Mfloat32 (CVword32 _)"
| "chunk_fits_chunkval Many32 (CVword32 _)"
| "chunk_fits_chunkval Mint32 (CVfragments _ Q32)"
| "chunk_fits_chunkval Mfloat32 (CVfragments _ Q32)"
| "chunk_fits_chunkval Many32 (CVfragments _ Q32)"
| "chunk_fits_chunkval Mint64 (CVword64 _)"
| "chunk_fits_chunkval Mfloat64 (CVword64 _)"
| "chunk_fits_chunkval Many64 (CVword64 _)"
| "chunk_fits_chunkval Mint64 (CVfragments _ Q64)"
| "chunk_fits_chunkval Mfloat64 (CVfragments _ Q64)"
| "chunk_fits_chunkval Many64 (CVfragments _ Q64)"
| "size_chunk_nat chunk = nat_of_num l \<Longrightarrow> chunk_fits_chunkval chunk (CVundef l)"

lemma chunk_fits_chunkval_size:
  shows "chunk_fits_chunkval chunk cv \<longleftrightarrow> size_chunkval_nat cv = size_chunk_nat chunk"
  apply (cases chunk; cases cv)
  by (auto simp: size_chunk_nat.simps num_of_nat_inverse chunk_fits_chunkval.simps elim: size_quantity_nat.elims)

section \<open>Equivalence with memvals\<close>

fun chunkval_to_memvals :: "chunkval \<Rightarrow> memval list" where
  "chunkval_to_memvals (CVword8 w) = inj_bytes (encode_int 1 (uint w))"
| "chunkval_to_memvals (CVword16 w) = inj_bytes (encode_int 2 (uint w))"
| "chunkval_to_memvals (CVword32 w) = inj_bytes (encode_int 4 (uint w))"
| "chunkval_to_memvals (CVword64 w) = inj_bytes (encode_int 8 (uint w))"
| "chunkval_to_memvals (CVfragments v q) = inj_value q v"
| "chunkval_to_memvals (CVundef sz) = replicate (nat_of_num sz) Undef"

lemma length_chunkval_to_memvals[simp]:
  "length (chunkval_to_memvals cv) = size_chunkval_nat cv"
  apply (cases cv)
  by auto

section \<open>Encoding/Decoding\<close>

fun encode_chunkval :: "memory_chunk \<Rightarrow> val \<Rightarrow> chunkval" where
  "encode_chunkval Mint8signed (Vint n) = (CVword8 (ucast n))"
| "encode_chunkval Mint8unsigned (Vint n) = (CVword8 (ucast n))"
| "encode_chunkval Mint16signed (Vint n) = (CVword16 (ucast n))"
| "encode_chunkval Mint16unsigned (Vint n) = (CVword16 (ucast n))"
| "encode_chunkval Mint32 (Vint n) = (CVword32 n)"
| "encode_chunkval Mint64 (Vlong n) = (CVword64 n)"
| "encode_chunkval Mint64 (Vptr b ofs) = (CVfragments (Vptr b ofs) Q64)"
| "encode_chunkval Mfloat32 (Vsingle f) = (CVword32 (fp32_of_float f))"
| "encode_chunkval Mfloat64 (Vfloat f) = (CVword64 (fp64_of_float f))"
| "encode_chunkval Many32 v = (CVfragments v Q32)" (* done like this in encode_val *)
| "encode_chunkval Many64 v = (CVfragments v Q64)"
| "encode_chunkval chunk _ = CVundef (num_of_nat (size_chunk_nat chunk))"

lemma size_encode_chunkval[simp]:
  "size_chunkval_nat (encode_chunkval chunk v) = size_chunk_nat chunk"
  apply (rule encode_chunkval.cases[of "(chunk, v)"])
  apply (auto simp add: size_chunk_nat.simps)
  using nat_of_num_inverse nat_of_num_numeral by auto

lemma chunk_fits_chunkval_encode[iff]:
  shows "chunk_fits_chunkval chunk (encode_chunkval chunk v)"
  apply (cases chunk; cases v)
  by (auto intro!: chunk_fits_chunkval.intros simp: num_of_nat_inverse)

fun decode_chunkval :: "memory_chunk \<Rightarrow> chunkval \<Rightarrow> val" where
  "decode_chunkval Mint8signed cv     = (case cv of (CVword8 w) \<Rightarrow> Vint (scast w) | _ \<Rightarrow> Vundef)"
| "decode_chunkval Mint8unsigned cv   = (case cv of (CVword8 w) \<Rightarrow> Vint (ucast w) | _ \<Rightarrow> Vundef)"
| "decode_chunkval Mint16signed cv    = (case cv of (CVword16 w) \<Rightarrow> Vint (scast w) | _ \<Rightarrow> Vundef)"
| "decode_chunkval Mint16unsigned cv  = (case cv of (CVword16 w) \<Rightarrow> Vint (ucast w) | _ \<Rightarrow> Vundef)"
| "decode_chunkval Mint32 cv          = (case cv of (CVword32 w) \<Rightarrow> Vint w | _ \<Rightarrow> Vundef)"
| "decode_chunkval Mint64 cv          = (case cv of
    (CVword64 w) \<Rightarrow> Vlong w
  | (CVfragments (Vlong w) Q64) \<Rightarrow> (Vlong w)
  | (CVfragments (Vptr b ofs) Q64) \<Rightarrow> (Vptr b ofs)
  | _ \<Rightarrow> Vundef)"
| "decode_chunkval Mfloat32 cv        = (case cv of (CVword32 w) \<Rightarrow> (Vsingle (float_of_fp32 w))| _ \<Rightarrow> Vundef)"
| "decode_chunkval Mfloat64 cv        = (case cv of (CVword64 w) \<Rightarrow> (Vfloat (float_of_fp64 w))| _ \<Rightarrow> Vundef)"
| "decode_chunkval Many32 cv = (case cv of
    (CVfragments (Vint n) Q32) \<Rightarrow> (Vint n)
  | (CVfragments (Vsingle f) Q32) \<Rightarrow> (Vsingle f)
  | _ \<Rightarrow> Vundef)"
| "decode_chunkval Many64 cv = (case cv of
    (CVfragments v Q64) \<Rightarrow> v
  | _ \<Rightarrow> Vundef)"

lemma encode_chunkval_val[simp]: "chunkval_to_memvals (encode_chunkval chunk v) = encode_val chunk v"
  apply (cases chunk; cases v)
  apply (auto simp: mem_simps uint_word_of_int encode_int_truncate' encode_val.simps)
  using nat_of_num_inverse nat_of_num_numeral by auto

lemma decode_chunkval_val[simp]: "decode_val chunk (chunkval_to_memvals cv) = decode_chunkval chunk cv"
  if "chunk_fits_chunkval chunk cv" (* decode_val doesn't enforce this, but Mem.load does *)
  using that
  apply (auto elim!: chunk_fits_chunkval.cases)
  by (auto simp: mem_simps decode_val.simps split: val.split option.splits memory_chunk.splits)

(* if we encode a value as memvals and as a chunkval, the decoding will agree *)
lemma encode_decode_chunkval[simp]:
  shows "decode_chunkval chunk (encode_chunkval chunk v) = Val.load_result chunk v"
  apply (cases chunk; cases v)
  by (auto)

declare encode_chunkval.simps[simp del] decode_chunkval.simps[simp del]

section \<open>Memory accesses with Chunkvals\<close>

lemma load_chunkval:
  assumes [iff]: "chunk_fits_chunkval chunk cv"
  assumes [iff]: "Mem.valid_access m chunk b ofs Readable"
  assumes [simp]: "Mem.getN (size_chunk_nat chunk) ofs (mem_contents m b) = chunkval_to_memvals cv"
  shows "Mem.load chunk m b ofs = Some (decode_chunkval chunk cv)"
  by (auto simp: Mem.load.simps)

end