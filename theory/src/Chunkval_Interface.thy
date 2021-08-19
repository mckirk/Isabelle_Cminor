theory Chunkval_Interface
imports Sep_Logic Chunkvals
begin

(*
  to satisfy Mem.valid_access, we demand alignment of chunkvals to their respective sizes
  note that this is actually more restrictive than align_chunk in the Mfloat64 and Many64 cases!
*)
fun align_chunkval_nat :: "chunkval \<Rightarrow> nat" where
  "align_chunkval_nat (CVword8 _) = 1"
| "align_chunkval_nat (CVword16 _) = 2"
| "align_chunkval_nat (CVword32 _) = 4"
| "align_chunkval_nat (CVword64 _) = 8"
| "align_chunkval_nat (CVfragments _ q) = size_quantity_nat q"
| "align_chunkval_nat (CVundef l) = nat_of_num l"

lemma align_chunkval_encode[simp]:
  "align_chunkval_nat (encode_chunkval chunk v) = size_chunk_nat chunk"
  apply (cases chunk; cases v)
  by (auto simp add: encode_chunkval.simps num_of_nat_inverse size_chunk_nat.simps)

lemma chunk_fits_encoding_aligned:
  fixes ofs :: int
  assumes fits: "chunk_fits_chunkval chunk cv"
  assumes "align_chunkval_nat cv dvd ofs"
  shows "align_chunkval_nat (encode_chunkval chunk v) dvd ofs"
  apply (rule chunk_fits_chunkval.cases[OF fits])
  using assms
  by (auto simp: size_chunkval_nat.simps align_chunk.simps align_chunkval_nat.simps size_chunk_nat.simps)

lemma chunk_fits_aligns_agree:
  fixes ofs :: int
  assumes "chunk_fits_chunkval chunk cv"
  assumes "align_chunkval_nat cv dvd ofs"
  shows "align_chunk chunk dvd ofs"
  apply (rule chunk_fits_chunkval.cases[OF assms(1)])
  using assms(2)
  apply (auto simp: align_chunk.simps)
  apply (cases chunk)
  by (auto simp: align_chunk.simps size_chunk_nat.simps)

section \<open>Chunkval Assertion\<close>

definition "chunkval_at \<equiv> \<lambda>(b, ofs) cv.
  mem.val_range (b, ofs) (chunkval_to_memvals cv) ** \<up>(int (align_chunkval_nat cv) dvd ofs)"

lemma dvd_trumphs: "(4 dvd ofs \<and> 8 dvd ofs) \<longleftrightarrow> 8 dvd ofs" for ofs :: int
  by (meson cong_exp_iff_simps(2) dvd_trans even_numeral mod_eq_0_iff_dvd)

lemma chunkval_as_memchunk:
  assumes "chunk_fits_chunkval chunk cv"
  shows "chunkval_at (b, ofs) cv
        = (mem.mem_chunk chunk (b, ofs) (chunkval_to_memvals cv) ** \<up>(int (align_chunkval_nat cv) dvd ofs))"
  unfolding chunkval_at_def mem.mem_chunk_def
  apply (cases "int (align_chunkval_nat cv) dvd ofs")
   apply (drule chunk_fits_aligns_agree[OF assms(1)])
  using chunk_fits_chunkval_size assms
  by (auto simp add: sep_algebra_simps)

fun size_chunkvals where
  "size_chunkvals [] = 0"
| "size_chunkvals (cv # cvs) = size_chunkval_nat cv + size_chunkvals cvs"

lemma size_chunkvals_append:
  "size_chunkvals (cvs @ [cv]) = size_chunkval_nat cv + size_chunkvals cvs"
  apply (induction cvs)
  by auto

lemma size_chunkvals_replicate[simp]:
  "size_chunkvals (replicate l cv) = size_chunkval_nat cv * l"
  apply (induct l)
  by auto

lemma size_chunkvals_some[iff]:
  assumes "cvs \<noteq> []"
  shows "0 < size_chunkvals cvs"
  apply (cases cvs)
  using assms
  by auto

lemma size_chunkvals_some_word[iff]:
  assumes "cvs \<noteq> []"
  assumes "int (size_chunkvals cvs) < arch_max_size"
  shows "0 < (word_of_nat (size_chunkvals cvs) :: ptrsize word)"
  apply (rule ccontr)
  apply (simp add: word_of_nat_less_iff[of 0, simplified])
  using assms unfolding arch_max_size_def
  using size_chunkvals_some
  by (metis Word_64.word_bits_conv Word_64.word_bits_len_of bot_nat_0.extremum_strict of_nat_less_imp_less real_of_nat_eq_numeral_power_cancel_iff take_bit_nat_eq_self_iff)

definition "chunkvals_to_memvals cvs \<equiv> concat (map chunkval_to_memvals cvs)"
lemma chunkvals_to_memvals0[simp]:
  "chunkvals_to_memvals [] = []"
  unfolding chunkvals_to_memvals_def by simp

lemma length_chunkvals_to_memvals[simp]:
  "length (chunkvals_to_memvals cvs) = size_chunkvals cvs"
  unfolding chunkvals_to_memvals_def
  apply (induction cvs)
  by (auto)

section \<open>Chunkval Range\<close>

fun cv_range where
  "cv_range (b, ofs) [] = \<box>"
| "cv_range (b, ofs) (cv # cvs) = (chunkval_at (b, ofs) cv ** cv_range (b, ofs+size_chunkval_nat cv) cvs)"

lemma cv_range_append:
  "cv_range (b, ofs) (cvs @ [cv]) = (cv_range (b, ofs) cvs ** chunkval_at (b, ofs+size_chunkvals cvs) cv)"
  apply (induction cvs arbitrary: ofs)
  by (auto simp add: add.assoc)

lemma cv_range_undef:
  fixes ofs :: int
  fixes sz :: nat
  assumes "0 < sz"
  assumes "sz dvd ofs"
  shows "cv_range (b, ofs) (replicate n (CVundef (num_of_nat sz)))
  =  mem.val_range (b, ofs) (replicate (n*sz) Undef)"
  using assms
  apply (induction n arbitrary: ofs)
  apply (simp)
  apply (subst replicate_Suc)+
  apply (simp add: replicate_add mem.val_range_split_concat num_of_nat_inverse)
  apply (rule sep_conj_trivial_strip2)
  unfolding chunkval_at_def
  by (simp add: sep_algebra_simps num_of_nat_inverse)

fun cvs_aligned where
  "cvs_aligned (b, ofs) [] = True"
| "cvs_aligned (b, ofs) (cv # cvs)
  = (int (align_chunkval_nat cv) dvd ofs \<and> cvs_aligned (b, ofs + size_chunkval_nat cv) cvs)"

lemma cv_range_alt:
  "cv_range p cvs = (\<up>(cvs_aligned p cvs) ** mem.val_range p (chunkvals_to_memvals cvs))"
  apply (cases p)
  subgoal for b ofs
    apply (induction cvs arbitrary: p ofs)
     apply (simp add: sep_algebra_simps)
    by (simp add: chunkvals_to_memvals_def chunkval_at_def mem.val_range_split_concat sep_algebra_simps)
  done

thm mem.val_range_split[no_vars]

lemma cv_range_split:
  assumes "len \<le> length cvs"
  shows "cv_range (b, ofs) cvs = 
          (cv_range (b, ofs) (take len cvs)
        \<and>* cv_range (b, ofs + (size_chunkvals (take len cvs))) (drop len cvs))"
  using assms
proof (induction len)
  case 0
  then show ?case
    by (simp add: sep_algebra_simps)
next
  case (Suc len)

  then have "len \<le> length cvs" by simp

  note IH = Suc(1)[OF this]

  let ?cvs1 = "take len cvs"
  let ?cvs2 = "drop len cvs"
  let ?cv = "cvs ! len"

  have cvs1': "take (Suc len) cvs = ?cvs1 @ [?cv]"
    by (meson Suc.prems less_eq_Suc_le take_Suc_conv_app_nth)

  obtain cvs2' where cvs2': "?cvs2 = ?cv # cvs2'" "drop (Suc len) cvs = cvs2'"
    by (metis Cons_nth_drop_Suc Suc.prems Suc_le_lessD)

  show ?case
    apply (simp add: IH cvs1' cvs2' cv_range_append size_chunkvals_append)
    by (smt (verit, best))
qed

lemma cv_range_extract:
  assumes "idx < length cvs"
  shows "cv_range (b, 0) cvs
    =  (cv_range (b, 0) (take idx cvs)
    \<and>* chunkval_at (b, int (size_chunkvals (take idx cvs))) (cvs ! idx)
    \<and>* cv_range (b, int (size_chunkvals (take idx cvs) + size_chunkval_nat (cvs ! idx))) (drop (Suc idx) cvs))"
  apply (simp add: sep_algebra_simps)
proof (goal_cases)
  case 1

  have "idx \<le> length cvs"
    using assms by simp

  note split1 = cv_range_split[OF this, of b 0, simplified]

  obtain cv cvs' where cvs': "drop idx cvs = cv # cvs'" "cvs ! idx = cv" "drop (Suc idx) cvs = cvs'"
    by (metis Cons_nth_drop_Suc assms)

  let ?ofs_idx = "int (size_chunkvals (take idx cvs))"
  let ?ofs_cvs' = "int (size_chunkvals (take idx cvs)) + size_chunkval_nat cv"

  have split2: "cv_range (b, ?ofs_idx) (drop idx cvs)
      = (chunkval_at (b, ?ofs_idx) cv ** cv_range (b, ?ofs_cvs') cvs')"
    by (simp add: cvs')

  then show ?case
    by (simp add: split1 split2 cvs')
qed

definition "cvs_of_size cvs elem_size \<equiv> \<forall>cv \<in> set cvs. (size_chunkval_nat cv) = elem_size"

lemma cvs_of_size0[iff]: "cvs_of_size [] sz"
  unfolding cvs_of_size_def by auto
lemma cvs_of_size_undef[iff]:
  "cvs_of_size (replicate n (CVundef elem_size)) (nat_of_num elem_size)"
  unfolding cvs_of_size_def by auto

lemma size_chunkvals_of_size:
  assumes "cvs_of_size cvs elem_size"
  shows "size_chunkvals cvs = elem_size * length cvs"
  using assms
  apply (induction cvs)
   apply simp
  unfolding cvs_of_size_def
  by auto

lemma cvs_of_size_take[iff]:
  assumes "cvs_of_size cvs elem_size"
  shows "cvs_of_size (take l cvs) elem_size"
  using assms unfolding cvs_of_size_def
  by (meson in_set_takeD)

lemma size_chunkvals_of_size_take:
  assumes "l < length cvs"
  assumes "cvs_of_size cvs elem_size"
  shows "size_chunkvals (take l cvs) = elem_size * l"
  using cvs_of_size_take[OF assms(2), THEN size_chunkvals_of_size]
  using assms(1) by auto

lemma cv_range_extract_samesize:
  assumes "idx < length cvs"
  assumes "cvs_of_size cvs elem_size"
  shows "cv_range (b, 0) cvs
    =  (cv_range (b, 0) (take idx cvs)
    \<and>* chunkval_at (b, int (elem_size * idx)) (cvs ! idx)
    \<and>* cv_range (b, int (elem_size * (Suc idx))) (drop (Suc idx) cvs))"
  apply (simp add: cv_range_extract[OF assms(1)])
  apply (simp add: cv_range_extract size_chunkvals_of_size_take[OF assms])
  using assms(2) cvs_of_size_def
  by (smt (verit, ccfv_threshold) assms(1) nth_mem)

section \<open>Chunkval Array\<close>

record cv_array_def =
  array_name :: ident
  array_elem_size :: nat
  array_length :: nat

record cv_array = cv_array_def +
  array_block :: positive
  array_chunkvals :: "chunkval list"

definition "array_size array \<equiv> array_elem_size array * array_length array"

definition array_idx_offset :: "'a cv_array_def_scheme \<Rightarrow> nat \<Rightarrow> int" where
  "array_idx_offset array idx \<equiv> (array_elem_size array) * idx"

lemma [iff]: "0 \<le> array_idx_offset array idx"
  unfolding array_idx_offset_def
  by simp

definition "chunk_fits_array chunk array \<equiv> size_chunk_nat chunk = (array_elem_size array)"

fun array_from_def :: "cv_array_def \<Rightarrow> positive \<Rightarrow> chunkval list \<Rightarrow> cv_array" where
  "array_from_def def b cvs = cv_array_def.extend def (cv_array.fields b cvs)"

definition "SAME_DEF def array \<equiv> cv_array_def.truncate array = def"

inductive array_def_valid :: "cv_array_def \<Rightarrow> bool" where
  "\<lbrakk> 0 < array_elem_size def;
     0 < array_length def;
     array_size def < arch_max_size \<rbrakk> \<Longrightarrow> array_def_valid def"

inductive_cases array_def_validE: "array_def_valid array"

inductive array_valid :: "cv_array \<Rightarrow> bool" where
  "\<lbrakk> array_chunkvals array \<noteq> [];
     length (array_chunkvals array) = array_length array;
     cvs_of_size (array_chunkvals array) (array_elem_size array);
     array_size array < arch_max_size \<rbrakk> \<Longrightarrow> array_valid array"

inductive_cases array_validE: "array_valid array"

context
  fixes array
  assumes valid: "array_valid array"
begin

lemma properties[iff]:
  "length (array_chunkvals array) = array_length array"
  "cvs_of_size (array_chunkvals array) (array_elem_size array)"
  "array_size array < arch_max_size"
  using array_validE[OF valid] by auto

lemma array_chunkvals_size[simp]:
  shows "size_chunkvals (array_chunkvals array) = array_size array"
  apply (rule array_validE[OF valid])
  unfolding array_size_def cvs_of_size_def
proof (induction "array_chunkvals array" arbitrary: array)
  case Nil
  then show ?case by simp
next
  case (Cons a x)
  note [simp] = \<open>a # x = array_chunkvals array\<close>[symmetric]
  show ?case
    using Cons(1,3)
    apply simp
    by (metis Cons.hyps(2) Cons.prems cvs_of_size_def size_chunkvals.simps(2) size_chunkvals_of_size)
qed

lemma array_valid_size_g0[iff]:
  shows "0 < array_size array"
  unfolding array_size_def
  by (metis array_chunkvals_size array_size_def array_validE size_chunkvals_some valid)

lemma array_valid_size_bounded[simp]:
  shows "take_bit 64 (array_size array) = array_size array"
  unfolding arch_max_size_def
  by (metis arch_max_size_def fact_2 int_ops(3) len64 of_nat_fact of_nat_less_numeral_power_cancel_iff properties(3) take_bit_nat_eq_self)

lemma array_idx_offset_bounded:
  assumes idx: "idx < array_length array"
  shows "array_idx_offset array idx < array_size array"
  apply (rule array_validE[OF valid])
  unfolding array_idx_offset_def array_size_def
  using idx
  by (metis less_imp_of_nat_less nat_0_less_mult_iff nat_mult_less_cancel_disj size_chunkvals_of_size size_chunkvals_some)

lemma array_idx_offset_bounded'[simp]:
  assumes idx: "idx < array_length array"
  shows "take_bit 64 (array_idx_offset array idx) = array_idx_offset array idx"
  using assms array_idx_offset_bounded
  unfolding array_valid.simps arch_max_size_def array_idx_offset_def
  by (smt (verit, ccfv_threshold) array_valid_size_bounded of_nat_power_less_of_nat_cancel_iff take_bit_nat_eq_self_iff take_bit_of_nat valid)

lemma chunk_fits_chunkval_if_array:
  assumes idx: "idx < array_length array"
  assumes fits: "chunk_fits_array chunk array"
  shows "chunk_fits_chunkval chunk (array_chunkvals array ! idx)"
  apply (rule array_validE[OF valid])
  by (simp add: chunk_fits_chunkval_size fits[unfolded chunk_fits_array_def, symmetric] cvs_of_size_def idx)
end

lemma chunk_fits_cvs_of_size_update:
  assumes "chunk_fits_array chunk array"
  assumes "cvs_of_size (array_chunkvals array) (array_elem_size array)"
  shows "cvs_of_size ((array_chunkvals array)[idx := encode_chunkval chunk v]) (array_elem_size array)"
  using assms
  unfolding cvs_of_size_def chunk_fits_array_def
  apply (cases array)
  by (metis insertE set_update_subset_insert size_encode_chunkval subsetD)

lemma array_same_def[simp]:
  assumes "SAME_DEF def array"
  shows
    "array_name def = array_name array"
    "array_elem_size def = array_elem_size array"
    "array_length def = array_length array"
    "array_idx_offset def idx = array_idx_offset array idx"
    "chunk_fits_array chunk def = chunk_fits_array chunk array"
  using assms
  unfolding SAME_DEF_def array_idx_offset_def chunk_fits_array_def
  by (auto simp: cv_array_def.defs)

definition "have_array_head def array \<equiv> (\<up>(SAME_DEF def array \<and> array_valid array)
  \<and>* env.assn_is (array_name array) (Vptr (array_block array) 0) 
  \<and>* chunkval_at (array_block array, -8) (CVword64 (Int64.repr (array_size array))))"

definition "have_array def array \<equiv>
  have_array_head def array \<and>* cv_range (array_block array, 0) (array_chunkvals array)"

schematic_goal cv_array_alt:
  "have_array def array
    =  (\<up>(?x)
    \<and>* env.assn_is (array_name array) (Vptr (array_block array) 0)
    \<and>* mem.mem_val_fit Mptr (array_block array, - size_chunk Mptr) (Vptrofs (Int64.repr (array_size array)))
    \<and>* mem.val_range (array_block array, 0) (chunkvals_to_memvals (array_chunkvals array)))"
  unfolding have_array_def have_array_head_def chunkval_at_def Mptr_def Vptrofs_def cv_range_alt mem.mem_chunk_def
  by (simp add: sep_algebra_simps encode_val.simps mem.chunk_fit.simps size_chunk_nat.simps
      align_chunk.simps size_chunk.simps)

definition array_get_val :: "cv_array \<Rightarrow> nat \<Rightarrow> memory_chunk \<Rightarrow> val" where
  "array_get_val array idx chunk \<equiv> decode_chunkval chunk (array_chunkvals array ! idx)"

definition array_set_val :: "cv_array \<Rightarrow> nat \<Rightarrow> memory_chunk \<Rightarrow> val \<Rightarrow> cv_array" where
  "array_set_val array idx chunk v \<equiv>
    array_chunkvals_update (\<lambda>cvs. list_update cvs idx (encode_chunkval chunk v)) array"

lemma array_same_def_set_val[iff]:
  assumes "SAME_DEF array_def array"
  shows "SAME_DEF array_def (array_set_val array idx chunk v)"
  using assms unfolding SAME_DEF_def array_set_val_def
  by (auto simp: cv_array_def.defs)

section \<open>Chunkval Operations\<close>

named_theorems cv_op_wrappers

definition [cv_op_wrappers]: "mem_op_valid_access_cv = mem.op_valid_access"

definition [cv_op_wrappers]: "mem_op_decode_chunk_cv = mem.op_decode_chunk"
definition [cv_op_wrappers]: "mem_op_load_cv = mem.op_load"
definition [cv_op_wrappers]: "mem_op_loadv_cv = mem.op_loadv"

definition [cv_op_wrappers]: "mem_op_store_cv = mem.op_store"
definition [cv_op_wrappers]: "mem_op_storev_cv = mem.op_storev"

definition [cv_op_wrappers]: "Eload_cv \<equiv> Eload"

definition [cv_op_wrappers]: "Sstore_cv \<equiv> Sstore"

lemmas mem_wp_load_cv[vcg_decomp_rules] = mem.wp_load[folded cv_op_wrappers]
lemmas mem_wp_loadv_cv[vcg_decomp_rules] = mem.wp_loadv[folded cv_op_wrappers]

lemmas mem_wp_storev_cv[vcg_decomp_rules] = mem.wp_storev[folded cv_op_wrappers]

lemmas wp_Eload_cv[vcg_decomp_rules] = wp_Eload[folded cv_op_wrappers]

lemmas wp_Sstore_cv[vcg_decomp_rules] = wp_Sstore[folded cv_op_wrappers]

print_statement mem.ht_valid_access_inv[folded cv_op_wrappers]

lemma mem_ht_valid_access_cv[vcg_rules]:
  assumes fits: "chunk_fits_chunkval chunk cv"
  shows
    "mem.htriple
    (chunkval_at p cv)
    (mem_op_valid_access_cv chunk p perm)
    (\<lambda>r. \<up>r \<and>* chunkval_at p cv)"
  apply (rule ptrI[of p])
  unfolding chunkval_as_memchunk[OF fits] mem_op_valid_access_cv_def
  by vcg

print_statement mem.ht_decode_chunk_inv[folded cv_op_wrappers]

lemma mem_ht_decode_chunk_cv[vcg_rules]:
  assumes fits: "chunk_fits_chunkval chunk cv"
  shows
    "mem.htriple
    (chunkval_at p cv)
    (mem_op_decode_chunk_cv chunk p)
    (\<lambda>r. \<up>(decode_val chunk r = decode_chunkval chunk cv) \<and>* chunkval_at p cv)"
  apply (rule ptrI)
  unfolding chunkval_as_memchunk[OF fits] mem_op_decode_chunk_cv_def
  unfolding mem.op_decode_chunk_def mem.mem_chunk_def
  using decode_chunkval_val[OF fits]
  by vcg

print_statement mem.ht_store_inv[folded cv_op_wrappers]

lemma mem_ht_store_cv_weak:
  assumes fits: "chunk_fits_chunkval chunk cv"
  shows
    "mem.htriple_weak
    (chunkval_at p cv)
    (mem_op_store_cv chunk p v)
    (\<lambda>_. chunkval_at p (encode_chunkval chunk v))"
  apply (rule ptrI)
  unfolding chunkval_as_memchunk[OF fits] mem_op_store_cv_def
  apply vcg
  unfolding chunkval_at_def mem.mem_chunk_def
  using chunk_fits_encoding_aligned[OF fits] chunk_fits_aligns_agree[OF fits] encode_chunkval_val
  by vcg

lemma mem_ht_store_cv[vcg_rules]:
  assumes fits: "chunk_fits_chunkval chunk cv"
  shows
    "mem.htriple
    (chunkval_at p cv)
    (mem_op_store_cv chunk p v)
    (\<lambda>_. chunkval_at p (encode_chunkval chunk v))"
  apply (rule ptrI)
  apply (rule state_op.htriple_strengthen_inv[OF mem_ht_store_cv_weak[OF fits]])
   apply simp
  unfolding mem_op_store_cv_def mem.op_store_def
  apply (simp split: prod.splits option.splits add: concrete_mem_lens.update_maybe_def concrete_mem_lens.laws)
  by (metis Mem'.store_inv concrete_mem_lens.get_put mem.invariants_def)

section \<open>Array Operation\<close>

definition Sarray_alloc :: "cv_array_def \<Rightarrow> stmt" where
  "Sarray_alloc def \<equiv>
    (Sbuiltin (Some (array_name def)) EF_malloc 
      [Econst (Olongconst (Int64.repr (array_size def)))])"

lemma ht_malloc_cv_array[vcg_rules]:
  notes ht_malloc[vcg_rules]
  fixes def :: cv_array_def
  assumes def_valid: "array_def_valid def"
  defines "new_array b \<equiv>
    array_from_def def b (replicate (array_length def) (CVundef (num_of_nat (array_elem_size def))))"
  shows "stmt_ht ge f sp
      (env.assn_is (array_name def) v)
      (Sarray_alloc def)
      (silent_op (EXS b. have_array def (new_array b)))"
proof -
  have array_def_assms[iff]:
    "0 < array_elem_size def"
    "0 < array_length def"
    "int (array_size def) < arch_max_size"
    using def_valid[unfolded array_def_valid.simps, simplified]
    by auto

  have [simp]: "\<And>b sz. chunkval_at (b, -8) (CVword64 sz)
     = mem.mem_val Mptr (b, - size_chunk Mptr) (Vptrofs sz)"
    unfolding chunkval_at_def mem.mem_chunk_def
    unfolding Mptr_def Vptrofs_def
    by (simp add: size_chunk.simps size_chunk_nat.simps align_chunk.simps encode_val.simps mem.chunk_fit.simps sep_algebra_simps)

  have [simp]:
    "\<And>b. array_name (new_array b) = array_name def"
    "\<And>b. array_size (new_array b) = array_size def"
    "\<And>b. array_block (new_array b) = b"
    unfolding new_array_def
    by (auto simp: cv_array_def.defs cv_array.defs array_size_def)

  have [iff]: "\<And>x. mem.chunk_fit Mptr (Vptrofs x)"
    unfolding Mptr_def Vptrofs_def
    by (simp add: mem.chunk_fit.intros(5))

  have [simp]: "take_bit 64 (array_size def) = array_size def"
    using \<open>int (array_size def) < arch_max_size\<close>
    unfolding arch_max_size_def
    by (simp add: take_bit_nat_eq_self_iff)

  have [simp]: "\<And>b. cv_range (b, 0) (array_chunkvals (new_array b))
      = mem.val_range (b, 0) (replicate (nat (Int64.unsigned (Int64.repr (int (array_size def))))) Undef)"
    unfolding new_array_def array_size_def
    using cv_range_undef
    by (simp add: cv_array.defs cv_array_def.defs array_size_def[symmetric] mult.commute)

  have [iff]: "\<And>b. array_valid (new_array b)"
    unfolding array_valid.simps new_array_def
    unfolding array_size_def
    apply (simp add: cv_array.defs cv_array_def.defs)
    by (metis array_def_assms(1) array_def_assms(3) array_size_def cvs_of_size_undef num_of_nat_inverse of_nat_mult)

  have [iff]: "\<And>b. SAME_DEF def (new_array b)"
    unfolding SAME_DEF_def new_array_def
    by (simp add: cv_array_def.defs)

  then show ?thesis
    unfolding Sarray_alloc_def have_array_def have_array_head_def
    supply [simp] = sep_algebra_simps
    by vcg
qed

definition "Sarray_free def \<equiv> Sbuiltin None (EF_free) [Evar (array_name def)]"

lemma ht_free_cv_array[vcg_rules]:
  shows "stmt_ht ge f sp
      (have_array def array)
      (Sarray_free def)
      (silent_op (EXS v. env.assn_is (array_name def) v))"
  unfolding Sarray_free_def cv_array_alt
  apply vcg
    apply (metis array_chunkvals_size array_valid.simps size_chunkvals_some_word)
   apply simp
  apply (simp add: sep_algebra_simps)
  by vcg

definition Earray_idx_offset where
  "Earray_idx_offset array_def idx \<equiv> (Ebinop Oaddl
          (Evar (array_name array_def))
          (Econst (Olongconst (word_of_int (array_idx_offset array_def idx)))))"

lemma ht_array_idx_offset[vcg_rules]:
  assumes [iff]: "idx < array_length array"
  shows
      "expr_ht ge sp
      (have_array array_def array)
      (Earray_idx_offset array_def idx)
      (\<lambda>r. r = Vptr (array_block array) (word_of_int (array_idx_offset array idx)))"
  unfolding have_array_def have_array_head_def
  unfolding Earray_idx_offset_def
  by vcg

definition Earray_load where
  "Earray_load array_def idx chunk \<equiv> Eload_cv chunk (Earray_idx_offset array_def idx)"

lemma ht_array_load[vcg_rules]:
  assumes fits_array: "chunk_fits_array chunk array"
  assumes idx_ok: "idx < array_length array"
  shows
      "expr_ht ge sp
      (have_array array_def array)
      (Earray_load array_def idx chunk)
      (\<lambda>r. r = array_get_val array idx chunk)"
  unfolding have_array_def have_array_head_def
  apply (rule expr.htriple_pure_preI)
  apply (simp add: pure_part_pure_conj_eq sep_algebra_simps)
  apply clarify
proof (goal_cases)
  case 1

  note valid = \<open>array_valid array\<close>

  note array_assms = valid[simplified array_valid.simps, simplified]

  then have idx_inrange: "idx < length (array_chunkvals array)"
    using idx_ok by auto

  note extr = cv_range_extract[OF this]

  note array_offset_ok = array_idx_offset_bounded'[OF valid idx_ok]

  have [simp]: "int (size_chunkvals (take idx (array_chunkvals array))) = array_idx_offset array idx"
    by (metis array_assms array_idx_offset_def idx_ok size_chunkvals_of_size_take)

  have [iff]: "chunk_fits_chunkval chunk (array_chunkvals array ! idx)"
    by (simp add: 1 chunk_fits_chunkval_if_array fits_array idx_ok)

  have [simp]: "decode_chunkval chunk (array_chunkvals array ! idx) = array_get_val array idx chunk"
    by (simp add: array_get_val_def)

  show ?case
    apply (simp add: extr)
    unfolding Earray_load_def Earray_idx_offset_def
    using \<open>SAME_DEF array_def array\<close>
    apply vcg
    apply (simp add: array_offset_ok)
    by vcg
qed

definition Sarray_store :: "cv_array_def \<Rightarrow> nat \<Rightarrow> memory_chunk \<Rightarrow> expr \<Rightarrow> stmt" where
  "Sarray_store array_def idx chunk a \<equiv> Sstore_cv chunk (Earray_idx_offset array_def idx) a"

lemma ht_array_store[vcg_rules]:
  assumes fits_array: "chunk_fits_array chunk array"
  assumes idx_ok: "idx < array_length array"
  assumes [vcg_rules]: "expr_ht ge sp F a (\<lambda>r. r = v)"
  shows "stmt_htF ge f sp
      F (have_array array_def array)
      (Sarray_store array_def idx chunk a)
      (silent_op (have_array array_def (array_set_val array idx chunk v)))"
  unfolding have_array_def have_array_head_def
  apply (rule stmt.htripleF_pure_preI)
  apply (simp add: pure_part_pure_conj_eq sep_algebra_simps)
  apply clarify
proof (goal_cases)
  case 1

  note valid = \<open>array_valid array\<close>

  note array_assms = valid[simplified array_valid.simps, simplified]

  let ?cvs = "array_chunkvals array"
  let ?cv' = "encode_chunkval chunk v"
  let ?cvs' = "?cvs[idx := ?cv']"

  have idx_inrange: "idx < length ?cvs"
    using idx_ok array_assms
    by simp

  have idx_inrange': "idx < length ?cvs'"
    using idx_ok array_assms
    by simp

  have [simp]: "?cvs' ! idx = ?cv'"
    using idx_inrange' by auto

  note extr = cv_range_extract[OF idx_inrange]
  note extr_new = cv_range_extract[OF idx_inrange', simplified]

  note array_offset_ok = array_idx_offset_bounded'[OF valid idx_ok]

  have [simp]: "int (size_chunkvals (take idx (array_chunkvals array))) = array_idx_offset array idx"
    by (metis array_assms array_idx_offset_def idx_ok size_chunkvals_of_size_take)

  have [iff]: "chunk_fits_chunkval chunk (array_chunkvals array ! idx)"
    by (simp add: valid chunk_fits_chunkval_if_array fits_array idx_ok)

  have [iff]: "array_valid (array_set_val array idx chunk v)"
    unfolding array_valid.simps array_set_val_def
    using array_assms
    apply (auto)
    using chunk_fits_cvs_of_size_update fits_array apply auto[1]
    unfolding array_size_def
    by simp

  have [simp]: "size_chunkval_nat (array_chunkvals array ! idx) = size_chunk_nat chunk"
    using chunk_fits_chunkval_size by auto

  note [simp] = array_same_def[OF \<open>SAME_DEF array_def array\<close>]

  show ?case
    unfolding Sarray_store_def Earray_idx_offset_def
    apply vcg
    apply (simp add: array_offset_ok extr)
    apply vcg
    unfolding array_set_val_def
    apply (simp add: sep_algebra_simps extr_new)
    unfolding array_size_def
    apply simp
    by vcg
qed

end