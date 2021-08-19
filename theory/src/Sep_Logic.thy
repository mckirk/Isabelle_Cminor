theory Sep_Logic
  imports
"../compcert/Cminor"
Sep_Generic_Wp
Basic_Lens
State_Ops
TSA_Map
begin

section \<open>Misc\<close>

fun tsa_opt_to_option :: "'a tsa_opt \<Rightarrow> 'a option" where
  "tsa_opt_to_option (TRIV v) = Some v"
| "tsa_opt_to_option ZERO = None"

fun option_to_tsa_opt :: "'a option \<Rightarrow> 'a tsa_opt" where
  "option_to_tsa_opt (Some v) = TRIV v"
| "option_to_tsa_opt None = ZERO"

lemma option_to_tsa_opt_inj: "option_to_tsa_opt x = option_to_tsa_opt y \<Longrightarrow> x = y"
  by (metis option_to_tsa_opt.elims tsa_opt.distinct(1) tsa_opt.inject)

abbreviation "I\<^sub>0 \<equiv> \<lambda>_. True" (* the 'always' invariant *)

interpretation mem_access_lens: basic_lens "BLENS mem_access (\<lambda>ma' m. m\<lparr>mem_access := ma'\<rparr>)"
  apply standard
  by auto

lemmas mem_access_laws = mem_access_lens.laws[unfolded mem_access_lens.ground_defs, simplified basic_lens.sel]

interpretation mem_contents_lens: basic_lens "BLENS mem_contents (\<lambda>mc' m. m\<lparr>mem_contents := mc'\<rparr>)"
  apply standard
  by auto

lemmas mem_contents_laws = mem_contents_lens.laws[unfolded mem_contents_lens.ground_defs, simplified basic_lens.sel]

section \<open>Environment\<close>

type_synonym cminor_env = "(ident, val) tsa_map"

definition env_access :: "ident \<Rightarrow> (val option \<lhd> env)" where
  "env_access i \<equiv> BLENS (\<lambda>e. e i) (\<lambda>v e. e(i := v))"

interpretation env_access: tsa_map_\<alpha> env_access Some id
  unfolding env_access_def
  apply standard
  by auto

locale env_assns = Lc: basic_lens Lc + L\<alpha>: sep_algebra_lens L\<alpha>
  for \<alpha>_full :: "'fc \<Rightarrow> 'fa::stronger_sep_algebra"
  and Lc :: "(env \<lhd> 'fc)"
  and L\<alpha> :: "(cminor_env \<lhd> 'fa)" +
assumes lenses:
  "L\<alpha>.get (\<alpha>_full s) = env_access.\<alpha> (Lc.get s)"
  "L\<alpha>.put (env_access.\<alpha> a) (\<alpha>_full s) = \<alpha>_full (Lc.put a s)"
fixes state_I :: "'fc \<Rightarrow> bool"
assumes I_independent: "\<And>a. state_I (Lc.put a s) \<longleftrightarrow> state_I s"
begin

sublocale compose_lens_assertion Some TRIV env_access.\<alpha> "\<lambda>vo. vo = None" env_access sep_algebra_func_lens
  apply (simp add: compose_lens_assertion_def; safe)
     apply (simp add: env_access.lens_assertion_axioms[simplified])
    apply (simp add: Lc.basic_lens_axioms)
   apply (simp add: L\<alpha>.sep_algebra_lens_axioms)
  unfolding compose_lens_assertion_axioms_def
  by (auto simp add: lenses)

lemmas concrete_unfold = concrete.compose_inner_unfold[OF env_access_def[abs_def]]

definition "op_concrete_put i v' \<equiv> Update (concrete.put i (Some v'))"

definition "op_set_params \<equiv> \<lambda>vs is. Update (Lc.put (set_params vs is))"
definition "op_set_locals \<equiv> \<lambda>is. Update (Lc.update (set_locals is))"
definition "op_set_optvar \<equiv> \<lambda>io v. Update (Lc.update (set_optvar io v))"

lemma wp_set_optvar_none[vcg_decomp_rules]:
  assumes "Q r_dummy s"
  shows "wp_stateop (op_set_optvar None v') Q s"
  using assms
  unfolding op_concrete_put_def op_set_optvar_def concrete_unfold
  by (simp add: set_optvar.simps[abs_def] Lc.update_id)

lemma wp_set_optvar_some[vcg_decomp_rules]:
  assumes "wp_stateop (op_concrete_put i v') Q s"
  shows "wp_stateop (op_set_optvar (Some i) v') Q s"
  using assms
  unfolding op_concrete_put_def op_set_optvar_def concrete_unfold
  by (simp add: set_optvar.simps[abs_def])

lemma ht_set[vcg_rules]:
  shows "state_ht \<alpha>_full state_I
          (assn_is i v)
          (op_concrete_put i v')
          (\<lambda>_. assn_is i v')"
  apply (rule state_htI)
  unfolding op_concrete_put_def
  apply (auto split: option.splits simp: assn_is_update[simplified] intro!: wp_stateopI)
  unfolding concrete.compose_defs Lc.update_def
  using I_independent by simp

end

section \<open>Memory\<close>

type_synonym cminor_ptr = "(block \<times> Z)"

lemma ptrI: "(\<And>b ofs. p = (b, ofs) \<Longrightarrow> f (b, ofs)) \<Longrightarrow> f p"
  by (metis surj_pair)

type_synonym cminor_mem = "(cminor_ptr, memval) tsa_map"

type_synonym cminor_mem_range = "memval list"

type_synonym cminor_perm = "perm_kind \<Rightarrow> permission option"

definition perm_none :: cminor_perm where
  "perm_none \<equiv> \<lambda>_. None"
definition perm_freeable :: cminor_perm where
  "perm_freeable \<equiv> \<lambda>_. Some Freeable"

lemma perms_different[iff]:
  "perm_none \<noteq> perm_freeable"
  unfolding perm_none_def perm_freeable_def
  by (meson option.distinct(1))

definition mem_ptr_lens :: "cminor_ptr \<Rightarrow> ((memval \<times> cminor_perm) \<lhd> mem)" where
  "mem_ptr_lens \<equiv> \<lambda>p. BLENS
    (\<lambda>m. ((mem_contents m) (fst p) (snd p), (mem_access m) (fst p) (snd p)))
    (\<lambda>(mv', perm').
      mem_contents_update (PMap.update (fst p) (ZMap.set (snd p) mv')) o
      mem_access_update (PMap.update (fst p) (\<lambda>block ofs'. if ofs' = snd p then perm' else block ofs')))"

interpretation mem_ptr_lens: tsa_map_\<alpha> mem_ptr_lens
  "\<lambda>mv. (mv, perm_freeable)" "\<lambda>(mv, perm). if perm = perm_freeable then Some mv else None"
  unfolding mem_ptr_lens_def
  apply standard
  by (auto intro!: mem.equality ext split: if_splits option.splits)

lemma mem_ptr_lens_unfold_adapter:
  assumes "mem_ptr_lens \<equiv> \<lambda>(b, ofs). BLENS (get_f (b, ofs)) (put_f (b, ofs))"
  shows "mem_ptr_lens \<equiv> \<lambda>p. BLENS (get_f p) (put_f p)"
  unfolding assms
  by (simp add: cond_case_prod_eta)

lemmas mem_ptr_lens_unfold =
  mem_ptr_lens.concrete.unfold[OF mem_ptr_lens_def, where ?p="(b, ofs)", simplified fst_conv snd_conv] for b ofs

lemma mem_ptr_lens_nextblock_indifferent:
  "mem_ptr_lens.\<alpha> (mem_nextblock_update f m) = mem_ptr_lens.\<alpha> m"
  unfolding mem_ptr_lens.\<alpha>_def
  apply standard+
  by (auto split: option.splits if_splits prod.splits simp: mem_ptr_lens_unfold)

locale mem_assns_defs =
  mem_lens: basic_lens Lc_mem +
  mem_\<alpha>_lens: sep_algebra_lens L\<alpha>_mem
  for Lc_mem :: "(mem \<lhd> 'fc)"
  and L\<alpha>_mem :: "(cminor_mem \<lhd> 'fa::stronger_sep_algebra)"

locale mem_assns = mem_assns_defs Lc_mem L\<alpha>_mem
  for \<alpha>_full :: "'fc \<Rightarrow> 'fa::stronger_sep_algebra"
  and Lc_mem :: "(mem \<lhd> 'fc)"
  and L\<alpha>_mem :: "(cminor_mem \<lhd> 'fa)" +
assumes mem_lenses:
  "mem_\<alpha>_lens.get (\<alpha>_full s) = mem_ptr_lens.\<alpha> (mem_lens.get s)"
  "\<And>m. mem_\<alpha>_lens.put (mem_ptr_lens.\<alpha> m) (\<alpha>_full s) = \<alpha>_full (mem_lens.put m s)"
assumes nextblock_indifferent:
  "\<And>f. \<alpha>_full (mem_lens.update (mem_nextblock_update f) s) = \<alpha>_full s"
begin

definition "invariants \<equiv> \<lambda>fc. Mem.mem_invariants (mem_lens.get fc)"

lemma invariants_update:
  assumes "invariants s"
  assumes "\<And>m. Mem.mem_invariants m \<Longrightarrow> Mem.mem_invariants (f m)"
  shows "invariants (mem_lens.update f s)"
  using assms
  unfolding invariants_def
  by (simp add: mem_lens.get_update)

abbreviation "htriple \<equiv> state_ht \<alpha>_full invariants"
abbreviation "htriple_weak \<equiv> state_ht \<alpha>_full I\<^sub>0" (* without invariants, for intermediate steps*)

lemmas htripleI = state_op.htripleI

sublocale compose_lens_assertion "\<lambda>mv. (mv, perm_freeable)" TRIV mem_ptr_lens.\<alpha>
  "\<lambda>(mv, perm). perm \<noteq> perm_freeable" mem_ptr_lens sep_algebra_func_lens Lc_mem L\<alpha>_mem \<alpha>_full
  apply (simp add: compose_lens_assertion_def; safe)
  using mem_ptr_lens.lens_assertion_axioms
     apply (simp split: prod.splits if_splits)
  apply (smt (verit) Pair_inject cond_case_prod_eta)
    apply (simp add: mem_lens.basic_lens_axioms)
  apply (simp add: mem_\<alpha>_lens.sep_algebra_lens_axioms)
  unfolding compose_lens_assertion_axioms_def
  by (simp add: mem_lenses)

lemma concrete_get:
  shows "concrete.get (b, ofs) s = (mem_contents (mem_lens.get s) b ofs, mem_access (mem_lens.get s) b ofs)"
  unfolding concrete.compose_defs
  unfolding mem_ptr_lens_unfold
  by auto

lemma concrete_is:
  shows "concrete.is (b, ofs) (mv, perm) s = (mem_contents (mem_lens.get s) b ofs = mv \<and> mem_access (mem_lens.get s) b ofs = perm)"
  unfolding concrete.compose_defs
  unfolding mem_ptr_lens_unfold
  by auto

schematic_goal concrete_put:
  shows "concrete.put (b, ofs) (mv, perm)
      = (mem_lens.update ?x)"
  unfolding concrete.compose_defs
  unfolding mem_ptr_lens_unfold
  by simp
  
subsection \<open>Assertions\<close>

lemma assn_is_perm: "(assn_is (b, ofs) v ** F) (\<alpha>_full s) \<Longrightarrow> Mem.perm (mem_lens.get s) b ofs kind perm"
  apply (simp add: Mem.perm.simps Mem.perm_order'.simps perm_order.simps assn_is_concrete)
  unfolding perm_freeable_def
  using concrete.laws concrete_get by auto

definition val_range :: "cminor_ptr \<Rightarrow> memval list \<Rightarrow> 'fa \<Rightarrow> bool" where
"val_range \<equiv>
  \<lambda> (b, ofs) vs.
  (\<Union>*i \<in> {0..<length vs}. assn_is (b, ofs + int i) (vs ! i))"

lemma val_range_unfold: "val_range (b, ofs) vs = (\<Union>*i \<in> {0..<length vs}. assn_is (b, ofs + int i) (vs ! i))"
  unfolding val_range_def
  by auto

lemma val_range0[simp]: "val_range p [] = \<box>"
  unfolding val_range_def by (auto split: prod.splits)

lemma split_assn_eq:
  assumes "P = P'"
  assumes "Q = Q'"
  shows "(P ** Q) = (P' ** Q')"
  using assms
  by simp

lemma val_range_split:
  assumes "sz \<le> length vs"
  shows "val_range (b, ofs) vs = (val_range (b, ofs) (take sz vs) \<and>* val_range (b, ofs + sz) (drop sz vs))"
proof -
  let ?r1 = "{0..<sz}"
  let ?r2 = "{sz..<length vs}"

  have split_range: "{0..<length vs} = ?r1 \<union> ?r2" "?r1 \<inter> ?r2 = {}" using assms by auto

  note split_union = sep_set_img_union[OF split_range(2)]

  have split_map_lhs:
      "\<And>x i. x + int sz + int i = x + int (i + sz)"
      "\<And>i. drop sz vs ! i = vs ! (i + sz)"
    using assms
    by (auto simp add: add.commute)

  have "inj_on (\<lambda>i. i + sz) {0..<length (drop sz vs)}" by simp
  note split_map = sep_set_img_map[OF this, of "\<lambda>i. assn_is (b, ofs + i) (vs ! i)", symmetric]

  show ?thesis unfolding val_range_unfold
    unfolding split_range
    unfolding split_union
    apply (rule split_assn_eq)
     apply (rule sep_set_img_cong)
    using assms apply simp
     apply simp
    unfolding split_map_lhs
    unfolding split_map
    by (simp add: assms)
qed

lemma val_range_split_deltalen:
  assumes "delta+len \<le> length vs"
  shows "val_range (b, ofs) vs
      = (val_range (b, ofs) (take delta vs)
      ** val_range (b, ofs+delta) (take len (drop delta vs))
      ** val_range (b, ofs+delta+len) (drop (delta+len) vs))"
proof -
  from assms have "delta \<le> length vs"
    by auto

  note split1 = val_range_split[OF this]

  from assms have "len \<le> length (drop delta vs)"
    by auto

  note split2 = val_range_split[OF this]

  show ?thesis
    apply (subst split1)
    apply (subst split2)
    by (simp add: add.commute)
qed

lemma val_range_step:
  shows "val_range (b, ofs) (v # vs) = (assn_is (b, ofs) v ** val_range (b, ofs + 1) vs)"
  using val_range_split[of 1 "v # vs"] unfolding val_range_unfold
  by auto

lemma val_range_step_end:
  shows "val_range (b, ofs) (vs @ [v]) = (assn_is (b, ofs+length vs) v ** val_range (b, ofs) vs)"
  apply (simp add: val_range_split[of "length vs" "vs @ [v]"])
  apply (subst sep_conj_commute)
  apply (rule sep_conj_trivial_strip2)
  unfolding val_range_unfold
  by auto

lemma val_range_split_concat:
  shows "val_range (b, ofs) (vs1@vs2)
      = (val_range (b, ofs) vs1 ** val_range (b,ofs + length vs1) vs2)"
  apply (induction vs1 arbitrary: ofs)
   apply simp
  apply (simp add: val_range_step)
  by (smt (z3))

lemmas val_range_merge = val_range_split_concat[symmetric]

lemma val_range_range_perm:
  notes [simp] = Mem.range_perm_def
  shows "(val_range (b, ofs) vs \<and>* F) (\<alpha>_full s) \<Longrightarrow> Mem.range_perm (mem_lens.get s) b ofs (ofs + length vs) Cur perm"
proof (induction vs arbitrary: ofs F)
  case Nil
  then show ?case
    by simp
next
  case (Cons a vs)

  from Cons(2)
  have ofs_perm: "Mem.perm (mem_lens.get s) b ofs Cur perm"
    by (simp add: val_range_step assn_is_perm)

  obtain F' where F': "(val_range (b, ofs+1) vs \<and>* F') (\<alpha>_full s)"
    using Cons(2)
    apply (simp add: val_range_step)
    apply (subst(asm)(2) sep_conj_commute)
    apply (subst(asm) sep_conj_assoc)
    by auto

  note IH = Cons(1)[OF this]

  then show ?case
    using ofs_perm apply auto
    by (smt (verit) atLeastLessThan_iff)
qed

definition mem_chunk :: "memory_chunk \<Rightarrow> cminor_ptr \<Rightarrow> cminor_mem_range \<Rightarrow> 'fa \<Rightarrow> bool" where
  "mem_chunk \<equiv> \<lambda> chunk p vs.
  \<up>(length vs = size_chunk_nat chunk \<and> align_chunk chunk dvd (snd p)) ** val_range p vs"

lemma range_to_chunk:
  assumes "length vs = size_chunk_nat chunk"
  assumes "align_chunk chunk dvd (snd p)"
  shows "val_range p vs = mem_chunk chunk p vs"
  unfolding mem_chunk_def
  using assms
  by (simp add: sep_algebra_simps)

abbreviation "mem_val chunk p v \<equiv> mem_chunk chunk p (encode_val chunk v)"

inductive chunk_fit :: "memory_chunk \<Rightarrow> val \<Rightarrow> bool" where
  "chunk_fit Mint32 (Vint n)"
| "chunk_fit Many32 (Vint n)"
| "chunk_fit Mfloat32 (Vsingle f)"
| "chunk_fit Many32 (Vsingle f)"
| "chunk_fit Mint64 (Vlong n)"
| "chunk_fit Many64 (Vlong n)"
| "chunk_fit Mfloat64 (Vfloat f)"
| "chunk_fit Many64 (Vfloat f)"
| "chunk_fit Mint64 (Vptr b ofs)"
| "chunk_fit Many64 (Vptr b ofs)"

lemma [iff]: "chunk_fit Mptr (Vptrofs sz)"
  unfolding Mptr_def Vptrofs_def
  by (simp add: chunk_fit.intros)

lemma chunk_fit_load_result[simp]:
  assumes "chunk_fit chunk v"
  shows "Val.load_result chunk v = v"
  using assms
  apply (rule chunk_fit.cases)
  by (auto simp: encode_val.simps decode_val.simps)

lemma chunk_fit_length:
  assumes "chunk_fit chunk v" "chunk_fit chunk v'"
  shows "length (encode_val chunk v) = length (encode_val chunk v')"
  apply (cases rule: chunk_fit.cases[OF assms(1)]; cases rule: chunk_fit.cases[OF assms(2)])
  by (auto simp: encode_val.simps)

abbreviation "mem_val_fit chunk p v \<equiv> \<up>(chunk_fit chunk v) ** mem_val chunk p v"

subsection \<open>Cminor Ops\<close>

definition "op_concrete_get p \<equiv> Read (concrete.get p)"
definition "op_concrete_put v p \<equiv> Update (concrete.put p v)"

definition "op_valid_access \<equiv> \<lambda>chunk (b, ofs) perm. Read (\<lambda>fc. Mem.valid_access (mem_lens.get fc) chunk b ofs perm)"

definition "op_getN \<equiv> \<lambda>sz (b, ofs). Read (\<lambda>fc. Mem.getN sz ofs (mem_contents (mem_lens.get fc) b))"
definition "op_setN \<equiv> \<lambda>vs (b, ofs). Update (mem_lens.update (mem_contents_update (PMap.update b (Mem.setN vs ofs))))"

definition "op_load \<equiv> \<lambda>chunk (b, ofs). ReadMaybe (\<lambda>fc. Mem.load chunk (mem_lens.get fc) b ofs)"
definition "op_store \<equiv> \<lambda>chunk (b, ofs) v. UpdateMaybe (mem_lens.update_maybe (\<lambda>m. Mem.store chunk m b ofs v))"

definition "op_loadv chunk vptr \<equiv> ReadMaybe (\<lambda>fc. Mem.loadv chunk (mem_lens.get fc) vptr)"
definition "op_storev chunk vptr v \<equiv> UpdateMaybe (mem_lens.update_maybe (\<lambda>m. Mem.storev chunk m vptr v))"

definition "op_alloc lo hi \<equiv> ReadUpdate (\<lambda>fc. case Mem.alloc (mem_lens.get fc) lo hi of (m', b) \<Rightarrow> (mem_lens.put m' fc, b))"
definition "op_free b lo hi \<equiv> UpdateMaybe (mem_lens.update_maybe (\<lambda>m. Mem.free m b lo hi))"

definition "op_outcome_free_mem out sp sz \<equiv> UpdateMaybe (mem_lens.update_maybe (\<lambda>m. outcome_free_mem_func out m sp sz))"

(* wrappers *)

definition "op_decode_chunk chunk p \<equiv> op_getN (size_chunk_nat chunk) p"
definition "op_encode_chunk chunk v' p \<equiv> op_setN (encode_val chunk v') p"

lemma [iff]: "readonly_op (op_concrete_get p)" unfolding op_concrete_get_def ..
lemma [iff]: "readonly_op (op_valid_access chunk p perm)" unfolding op_valid_access_def by (auto split: prod.splits)
lemma [iff]: "readonly_op (op_getN sz p)" unfolding op_getN_def by (auto split: prod.splits)
lemma [iff]: "readonly_op (op_loadv chunk vptr)" unfolding op_loadv_def ..
lemma [iff]: "readonly_op (op_decode_chunk chunk p)" unfolding op_decode_chunk_def ..

subsection \<open>WP decomp rules\<close>

lemma setN_unpack:
  "Mem.setN (v # vs) ofs = (Mem.setN vs (ofs+1)) o (ZMap.set ofs v)"
  apply standard+
  by (simp add: Mem.setN.simps)

lemma wp_getN_induct:
  assumes "wp_stateop (op_concrete_get (b, ofs)) (\<lambda>(v, po). wp_stateop (op_getN sz (b, ofs+1)) (\<lambda>vs. Q (v # vs))) s"
  shows "wp_stateop (op_getN (Suc sz) (b, ofs)) Q s"
  using assms unfolding op_concrete_get_def op_getN_def
  using concrete_get by (auto simp: Mem.getN.simps)

lemma mem_lens_update_equ: "\<And>f f'. (f (mem_lens.get s) = f' (mem_lens.get s)) \<Longrightarrow> mem_lens.update f s = mem_lens.update f' s"
  by (metis mem_lens.update_def)

lemma wp_setN_induct:
  notes setN_unpack[simp]
  assumes "concrete.get (b, ofs) s = (v', po)"
  assumes "wp_stateop (op_concrete_put (v, po) (b, ofs)) (\<lambda>_. wp_stateop (op_setN vs (b, ofs+1)) Q) s"
  shows "wp_stateop (op_setN (v # vs) (b, ofs)) Q s"
  using assms unfolding op_concrete_put_def op_setN_def
  apply (simp add: concrete.compose_defs mem_lens.laws)
  unfolding mem_ptr_lens_unfold
  apply clarify
proof (goal_cases)
  case 1

  have Q_equ: "\<And>x x'. x = x' \<Longrightarrow> Q r_dummy x = Q r_dummy x'"
    by simp

  have access_update:
    "(mem_access_update (\<lambda>m. m(b := \<lambda>ofs'. if ofs' = ofs then mem_access (mem_lens.get s) b ofs else m b ofs')))
     (mem_lens.get s) = (mem_lens.get s)"
    apply (rule mem.equality)
       apply auto
    apply standard+
    by auto

  show ?case
    apply (rule iffD1[OF _ 1(1)])
    apply (rule Q_equ)
    apply (rule mem_lens_update_equ)
    by (simp add: access_update)
qed

lemma wp_load[vcg_decomp_rules]:
  assumes "wp_stateop (op_valid_access chunk p Readable)
    (\<lambda>r fc. r \<and> wp_stateop (op_decode_chunk chunk p)
      (\<lambda>vs. Q (decode_val chunk vs)) fc) s"
  shows "wp_stateop (op_load chunk p) Q s"
  apply (cases p)
  using assms
  unfolding op_valid_access_def op_getN_def op_load_def op_decode_chunk_def
  by (auto split: option.splits simp: Mem.loadv.simps Mem.load.simps)

lemma wp_loadv[vcg_decomp_rules]:
  assumes "wp_stateop (op_load chunk (b, uint ofs)) Q s"
  shows "wp_stateop (op_loadv chunk (Vptr b ofs)) Q s"
  using assms
  unfolding op_load_def op_loadv_def
  by (auto simp: Mem.loadv.simps)

lemma wp_store:
  assumes "wp_stateop (op_valid_access chunk p Writable)
    (\<lambda>r fc. r \<and> wp_stateop (op_encode_chunk chunk v' p) Q fc) s"
  shows "wp_stateop (op_store chunk p v') Q s"
  apply (cases p)
  using assms
  unfolding op_valid_access_def op_setN_def op_store_def op_encode_chunk_def
  apply (auto simp: Mem.storev.simps Mem.store.simps mem_lens.update_maybe_def split: option.splits)
  by (simp add: mem_lens.update_def)

lemma wp_storev[vcg_decomp_rules]:
  assumes "wp_stateop (op_store chunk (b, uint ofs) v') Q s"
  shows "wp_stateop (op_storev chunk (Vptr b ofs) v') Q s"
  using assms
  unfolding op_store_def op_storev_def
  by (auto simp: Mem.storev.simps)

(* lemma wp_outcome_free_mem:
  assumes "(\<exists>x. out = Out_tailcall_return x) \<Longrightarrow> Q r_dummy s"
  assumes "\<not>(\<exists>x. out \<noteq> Out_tailcall_return x) \<Longrightarrow> wp_stateop (op_free sp 0 sz) Q s"
  shows "wp_stateop (op_outcome_free_mem out sp sz) Q s"
  unfolding op_free_def op_outcome_free_mem_def mem_lens.update_maybe_def
  apply (cases "\<exists>x. out = Out_tailcall_return x")
  apply (rule wp_stateopI)
   apply (auto split: option.splits simp: mem_lens.laws)
   apply (cases out)
  apply auto *)

subsection \<open>HT rules (without invariant-guarantee)\<close>

lemma ht_concrete_get[vcg_rules]:
  shows "htriple_weak
          (assn_is p v)
          (op_concrete_get p)
          (\<lambda>r. \<up>(r = (v, perm_freeable)) ** assn_is p v)"
  apply (cases p)
  apply (rule state_htI)
  apply (simp add: op_concrete_get_def)
  subgoal for b ofs F s
    apply (rule sep_conjI[of _ 0 _ "(\<alpha>_full s)"])
    unfolding pred_lift_def
    by (auto simp add: assn_is_concrete concrete.laws)
  done

lemma ht_concrete_set[vcg_rules]:
  shows "htriple_weak
          (assn_is p v)
          (op_concrete_put (v', perm_freeable) p)
          (\<lambda>_. assn_is p v')"
  apply (rule state_htI)
  unfolding op_concrete_put_def
  by (auto split: option.splits simp: assn_is_update[simplified])

lemma ht_getN[vcg_rules]:
  assumes "len = length vs"
  shows "htriple_weak
          (val_range p vs)
          (op_getN len p)
          (\<lambda>r. \<up>(r = vs) ** val_range p vs)"
  apply (cases p)
  subgoal for b ofs
  using assms
proof (induction vs arbitrary: p ofs len)
  case Nil
  then show ?case
    unfolding val_range_def op_getN_def
    apply simp
    apply (rule state_htI)
    by (auto simp: Mem.getN.simps pure_true_conv)
next
  case (Cons v vs)

  then obtain p' len' where p': "p' = (b, ofs+1)" "len' = length vs" by simp

  note IH[vcg_rules] = Cons(1)[OF this, unfolded p'(1)]

  have [simp]: "len = Suc len'"
    by (simp add: Cons.prems \<open>len' = length vs\<close>)

  note wp_getN_induct[vcg_decomp_rules]

  show ?case
    apply (simp add: Cons val_range_step)
    by vcg
qed
  done

lemma ht_setN[vcg_rules]:
  assumes "length vs = length vs'"
  shows "htriple_weak
          (val_range p vs)
          (op_setN vs' p)
          (\<lambda>_. val_range p vs')"
  apply (cases p)
  subgoal for b ofs
  using assms
proof (induction vs vs' arbitrary: p ofs rule: list_induct2)
  case Nil

  have [simp]: "\<And>p. Mem.setN [] p = id"
    apply standard+
    by (simp add: Mem.setN.simps)

  have [simp]: "\<And>b. PMap.update b id = id"
    by auto

  show ?case
    apply (rule state_htI)
    by (simp add: op_setN_def val_range_def mem_lens.laws mem_update_id)
next
  case (Cons v vs v' vs')

  note p = \<open>p = (b, ofs)\<close>
  obtain p' where p': "p' = (b, ofs+1)" by simp

  note Cons(2)[OF this, unfolded p', vcg_rules]

  note wp_setN_induct[of b ofs _ v perm_freeable, vcg_decomp_rules]

  have vcg_help: "\<And>F s. STATE \<alpha>_full I\<^sub>0 (assn_is (b, ofs) v \<and>* val_range (b, ofs + 1) vs \<and>* F) s \<Longrightarrow>
           concrete.get (b, ofs) s = (v, perm_freeable)"
    unfolding STATE_def
    apply simp
    using assn_is_concrete
    by (simp add: concrete.laws(5))

  show ?case
    apply (simp add: p val_range_step)
    using vcg_help
    by vcg
qed
  done

lemma ht_valid_access[vcg_rules]:
  shows "htriple_weak
        (mem_chunk chunk p vs)
        (op_valid_access chunk p perm)
        (\<lambda>r. \<up>r ** mem_chunk chunk p vs)"
  apply (cases p)
  apply (rule state_htI)
  unfolding op_valid_access_def mem_chunk_def
  apply (auto simp add: Mem.valid_access.simps pred_lift_extract_simps)
  using val_range_range_perm
  by (metis)

lemma ht_decode_chunk[vcg_rules]:
  shows "htriple_weak
          (mem_val chunk p v)
          (op_decode_chunk chunk p)
          (\<lambda>r. \<up>(decode_val chunk r = Val.load_result chunk v) ** (mem_val chunk p v))"
  unfolding op_decode_chunk_def
  apply vcg
  unfolding mem_chunk_def
  by vcg

lemma ht_encode_chunk[vcg_rules]:
  shows "htriple_weak
    (mem_chunk chunk p vs)
    (op_encode_chunk chunk v' p)
    (\<lambda>_. (mem_val chunk p v'))"
  unfolding op_encode_chunk_def
  apply vcg
  unfolding mem_chunk_def
  by vcg

lemma ht_store[vcg_rules]: (* needs to be explicit rule to proof invariants *)
  notes [vcg_decomp_rules] = wp_store
  shows "htriple_weak
    (mem_chunk chunk p vs)
    (op_store chunk p v')
    (\<lambda>_. mem_val chunk p v')"
  by vcg

lemma ht_free[vcg_rules]:
  assumes [iff]: "lo \<le> hi"
  defines "len \<equiv> nat (hi - lo)"
  assumes len_vs: "length vs = len"
  shows "htriple_weak
    (val_range (b, lo) vs)
    (op_free b lo hi)
    (\<lambda>_. \<box>)"
  unfolding op_free_def mem_lens.update_maybe_def
  apply (rule state_htI)
  supply [simp] = val_range_range_perm[where ?ofs=lo and ?vs=vs, unfolded len_vs, unfolded len_def, simplified]
  apply (simp add: Mem.free.simps split: option.splits)
  subgoal for F s
  using assms
proof (induction vs arbitrary: lo len s)
  case Nil

  have [simp]: "\<And>ofs x. (if lo \<le> ofs \<and> ofs < lo then None else x) = x"
    by auto

  with Nil show ?case
    by (simp add: Mem.unchecked_free.simps mem_update_id mem_lens.laws)
next
  case (Cons v vs)

  then have v_s: "(assn_is (b, lo) v ** val_range (b, lo + 1) vs \<and>* F) (\<alpha>_full s)"
    using val_range_step
    by (simp)

  note range_s' = assn_is_destroy[where ?v'="(v, perm_none)", simplified, OF this]
  let ?step = "concrete.put (b, lo) (v, perm_none)"
  let ?s' = "?step s"

  have "lo + 1 \<le> hi" "length vs = nat (hi - (lo + 1))" using \<open>length (v # vs) = nat (hi - lo)\<close>
    by auto

  note IH = Cons(1)[OF range_s' this]

  have prev_v: "(mem_contents (mem_lens.get s))(b := (mem_contents (mem_lens.get s) b)(lo := v))
              = mem_contents (mem_lens.get s)"
    using v_s
    unfolding assn_is_concrete concrete_is
    by (auto intro!: ext)
                
  have "((mem_lens.update (\<lambda>m. Mem.unchecked_free m b (lo + 1) hi)) o (?step)) s
      = mem_lens.update (\<lambda>m. Mem.unchecked_free m b lo hi) s"
    apply (subst concrete_put)
    apply (subst mem_lens.update_comp')
    unfolding mem_lens.update_def
    apply (subst mem_lens.put_equality)
    apply (simp add: Mem.unchecked_free.simps concrete_put)
    apply (rule mem.equality)
    using \<open>lo + 1 \<le> hi\<close>
    by (auto simp: prev_v perm_none_def intro!: ext)

  then show ?case
    unfolding mem_lens.update_def
    using IH by auto
qed
  done

subsection \<open>HT rules (with invariants)\<close>

lemma from_weak_unchanged:
  assumes ht: "htriple_weak P c Q"
  assumes ro: "readonly_op c"
  shows "htriple P c Q"
  using ro
  apply (rule readonly_op.cases)
  using ht
  unfolding state_op.htriple_def
    apply (auto split: option.splits)
  by force

lemmas ht_concrete_get_inv[vcg_rules] = from_weak_unchanged[OF ht_concrete_get, simplified]
lemmas ht_getN_inv[vcg_rules] = from_weak_unchanged[OF ht_getN, simplified]
lemmas ht_decode_chunk_inv[vcg_rules] = from_weak_unchanged[OF ht_decode_chunk, simplified]
lemmas ht_valid_access_inv[vcg_rules] = from_weak_unchanged[OF ht_valid_access, simplified]
  
lemma ht_store_inv[vcg_rules]:
  notes [vcg_decomp_rules] = wp_store
  shows "htriple
    (mem_chunk chunk p vs)
    (op_store chunk p v')
    (\<lambda>_. mem_val chunk p v')"
  using ht_store
  apply (rule state_op.htriple_strengthen_inv)
   apply simp
  unfolding op_store_def
  apply (simp split: prod.splits option.splits add: mem_lens.update_maybe_def mem_lens.laws invariants_def)
  using Mem.store_inv
  by auto

lemma ht_alloc_inv[vcg_rules]:
  assumes "lo \<le> hi"
  defines "len \<equiv> nat (hi - lo)"
  shows "htriple
    (\<box>)
    (op_alloc lo hi)
    (\<lambda>b. val_range (b, lo) (replicate len Undef))"
  apply (rule state_htI)
  unfolding op_alloc_def
proof (goal_cases)
  case (1 F s)

  obtain m where m: "m = mem_lens.get s" by simp

  obtain m'' b where m''_alloc: "(m'', b) = Mem.alloc m lo hi"
    by (metis old.prod.exhaust)

  then obtain s'' where s''_alloc: "s'' = mem_lens.put m'' s"
    by simp

  with m''_alloc 1(1) have inv_s'': "invariants s''"
    using invariants_def Mem.alloc_inv m
    by (metis mem_lens.get_put)

  have b: "b = mem_nextblock m"
    using m''_alloc Mem.alloc.simps by auto

  let ?contents_update = "mem_contents_update (PMap.set (mem_nextblock m) (ZMap.init Undef))"
  let ?access_update = "\<lambda>hi. mem_access_update (PMap.set (mem_nextblock m) (\<lambda>ofs k. if lo \<le> ofs \<and> ofs < hi then Some Freeable else None))"
  let ?contents_access_update = "\<lambda>hi. ?contents_update o (?access_update hi)"
  let ?nextblock_update = "mem_nextblock_update ((+) 1)"

  obtain m' where m':
    "m' = (?contents_access_update hi) m"
    "?nextblock_update m' = m''"
    using m m''_alloc
    by (simp add: Mem.alloc.simps)

  then obtain s' where s':
    "s' = mem_lens.update (?contents_access_update hi) s"
    "mem_lens.update ?nextblock_update s' = s''"
    using Mem.alloc.simps m mem_lens.laws mem_lens.update_def s''_alloc
    by auto

  note mem_inv' = \<open>invariants s\<close>[unfolded invariants_def m[symmetric], unfolded Mem.mem_invariants_def]
  then have mem_inv:
    "(\<And>b ofs k. mem_nextblock m \<le> b \<Longrightarrow> mem_access m b ofs k = None)"
    "(\<And>b ofs. mem_nextblock m \<le> b \<Longrightarrow> mem_contents m b ofs = Undef)"
    by auto

  have "(val_range (b, lo) (replicate len Undef) \<and>* F) (\<alpha>_full s')"
    using assms s'(1) 1
  proof (induction len arbitrary: hi m' s')
    case 0

    have [simp]: "(mem_contents_update (\<lambda>a b. if b = mem_nextblock m then \<lambda>a. Undef else a b)
       (mem_access_update (\<lambda>a b. if b = mem_nextblock m then \<lambda>ofs. Map.empty else a b) m)) = m"
      apply (rule mem.equality)
      using mem_inv
      by (auto intro!: ext)

    have [simp]: "\<And>ofs. (lo \<le> ofs \<and> ofs < lo) = False" by simp

    from 0 have "s' = s"
      apply (simp add: Mem.alloc.simps mem_update_id(2) mem_lens.laws mem_lens.update_def m[symmetric])
      by (simp add: m mem_lens.put_get)

    then show ?case
      unfolding val_range_def
      using "1"(2) by auto
  next
    case (Suc len)

    obtain hi_prev where hi_prev: "hi = hi_prev + 1"
      using diff_eq_eq by auto

    have "lo \<noteq> hi" using \<open>Suc len = nat (hi - lo)\<close> by simp

    then have lo_hi_prev: "lo \<le> hi_prev" "len = nat (hi_prev - lo)"
      using \<open>lo \<le> hi\<close> hi_prev apply simp
      using \<open>Suc len = nat (hi - lo)\<close> hi_prev by simp

    moreover obtain s_prev where s_prev: "s_prev = mem_lens.update (?contents_access_update hi_prev) s"
      by simp

    note val_range_prev = Suc(1)[OF calculation this \<open>invariants s\<close> \<open>(\<box> \<and>* F) (\<alpha>_full s)\<close>]

    from lo_hi_prev have hi_prev_lo_len: "hi_prev = lo + int len"
      by simp

    let ?single_update = "mem_ptr_lens.concrete.put (mem_nextblock m, hi_prev) (Undef, perm_freeable)"

    have single_update: "?contents_access_update hi = ?single_update o (?contents_access_update hi_prev)"
      apply standard
      apply (rule mem.equality)
      unfolding mem_ptr_lens_unfold
      using mem_inv
      by (auto intro!: ext simp add: perm_freeable_def hi_prev lo_hi_prev)

    have "s' = mem_lens.update (?single_update) s_prev"
      using s_prev Suc(4) single_update
      using mem_lens.update_comp by auto

    with single_update have s_step: "s' = concrete.put (mem_nextblock m, hi_prev) (Undef, perm_freeable) s_prev"
      by (simp add: concrete.compose_defs(2))

    have concrete_prev: "concrete.get (mem_nextblock m, hi_prev) s_prev = (Undef, perm_none)"
      unfolding perm_none_def s_prev
      by (auto simp: concrete_get m[symmetric] mem_lens.laws)

    note create = assn_is_create[where ?c="s_prev" and ?F="(val_range (b, lo) (replicate len Undef) \<and>* F)",
        OF _ val_range_prev, simplified]

    show ?case
      apply (simp add: replicate_append_same[symmetric] val_range_step_end s_step hi_prev_lo_len b[symmetric])
      apply (rule create)
      by (simp add: concrete_prev hi_prev_lo_len[symmetric] b)
  qed

  note new_val_range = this

  note intro = wp_stateopI(6)[of _ _ s'' b]
  show ?case
    apply (rule intro)
    apply (metis m m''_alloc old.prod.case s''_alloc)
    apply (simp add: inv_s'')
    using new_val_range nextblock_indifferent s'(2)[symmetric]
    by simp
qed

lemma ht_free_inv[vcg_rules]:
  assumes "lo \<le> hi"
  defines "len \<equiv> nat (hi - lo)"
  assumes "length vs = len"
  shows "htriple
    (val_range (b, lo) vs)
    (op_free b lo hi)
    (\<lambda>_. \<box>)"
  apply (rule state_op.htriple_strengthen_inv[OF ht_free])
     apply (fact assms(1))
    apply (simp add: assms(3) len_def)
   apply simp
  unfolding op_free_def mem_lens.update_maybe_def
  apply (simp split: option.splits)
  by (metis Mem'.free_inv invariants_def mem_lens.get_put)
  

end

section \<open>State\<close>

datatype concrete_cminor_state = CMSTATE (env: env) (mem: mem)

type_synonym cminor_stmt = "func \<times> val \<times> stmt"
type_synonym cminor_expr = "val \<times> expr"

lemmas fold_state = concrete_cminor_state.collapse

type_synonym abstract_cminor_state = "(cminor_env \<times> cminor_mem)"
type_synonym cminor_assn = "abstract_cminor_state \<Rightarrow> bool"

definition cminor_\<alpha> :: "concrete_cminor_state \<Rightarrow> abstract_cminor_state" where
  "cminor_\<alpha> s = (env_access.\<alpha> (env s), mem_ptr_lens.\<alpha> (mem s))"

subsection \<open>Interpretations\<close>

subsubsection \<open>Mem\<close>

definition "concrete_mem_lens \<equiv> BLENS mem (\<lambda>m' s. CMSTATE (env s) m')"

interpretation concrete_mem_lens: basic_lens concrete_mem_lens
  unfolding concrete_mem_lens_def
  apply standard
  by auto

lemmas concrete_mem_lens_unfold = concrete_mem_lens.unfold[OF concrete_mem_lens_def]

definition abstract_mem_lens :: "(cminor_mem \<lhd> abstract_cminor_state)" where
  "abstract_mem_lens \<equiv> BLENS (\<lambda>(e,m). m) (\<lambda>m' (e,m). (e,m'))"

interpretation abstract_mem_lens: sep_algebra_lens abstract_mem_lens
  unfolding sep_algebra_lens_def
  apply safe
proof -
  show "basic_lens abstract_mem_lens"
    by unfold_locales (auto simp: abstract_mem_lens_def)

  then interpret basic: basic_lens abstract_mem_lens .

  show "sep_algebra_lens_axioms abstract_mem_lens"
    apply unfold_locales
    unfolding basic.defs
    unfolding abstract_mem_lens_def
    by (auto simp add: zero_prod_def fst_plus plus_prod_def sep_disj_prod_lower)
qed

interpretation mem_defs: mem_assns_defs concrete_mem_lens abstract_mem_lens
  by standard

interpretation mem: mem_assns cminor_\<alpha> concrete_mem_lens abstract_mem_lens
  apply standard
  unfolding cminor_\<alpha>_def abstract_mem_lens.ground_defs
  unfolding abstract_mem_lens_def
  unfolding concrete_mem_lens_unfold
  using mem_ptr_lens_nextblock_indifferent
  by auto

subsubsection \<open>Env\<close>

definition "concrete_env_lens \<equiv> BLENS env (\<lambda>e' s. CMSTATE e' (mem s))"

interpretation concrete_env_lens: basic_lens concrete_env_lens
  unfolding concrete_env_lens_def
  apply standard
  by auto

lemmas concrete_env_lens_unfold = concrete_env_lens.unfold[OF concrete_env_lens_def]

definition abstract_env_lens :: "(cminor_env \<lhd> abstract_cminor_state)" where
  "abstract_env_lens \<equiv> BLENS fst (\<lambda>e' (e,m). (e',m))"

interpretation abstract_env_lens: sep_algebra_lens abstract_env_lens
  unfolding sep_algebra_lens_def
  apply safe
proof -
  show "basic_lens abstract_env_lens"
    by unfold_locales (auto simp: abstract_env_lens_def)

  then interpret basic: basic_lens abstract_env_lens .

  show "sep_algebra_lens_axioms abstract_env_lens"
    apply unfold_locales
    unfolding basic.defs
    unfolding abstract_env_lens_def
    by (auto simp add: zero_prod_def fst_plus plus_prod_def sep_disj_prod_lower)
qed

interpretation env: env_assns cminor_\<alpha> concrete_env_lens abstract_env_lens mem.invariants
  apply standard
  unfolding cminor_\<alpha>_def abstract_env_lens.defs concrete_env_lens.defs
  unfolding abstract_env_lens_def concrete_env_lens_def
    apply auto
  unfolding mem.invariants_def Mem.mem_invariants_def concrete_mem_lens_unfold
  by auto

lemmas env_concrete_unfold = env.concrete.unfold

lemma env_concrete_is: "env.concrete.is ident v s \<longleftrightarrow> env s ident = v"
  unfolding env.concrete.compose_ground_defs
  unfolding env_access_def concrete_env_lens_def
  by simp

lemma env_concrete_put: "(env.concrete.put ident (Some v) s = s') \<longleftrightarrow> (mem s' = mem s \<and> env s' = env s(ident \<mapsto> v))"
  unfolding env.concrete.compose_ground_defs
  unfolding concrete_env_lens_def env_access_def
  apply simp
  by (metis concrete_cminor_state.exhaust_sel concrete_cminor_state.sel(1) concrete_cminor_state.sel(2))

section \<open>WP setup\<close>

subsection \<open>WP for expressions\<close>

interpretation expr: wp_from_inductive_determ "\<lambda>(ge, sp) a s v s'. eval_expr ge sp (env s) (mem s) a v \<and> s'=s"
  apply (unfold_locales)
  using eval_expr_determ by auto

thm expr.wp_determI

lemmas expr_wpI = expr.wp_determI[of "(ge, sp)" a "CMSTATE e m" v "CMSTATE e m", simplified] for ge sp a e m v e' m'
lemmas expr_wp_intros[intro] = eval_expr.intros[THEN expr_wpI, where ?e="env s" and ?m="mem s", simplified] for s

(* exprlists *)

interpretation exprlist: wp_from_inductive_determ "\<lambda>(ge, sp) as s vs s'. eval_exprlist ge sp (env s) (mem s) as vs \<and> s'=s"
  apply (unfold_locales)
  using eval_exprlist_determ by auto

lemmas exprlist_wpI = exprlist.wp_determI[of "(ge, sp)" as "CMSTATE e m" v "CMSTATE e m", simplified] for ge sp as e m v e' m'
lemmas exprlist_wp_intros[intro] = eval_exprlist.intros[THEN exprlist_wpI, where ?e="env s" and ?m="mem s", simplified] for s

subsection \<open>WP for external calls\<close>

interpretation extcall: wp_from_inductive "\<lambda>(ge, vargs) ef s (t, vres) s'. external_call ef (Genv.to_senv ge) vargs (mem s) t vres (mem s') \<and> (env s' = env s)"
  .

lemmas extcall_wpI = extcall.wpI[of "(ge, vargs)" ef "CMSTATE e m" "(t, vres)" "CMSTATE e m'", simplified] for ge vargs ef e m t vres m'
lemmas extcall_wp_intros[intro] =
  external_call_intros[THEN extcall_wpI, where ?e="env s" and ?m="mem s", simplified, simplified extcall_simps, simplified] for s

subsection \<open>WP for statements\<close>

interpretation stmt: wp_from_inductive "\<lambda>(ge, f, sp) st s (t, out) s'. exec_stmt ge f sp (env s) (mem s) st t (env s') (mem s') out"
  .

lemmas stmt_wpI = stmt.wpI[of "(ge, f, sp)" st "CMSTATE e m" "(t, out)" "CMSTATE e' m'", simplified] for ge f sp st e m t out e' m'
lemmas stmt_validI = stmt.validI[of "(ge, f, sp)" st "CMSTATE e m" "(t, out)" "CMSTATE e' m'", simplified] for ge f sp st e m t out e' m'

lemmas wp_intros = eval_funcall_exec_stmt.intros(3-)[THEN stmt_wpI, where ?e="env s'" and ?m="mem s'", simplified] for s'
lemmas valid_intros = eval_funcall_exec_stmt.intros(3-)[THEN stmt_validI, where ?e="env s'" and ?m="mem s'", simplified] for s'

subsection \<open>WP for functions\<close>

type_synonym cminor_func_call = "(func AST.fundef \<times> val list)"
type_synonym cminor_func_res = "(trace \<times> val)"

interpretation func: wp_from_inductive "\<lambda>(ge, vargs) f s (t, vres) s'. eval_funcall ge (mem s) f vargs t (mem s') vres \<and> (env s' = env s)"
  .

lemmas func_wpI = func.wpI[of "(ge, vargs)" f "CMSTATE e m" "(t, vres)" "CMSTATE e m'", simplified] for ge vargs f e m t vres m'
lemmas func_wp_intros[intro] =
  eval_funcall_exec_stmt.intros(1)[THEN func_wpI, where ?e="env s" and ?m="mem s", simplified, simplified eval_funcall_internal_simp] for s

thm eval_funcall_internal_simp

lemma wp_func_internal: (* TODO: turn into decomp rule *)
  assumes "\<exists>m1 sp e t e2 m2 out vres m3.
            (Mem.alloc (mem s) 0 (fn_stackspace f) = (m1, sp) \<and>
            set_locals (fn_vars f) (set_params vargs (fn_params f)) = e \<and>
            exec_stmt ge f (Vptr sp 0) e m1 (fn_body f) t e2 m2 out \<and>
            outcome_result_value out vres \<and>
            outcome_free_mem out m2 sp (fn_stackspace f) m3)"
          "\<And>m1 sp e t e2 m2 out vres m3.
            (Mem.alloc (mem s) 0 (fn_stackspace f) = (m1, sp) \<Longrightarrow>
            set_locals (fn_vars f) (set_params vargs (fn_params f)) = e \<Longrightarrow>
            exec_stmt ge f (Vptr sp 0) e m1 (fn_body f) t e2 m2 out \<Longrightarrow>
            outcome_result_value out vres \<Longrightarrow>
            outcome_free_mem out m2 sp (fn_stackspace f) m3) \<Longrightarrow>
            Q (t, vres) (CMSTATE (env s) m3)"
  shows "func.wp (ge, vargs) (Internal f) Q s"
  using assms
  apply (auto intro!: func_wp_intros)
  by (metis concrete_cminor_state.collapse)

(* lemma wp_func_internal:
  assumes "wp_stateop (mem.op_alloc 0 (fn_stackspace f) (
      \<lambda>sp. wp_stateop (op_set_params vargs (fn_params f)) (
       \<lambda>_. wp_stateop (op_set_locals (fn_vars f)) (
       \<lambda>_. stmt.wp (ge, f, sp) (fn_body f) (
\<lambda>(t, out). wp_stateop (Maybe (outcome_result_value_func out)) (
    \<lambda>vres. wp_stateop (UpdateMaybe (outcome_free_mem *)

section "WP-rules for expressions"

lemma wp_Econst[vcg_decomp_rules]:
  "wp_stateop (Maybe (eval_constant ge sp c)) Q s \<Longrightarrow> expr.wp (ge, sp) (Econst c) Q s"
  by (auto simp del: wp_stateop.simps)

lemma wp_Eunop[vcg_decomp_rules]:
  "expr.wp (ge, sp) a (\<lambda>v. wp_stateop (Maybe (eval_unop op v)) Q) s \<Longrightarrow>
    expr.wp (ge, sp) (Eunop op a) Q s"
  by (auto elim!: expr.wpE)

lemma wp_Ebinop[vcg_decomp_rules]:
  "expr.wp (ge, sp) (a1) (\<lambda>v1.
    expr.wp (ge, sp) (a2) (\<lambda>v2. 
      (wp_stateop (ReadMaybe (\<lambda>s. eval_binop op v1 v2 (mem s))) Q))) s \<Longrightarrow>
    expr.wp (ge, sp) (Ebinop op a1 a2) Q s"
  by (auto elim!: expr.wpE_concrete)

lemma wp_Eload[vcg_decomp_rules]:
  "expr.wp (ge, sp) (addr) (\<lambda>vaddr. wp_stateop (mem.op_loadv chunk vaddr) Q) s \<Longrightarrow>
    expr.wp (ge, sp) (Eload chunk addr) Q s"
  unfolding mem.op_loadv_def
  by (auto elim!: expr.wpE simp: concrete_mem_lens_unfold)

lemma wp_exprlist_nil[vcg_decomp_rules]:
  "Q [] s \<Longrightarrow> exprlist.wp (ge, sp) ([]) Q s"
  by (metis (mono_tags, lifting) exprlist_wp_intros(1))

lemma wp_exprlist_step[vcg_decomp_rules]:
  assumes "expr.wp (ge, sp) (a) (\<lambda>v. exprlist.wp (ge, sp) (as) (\<lambda>vs. Q (v # vs))) s"
  shows "exprlist.wp (ge, sp) (a # as) Q s"
  using assms
  by (smt (verit, best) expr.wp_determE exprlist.wp_determE exprlist_wp_intros(2) old.prod.case)

section \<open>WP-rules for external calls\<close>

lemma wp_extcall_malloc:
  assumes "wp_stateop (mem.op_alloc (- size_chunk Mptr) (Int64.unsigned sz))
          (\<lambda>b. wp_stateop (mem.op_store Mptr (b, - size_chunk Mptr) (Vptrofs sz)) (\<lambda>_. Q (E0, (Vptr b 0)))) s"
  shows "extcall.wp (ge, [Vptrofs sz]) EF_malloc Q s"
  using assms
  unfolding mem.op_alloc_def mem.op_store_def concrete_mem_lens_unfold
  apply (auto split: prod.splits option.splits intro!: extcall_wp_intros)
  by (metis concrete_cminor_state.collapse)

lemma wp_extcall_free:
  assumes "wp_stateop (mem.op_load Mptr (b, - size_chunk Mptr))
          (\<lambda>v s. case v of Vlong sz \<Rightarrow>
            sz > 0 \<and> wp_stateop (mem.op_free b (- size_chunk Mptr) (uint sz)) (\<lambda>_. Q (E0, Vundef)) s
           | _ \<Rightarrow> False) s"
  shows "extcall.wp (ge, [Vptr b 0]) EF_free Q s"
  using assms
  unfolding mem.op_load_def mem.op_free_def concrete_mem_lens_unfold
  apply (auto split: prod.splits option.splits val.splits intro!: extcall_wp_intros
          simp: Vptrofs_def Vnullptr_def word_less_def)
  by (metis concrete_cminor_state.collapse)

section \<open>WP-rules for statements\<close>

lemma wp_Sskip[vcg_decomp_rules]: "stmt.wp (ge, f, sp) (Sskip) Q s = Q (E0, Out_normal) s"
  by (smt (z3) case_prodE' concrete_cminor_state.expand exec_stmt_Sskip_simp old.prod.case stmt.wlp_def stmt.wp_def wp_intros(1))

lemma wp_Sassign[vcg_decomp_rules]:
  assumes "expr.wp (ge, sp) (a) (\<lambda>v. wp_stateop (env.op_concrete_put ident v) (\<lambda>_. Q (E0, Out_normal))) s"
  shows "stmt.wp (ge, f, sp) (Sassign ident a) Q s"
  using assms unfolding env.op_concrete_put_def
  apply (auto elim!: expr.wpE exec_stmt.cases intro!: wp_intros)
  by (metis env_concrete_put)

lemma wp_Sstore[vcg_decomp_rules]:
  assumes "expr.wp (ge, sp) (addr) (\<lambda>vaddr. 
            expr.wp (ge, sp) (a) (\<lambda>v.
              wp_stateop (mem.op_storev chunk vaddr v) (\<lambda>_. Q (E0, Out_normal))
            )
          )  s"
  shows "stmt.wp (ge, f, sp) (Sstore chunk addr a) Q s"
  using assms unfolding mem.op_storev_def concrete_mem_lens_unfold
  apply (rule expr.wpE)
  apply (erule expr.wpE)
  apply (erule wp_stateopE; simp)
proof (goal_cases)
  case (1 r ra f s')

  obtain m' where m': "Mem.storev chunk (mem s) r ra = Some m'"
    using "1"(3) "1"(4) by fastforce

  note intro = wp_intros(3)[OF
      \<open>eval_expr ge sp (env s) (mem s) addr r\<close>
      \<open>eval_expr ge sp (env s) (mem s) a ra\<close> m']

  show ?case
    apply (rule intro)
    apply safe
    by (metis "1"(1) "1"(4) concrete_cminor_state.exhaust_sel eval_expr_determ option.simps(5))
qed

inductive_cases exec_Sseq_cases: "exec_stmt ge f sp (env s) (mem s) (Sseq st1 st2) t (env s') (mem s') out"

lemma wp_Sseq[vcg_decomp_rules]:
  assumes "stmt.wp (ge, f, sp) (st1) (\<lambda>(t1, out1).
      if out1 = Out_normal
      then stmt.wp (ge, f, sp) (st2) (\<lambda>(t2, out2). Q (t1 @ t2, out2))
      else Q (t1, out1)) s"
  shows "stmt.wp (ge, f, sp) (Sseq st1 st2) Q s"
  apply (rule stmt.wp_to_wp[OF assms]; clarsimp)
proof (goal_cases)
  case (1 t out s')
  then show ?case
    apply (cases "out = Out_normal"; clarsimp)
     apply (erule stmt.wpE)
    apply simp
    using exec_Sseq_continue apply fastforce
    using exec_Sseq_stop by blast
next
  case (2 t' out' s'')

  show ?case
  proof (cases rule: exec_Sseq_cases[OF 2(2)])
    case (1 t1 e1 m1 t2)
    then obtain s1 where
      "exec_stmt ge f sp (env s) (mem s) st1 t1 (env s1) (mem s1) Out_normal"
      "exec_stmt ge f sp (env s1) (mem s1) st2 t2 (env s'') (mem s'') out'"
      by (metis concrete_cminor_state.sel(1) concrete_cminor_state.sel(2))
    with 1(1) 2 show ?thesis
      using stmt.wpD(2) by fastforce
  next
    case 2
    then show ?thesis
      using assms stmt.wpD(2) by fastforce
  qed
qed

lemma wp_Scall:
  assumes
    "expr.wp (ge, sp) (a)(
    \<lambda>vf. wp_stateop (Maybe (Genv.find_funct ge vf)) (
    \<lambda>fd s. funsig fd = sig \<and> exprlist.wp (ge, sp) (bl) (
    \<lambda>vargs. func.wp (ge, vargs) fd (
    \<lambda>(t, vres). wp_stateop (env.op_set_optvar optid vres) (\<lambda>_. Q (t, Out_normal)))) s)) s"
  shows "stmt.wp (ge, f, sp) (Scall optid sig a bl) Q s"
  using assms
  unfolding env.op_set_optvar_def
  unfolding concrete_env_lens_unfold
  apply (auto elim!: expr.wpE exprlist.wpE func.wpE)
  apply (rule wp_intros)
  apply (auto simp add: eval_expr_determ' eval_exprlist_determ')
  by (metis (no_types, hide_lams) concrete_cminor_state.exhaust_sel concrete_cminor_state.sel(1) concrete_cminor_state.sel(2))

lemma wp_Sbuiltin:
  assumes
    "exprlist.wp (ge, sp) (bl) (
    \<lambda>vargs. extcall.wp (ge, vargs) ef (
    \<lambda>(t, vres). wp_stateop (env.op_set_optvar optid vres) (
    \<lambda>_. Q (t, Out_normal)))) s"
  shows "stmt.wp (ge, f, sp) (Sbuiltin optid ef bl) Q s"
  using assms
  unfolding env.op_set_optvar_def
  apply (auto elim!: exprlist.wpE extcall.wpE simp: concrete_env_lens_unfold[abs_def] simp del: set_optvar.simps)
  apply (rule wp_intros)
     apply (auto simp: eval_exprlist_determ')
  by (metis (no_types, lifting) concrete_cminor_state.exhaust_sel concrete_cminor_state.sel(1) concrete_cminor_state.sel(2))


(* TODO: needs more work *)
(* lemma wp_Stailcall:
  assumes
    "wp_stateop (mem.op_free sp 0 (fn_stackspace f)) (
    \<lambda>_. expr.wp (ge, Vptr sp 0) a (
    \<lambda>vf. wp_stateop (Maybe (Genv.find_funct ge vf)) (
    \<lambda>fd s. funsig fd = sig \<and> exprlist.wp (ge, Vptr sp 0) bl (
    \<lambda>vargs. func.wp (ge, vargs) fd (\<lambda>(t, vres).
          Q (t, Out_tailcall_return vres)
    )) s))) s"
  shows "stmt.wp (ge, f, (Vptr sp 0)) (Stailcall sig a bl) Q s"
  using assms
  unfolding mem.op_free_def
  apply (auto elim!: expr.wpE exprlist.wpE func.wpE simp del: wp_stateop.simps)
  apply (rule wp_intros)
        apply (auto simp add: eval_expr_determ' eval_exprlist_determ' concrete_mem_lens.unfold[OF concrete_mem_lens_def])
  sorry *)

inductive_cases exec_Sifthenelse_cases: "exec_stmt ge f sp (env s) (mem s) (Sifthenelse a st1 st2) t e' m' out"

lemma wp_Sifthenelse:
  assumes "expr.wp (ge, sp) (a) (\<lambda>v _. Val.bool_of_val v True \<and> stmt.wp (ge, f, sp) (st1) Q s) s"
  assumes "expr.wp (ge, sp) (a) (\<lambda>v _. Val.bool_of_val v False \<and> stmt.wp (ge, f, sp) (st2) Q s) s"
  shows "stmt.wp (ge, f, sp) (Sifthenelse a st1 st2) Q s"
  apply (rule expr.wpE[OF assms(1)])
  apply (rule expr.wpE[OF assms(2)])
  apply (simp split: prod.splits add: eval_expr_determ')
proof (goal_cases)
  case (1 r)

  then obtain b where b: "Val.bool_of_val r b" "stmt.wp (ge, f, sp) (if b then st1 else st2) Q s"
    by (smt (verit, ccfv_threshold))

  note from_wp = stmt.wpD[OF b(2), simplified]

  show ?case
    apply (rule wp_intros)
       apply (fact 1(2))
      apply (fact b(1))
    using from_wp
    using "1"(3) "1"(1) bool_of_val_determ by blast+
qed

lemma wlp_Sloop:
  assumes init: "I (f, sp) (E0, Out_normal) s"
  assumes step: "\<And>f sp t out s. I (f, sp) (t, out) s \<Longrightarrow>
      if out = Out_normal
      then stmt.wlp (ge, f, sp) (st) (\<lambda>(t2, out2). I (f, sp) (t @ t2, out2)) s
      else Q (t, out) s"
  shows "stmt.wlp (ge, f, sp) (Sloop st) Q s"
  apply (rule stmt.wlpI)
proof (clarsimp; goal_cases)
  case (1 t out s')

  then have exec: "exec_stmt ge f sp (env s) (mem s) (Sloop st) t (env s') (mem s') out"
    using 1 by simp

  note induct = eval_funcall_exec_stmt.inducts(2)[where ?P1.0="top"]

  {
    fix t0
    assume init: "I (f, sp) (t0, Out_normal) s"
    have "Q (t0 @ t, out) s'" using exec init
    proof (induction f sp "env s" "mem s" "(Sloop st)" t "env s'" "mem s'" out arbitrary: t0 s s' rule: induct)
      case (eval_funcall_internal m f m1 sp vargs e t e2 m2 out vres m3)
      then show ?case by simp
    next
      case (eval_funcall_external ef args m t res m')
      then show ?case by simp
    next
      case (exec_Sloop_loop f sp t t1 e1 m1 t2 out s s' t0)

      note step[OF \<open>I (f, sp) (t0, Out_normal) s\<close>, simplified]
      note next_inv = stmt.wlpD[OF this, of "(t1, Out_normal)", simplified]

      show ?case
        using next_inv exec_Sloop_loop(1,4,5)
        by (metis append_assoc concrete_cminor_state.sel(1) concrete_cminor_state.sel(2))
    next
      case (exec_Sloop_stop f sp t out s s' t0)

      note step[OF \<open>I (f, sp) (t0, Out_normal) s\<close>, simplified]
      note next_inv = stmt.wlpD[OF this, of "(t, out)", simplified]

      show ?case
        using next_inv exec_Sloop_stop(1,2)
        by (meson exec_Sloop_stop.hyps(3) local.step)
    qed
  }

  then show ?case using init by fastforce
qed

lemma wp_Sloop: (* TODO: define whileI *)
  assumes wf: "wf R"
  assumes init: "I (f, sp) (E0, Out_normal) s"
  assumes step: "\<And>f sp t out s. I (f, sp) (t, out) s \<Longrightarrow>
      if out = Out_normal
      then stmt.wp (ge, f, sp) (st)
        (\<lambda>(t2, out2) s'. I (f, sp) (t @ t2, out2) s' \<and> (s',s) \<in> R) s
      else Q (t, out) s"
  shows "stmt.wp (ge, f, sp) (Sloop st) Q s"
  unfolding stmt.wp_def
proof(standard, goal_cases)
  case 1

  {
    fix t0
    assume init: "I (f, sp) (t0, Out_normal) s"

    have ?case
    using wf init
    proof (induction arbitrary: t0 rule: wf_induct_rule[where a=s])
      case (less s)

      note valid_Sloop_loop = valid_intros(9)
      note valid_Sloop_stop = valid_intros(10)

      note next_step = step[OF less(2), simplified]

      then show ?case
        apply (cases rule: stmt.wpE_concrete)
        apply clarsimp
      proof (goal_cases)
        case (1 t out s')

        show ?case
        proof (cases "out = Out_normal")
          case True

          with less(1) 1(2,3)
          have "stmt.valid (ge, f, sp) (Sloop st) s'" by simp
          then obtain t' e'' m'' out'
            where valid_loop: "exec_stmt ge f sp (env s') (mem s') (Sloop st) t' e'' m'' out'"
            by (auto elim!: stmt.validE)

          show ?thesis
            apply (rule valid_Sloop_loop)
            using 1(1,2) True apply simp
             apply (fact valid_loop)
            by simp
        next
          case False
          show ?thesis
            apply (rule valid_Sloop_stop)
            using 1(1) False by auto
        qed
      qed
    qed
  }

  then show ?case using init by simp
next
  case 2
  then show ?case
    using step[unfolded stmt.wp_def] wlp_Sloop
    by (smt case_prodI2' case_prod_conv init local.step stmt.wlpI stmt.wpE)
qed

lemma wp_Sblock[vcg_decomp_rules]:
  assumes "stmt.wp (ge, f, sp) (st) (\<lambda>(t, out) s'. Q (t, outcome_block out) s') s"
  shows "stmt.wp (ge, f, sp) (Sblock st) Q s"
  using assms
  by (auto intro!: wp_intros elim!: stmt.wpE elim: exec_stmt.cases)

lemma wp_Sexit: "Q (E0, Out_exit n) s \<Longrightarrow> stmt.wp (ge, f, sp) (Sexit n) Q s"
  using concrete_cminor_state.expand
  by (auto intro!: wp_intros elim!: exec_stmt.cases)

lemma wp_Sswitch:
  assumes "expr.wp (ge, sp) (a) (\<lambda>v s. \<exists>n. switch_argument islong v n \<and>
            Q (E0, Out_exit (switch_target n def cases)) s) s"
    shows "stmt.wp (ge, f, sp) (Sswitch islong a cases def) Q s"
  using assms
  apply (auto intro!: wp_intros elim!: expr.wpE exec_stmt.cases)
  using concrete_cminor_state.expand switch_argument_determ by blast

inductive_cases exec_Sreturn_cases: "exec_stmt ge f sp (env s) (mem s) (Sreturn (Some a)) t (env s') (mem s') out"

lemma wp_Sreturn_None[vcg_decomp_rules]:
  assumes "Q (E0, Out_return None) s"
  shows "stmt.wp (ge, f, sp) (Sreturn None) Q s"
  using assms
  apply (auto intro!: wp_intros elim!: exec_stmt.cases)
  by (metis concrete_cminor_state.expand)

lemma wp_Sreturn_Some[vcg_decomp_rules]:
  assumes "expr.wp (ge, sp) (a) (\<lambda>v. Q (E0, Out_return (Some v))) s"
  shows "stmt.wp (ge, f, sp) (Sreturn (Some a)) Q s"
proof (-)
  from assms have "expr.wp (ge, sp) (a) (\<lambda>v s. Q (E0, Out_return (Some v)) s) s" by simp
  then show ?thesis
    apply (auto elim!: expr.wpE exec_Sreturn_cases intro!: stmt.wpI)
    by (metis concrete_cminor_state.expand)
qed

section \<open>Expression hoare rules\<close>

context
  fixes ge :: genv
begin

abbreviation "expr_ht sp P c Qp \<equiv> expr.htriple (ge, sp) cminor_\<alpha> mem.invariants P c (\<lambda>r. \<up>(Qp r) ** P)"

notation expr_ht ("_ \<Turnstile>\<^sub>e")

lemma ht_Evar[vcg_rules]:
  shows "sp \<Turnstile>\<^sub>e
        (env.assn_is ident v)
        (Evar ident)
        (\<lambda>r. r = v)"
  apply (rule expr.htripleI)
  apply (rule expr_wp_intros)
   apply (simp add: env.assn_is_concrete env_concrete_is)
  by (simp add: pred_lift_extract_simps(2))

section \<open>Stmt hoare rules\<close>

abbreviation silent_op :: "cminor_assn \<Rightarrow> (trace \<times> outcome \<Rightarrow> cminor_assn)" where
  "silent_op P \<equiv> \<lambda>(t, out). \<up>(t = E0 \<and> out = Out_normal) ** P"

abbreviation "stmt_ht_weak f sp \<equiv> stmt.htriple (ge, f, sp) cminor_\<alpha> I\<^sub>0"
abbreviation "stmt_ht f sp \<equiv> stmt.htriple (ge, f, sp) cminor_\<alpha> mem.invariants"
abbreviation "stmt_htF f sp \<equiv> stmt.htripleF (ge, f, sp) cminor_\<alpha> mem.invariants"

lemma ht_Sassign[vcg_rules]:
  assumes [vcg_rules]:
    "expr_ht sp (env.assn_is i v ** F) e (\<lambda>r. r = v')"
  shows "stmt_htF f sp
      F (env.assn_is i v)
      (Sassign i e)
      (silent_op (env.assn_is i v'))"
  by vcg

lemma ht_Sassign':
  shows "stmt_ht f sp
      (env.assn_is i v)
      (Sassign i (Econst (Ointconst 42)))
      (silent_op (env.assn_is i (Vint 42)))"
  by vcg

lemma ht_Sstore[vcg_rules]:
  fixes b ofs
  defines [simp]: "p \<equiv> (b, uint ofs)"
  assumes fit: "mem.chunk_fit chunk v'"
  assumes expr_addr[vcg_rules]:
    "expr_ht sp (mem.mem_chunk chunk p vs ** P) expr_addr (\<lambda>r. r = (Vptr b ofs))"
  assumes expr_v[vcg_rules]:
    "expr_ht sp (mem.mem_chunk chunk p vs ** P) expr_v (\<lambda>r. r = v')"
  shows "stmt_ht f sp
      (mem.mem_chunk chunk p vs ** P)
      (Sstore chunk expr_addr expr_v)
      (silent_op (mem.mem_val_fit chunk p v' ** P))"
  using fit by vcg

lemma ht_Sstore':
  fixes b ofs
  defines [simp]: "p \<equiv> (b, uint ofs)"
  defines [simp]: "chunk \<equiv> Mint32"
  shows "stmt_ht f (Vptr b ofs)
      (mem.mem_chunk chunk p vs)
      (Sstore chunk (Econst (Oaddrstack 0)) (Econst (Ointconst 42)))
      (silent_op (mem.mem_val_fit chunk p (Vint 42)))"
  using mem.chunk_fit.intros
  by vcg

lemma ht_malloc[vcg_rules]:
  notes [simp] = Vptrofs_def Mptr_def
  notes wp_extcall_malloc[simplified, vcg_decomp_rules]
  notes wp_Sbuiltin[vcg_decomp_rules]
  shows "stmt_ht f sp
      (env.assn_is env_b b')
      (Sbuiltin (Some env_b) (EF_malloc) [Econst (Olongconst sz)])
      (silent_op (EXS b. env.assn_is env_b (Vptr b 0)
               ** mem.mem_val_fit Mptr (b, - size_chunk Mptr) (Vptrofs sz)
               \<and>* mem.val_range (b, 0) (replicate (nat (Int64.unsigned sz)) Undef)))"
proof -
  have split_okay: "8 \<le> length (replicate (nat (Int64.unsigned sz + 8)) Undef)"
    apply (simp)
    by (metis Word.of_nat_unat le_add2 nat_int_add of_nat_numeral)

  note split' = mem.val_range_split[OF this, simplified]

  have sep_sep: "\<And>P P' Q Q'. P = P' \<Longrightarrow> Q = Q' \<Longrightarrow> (P ** Q) = (P' ** Q')"
    by simp

  have split:
    "\<And>r. mem.val_range (r, - 8)
          (replicate (nat (Int64.unsigned sz + 8)) Undef)
       = (mem.mem_chunk Mint64 (r, - 8) (replicate (size_chunk_nat Mint64) Undef)
      **  mem.val_range (r, 0) (replicate (nat (Int64.unsigned sz)) Undef))"
    unfolding mem.mem_chunk_def
    apply (simp add: split')
    apply (simp add: sep_algebra_simps)
    apply (rule sep_sep)
    using split_okay apply force
    using nat_add_distrib by auto

  note [vcg_rules del] = mem.ht_store_inv

  show ?thesis
    apply vcg
    apply (subst (asm) split)
    supply [vcg_rules] = mem.ht_store_inv
    apply vcg
       apply (auto simp add: mem.chunk_fit.intros(5))
    by vcg
qed

lemma ht_free[vcg_rules]:
  notes mem.wp_load[vcg_decomp_rules]
  notes wp_extcall_free[vcg_decomp_rules]
  notes wp_Sbuiltin[vcg_decomp_rules]
  assumes [iff]: "0 < sz"
  assumes [simp]: "length vs = unat sz"
  shows "stmt_ht f sp
      (env.assn_is env_b (Vptr b 0)
       ** mem.mem_val Mptr (b, - size_chunk Mptr) (Vptrofs sz)
       \<and>* mem.val_range (b, 0) vs)
      (Sbuiltin None (EF_free) [Evar env_b])
      (silent_op (EXS v. env.assn_is env_b v))"
proof -

  have [simp]: "Mptr = Mint64" "Vptrofs = Vlong"
    unfolding Mptr_def Vptrofs_def by auto

  have merge:
    "\<And>F.(mem.mem_val Mint64 (b, - 8) (Vlong sz)
      \<and>* mem.val_range (b, 0) vs \<and>* F \<and>* env.assn_is env_b (Vptr b 0))
      = (mem.val_range (b, - 8) (encode_val Mint64 (Vlong sz) @ vs)
      \<and>* F \<and>* env.assn_is env_b (Vptr b 0))"
    unfolding Vptrofs_def Mptr_def mem.mem_chunk_def
    apply (simp add: mem.val_range_split_concat)
    by (simp add: mem.chunk_fit.simps sep_algebra_simps)

  show ?thesis
    apply vcg
    apply (subst (asm) merge)
    apply vcg
    apply (auto simp: Int.nat_add_distrib sep_algebra_simps)
    by vcg
qed

end

end