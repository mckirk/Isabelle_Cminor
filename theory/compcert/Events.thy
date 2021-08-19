theory Events
  imports
Main
Integers
Floats
AST
Globalenvs
begin

section \<open>Events and traces\<close>

(** The observable behaviour of programs is stated in terms of
  input/output events, which represent the actions of the program
  that the external world can observe.  CompCert leaves much flexibility as to
  the exact content of events: the only requirement is that they
  do not expose memory states nor pointer values
  (other than pointers to global variables), because these
  are not preserved literally during compilation.  For concreteness,
  we use the following type for events.  Each event represents either:

- A system call (e.g. an input/output operation), recording the
  name of the system call, its parameters, and its result.

- A volatile load from a global memory location, recording the chunk
  and address being read and the value just read.

- A volatile store to a global memory location, recording the chunk
  and address being written and the value stored there.

- An annotation, recording the text of the annotation and the values
  of the arguments.

  The values attached to these events are of the following form.
  As mentioned above, we do not expose pointer values directly.
  Pointers relative to a global variable are shown with the name
  of the variable instead of the block identifier.
*)

datatype eventval =
  EVint m_int
| EVlong m_int64
| EVfloat float64
| EVsingle float32
| EVptr_global AST.ident m_ptrofs

datatype event =
  Event_syscall string "eventval list" eventval
| Event_vload memory_chunk AST.ident m_ptrofs eventval
| Event_vstore memory_chunk AST.ident m_ptrofs eventval
| Event_annot string "eventval list"

(** The dynamic semantics for programs collect traces of events.
  Traces are of two kinds: finite (type [trace]) or infinite (type [traceinf]). *)

type_synonym trace = "event list"
abbreviation E0 :: trace where "E0 \<equiv> []"

codatatype traceinf = Econsinf event traceinf

fun Eappinf :: "trace \<Rightarrow> traceinf \<Rightarrow> traceinf" where
  "Eappinf [] T = T"
| "Eappinf (ev # evs) T = Econsinf ev (Eappinf evs T)"

section \<open>Relating values and event values\<close>

context
  fixes ge :: Senv_t
begin

(** Validity *)

fun eventval_valid :: "eventval \<Rightarrow> bool" where
  "eventval_valid (EVint _) = True"
| "eventval_valid (EVlong _) = True"
| "eventval_valid (EVfloat _) = True"
| "eventval_valid (EVsingle _) = True"
| "eventval_valid (EVptr_global ident ofs) = (Senv.public_symbol ge ident = True)"

fun eventval_type :: "eventval \<Rightarrow> type" where
  "eventval_type (EVint _) = Tint"
| "eventval_type (EVlong _) = Tlong"
| "eventval_type (EVfloat _) = Tfloat"
| "eventval_type (EVsingle _) = Tsingle"
| "eventval_type (EVptr_global ident ofs) = Tptr"

end

(** Compatibility with memory injections *)

definition symbols_inject :: "(block \<Rightarrow> (block * Z) option) \<Rightarrow> Senv_t \<Rightarrow> Senv_t \<Rightarrow> bool" where
  "symbols_inject f ge1 ge2 \<equiv>
    (\<forall> ident. Senv.public_symbol ge2 ident = Senv.public_symbol ge1 ident)
  \<and> (\<forall> ident b1 b2 delta.
       f b1 = Some(b2, delta) \<longrightarrow> Senv.find_symbol ge1 ident = Some b1 \<longrightarrow>
       delta = 0 \<and> Senv.find_symbol ge2 ident = Some b2)
  \<and> (\<forall> ident b1.
       Senv.public_symbol ge1 ident = True \<longrightarrow> Senv.find_symbol ge1 ident = Some b1 \<longrightarrow>
       (\<exists> b2. f b1 = Some(b2, 0) \<and> Senv.find_symbol ge2 ident = Some b2))
  \<and> (\<forall> b1 b2 delta.
       f b1 = Some(b2, delta) \<longrightarrow>
       Senv.block_is_volatile ge2 b2 = Senv.block_is_volatile ge1 b1)"

section \<open>Matching traces\<close>

context
  fixes ge :: Senv_t
begin

(** Matching between traces corresponding to single transitions.
  Arguments (provided by the program) must be equal.
  Results (provided by the outside world) can vary as long as they
  can be converted safely to values. *)

inductive match_traces :: "trace \<Rightarrow> trace \<Rightarrow> bool" where
    match_traces_E0:
      "match_traces [] []"
  | match_traces_syscall:
      "eventval_valid ge res1 \<Longrightarrow> eventval_valid ge res2 \<Longrightarrow> eventval_type res1 = eventval_type res2 \<Longrightarrow>
      match_traces (Event_syscall ident args res1 # []) (Event_syscall ident args res2 # [])"
  | match_traces_vload:
      "eventval_valid ge res1 \<Longrightarrow> eventval_valid ge res2 \<Longrightarrow> eventval_type res1 = eventval_type res2 \<Longrightarrow>
      match_traces (Event_vload chunk ident ofs res1 # []) (Event_vload chunk ident ofs res2 # [])"
  | match_traces_vstore:
      "match_traces (Event_vstore chunk ident ofs a # []) (Event_vstore chunk ident ofs a # [])"
  | match_traces_annot:
      "match_traces (Event_annot ident args # []) (Event_annot ident args # [])"

end

section \<open>Semantics of external functions\<close>

(** For each external function, its behavior is defined by a predicate relating:
- the global symbol environment
- the values of the arguments passed to this function
- the memory state before the call
- the result value of the call
- the memory state after the call
- the trace generated by the call (can be empty).
*)

type_synonym extcall_sem = "Senv_t \<Rightarrow> val list \<Rightarrow> mem \<Rightarrow> trace \<Rightarrow> val \<Rightarrow> mem \<Rightarrow> bool"

(** We now specify the expected properties of this predicate. *)

definition loc_out_of_bounds :: "mem \<Rightarrow> block \<Rightarrow> Z \<Rightarrow> bool" where
  "loc_out_of_bounds m b ofs \<equiv> ~Mem.perm m b ofs Max Nonempty"

definition loc_not_writable :: "mem \<Rightarrow> block \<Rightarrow> Z \<Rightarrow> bool" where
  "loc_not_writable m b ofs \<equiv> ~Mem.perm m b ofs Max Writable"

definition loc_unmapped :: "meminj \<Rightarrow> block \<Rightarrow> Z \<Rightarrow> bool" where
  "loc_unmapped f b ofs \<equiv> f b = None"

definition loc_out_of_reach :: "meminj \<Rightarrow> mem \<Rightarrow> block \<Rightarrow> Z \<Rightarrow> bool" where
  "loc_out_of_reach f m b ofs \<equiv>
    \<forall> b0 delta.
    f b0 = Some(b, delta) \<longrightarrow> ~Mem.perm m b0 (ofs - delta) Max Nonempty"

definition inject_separated :: "meminj \<Rightarrow> meminj \<Rightarrow> mem \<Rightarrow> mem \<Rightarrow> bool" where
  "inject_separated f f' m1 m2 \<equiv>
    \<forall> b1 b2 delta.
    f b1 = None \<longrightarrow> f' b1 = Some(b2, delta) \<longrightarrow>
    ~Mem.valid_block m1 b1 \<and> ~Mem.valid_block m2 b2"

context
  fixes sem :: extcall_sem
  fixes sg :: signature
begin

named_theorems extcall_properties_defs'

(** The return value of an external call must agree with its signature. *)
definition [extcall_properties_defs']: "ec_well_typed \<equiv>
  (\<forall> ge vargs m1 t vres m2.
    sem ge vargs m1 t vres m2 \<longrightarrow>
    Val.has_rettype vres (sig_res sg))"

(** The semantics is invariant under change of global environment that preserves symbols. *)
definition [extcall_properties_defs']: "ec_symbols_preserved \<equiv>
  (\<forall> ge1 ge2 vargs m1 t vres m2.
    Senv.equiv ge1 ge2 \<longrightarrow>
    sem ge1 vargs m1 t vres m2 \<longrightarrow>
    sem ge2 vargs m1 t vres m2)"

(** External calls cannot invalidate memory blocks.  (Remember that
  freeing a block does not invalidate its block identifier.) *)
definition [extcall_properties_defs']: "ec_valid_block \<equiv>
  (\<forall> ge vargs m1 t vres m2 b.
    sem ge vargs m1 t vres m2 \<longrightarrow>
    Mem.valid_block m1 b \<longrightarrow> Mem.valid_block m2 b)"

(** External calls cannot increase the max permissions of a valid block.
    They can decrease the max permissions, e.g. by freeing. *)
definition [extcall_properties_defs']: "ec_max_perm \<equiv>
  (\<forall> ge vargs m1 t vres m2 b ofs p.
    sem ge vargs m1 t vres m2 \<longrightarrow>
    Mem.valid_block m1 b \<longrightarrow> Mem.perm m2 b ofs Max p \<longrightarrow> Mem.perm m1 b ofs Max p)"

(** External call cannot modify memory unless they have [Max, Writable]
   permissions. *)
definition [extcall_properties_defs']: "ec_readonly \<equiv>
  (\<forall> ge vargs m1 t vres m2 b ofs n bytes.
    sem ge vargs m1 t vres m2 \<longrightarrow>
    Mem.valid_block m1 b \<longrightarrow>
    Mem.loadbytes m2 b ofs n = Some bytes \<longrightarrow>
    (\<forall> i ofs. ofs <= i \<and> i < ofs + n \<longrightarrow> ~Mem.perm m1 b i Max Writable) \<longrightarrow>
    Mem.loadbytes m1 b ofs n = Some bytes)"

(** External calls must commute with memory extensions, in the
  following sense. *)
definition [extcall_properties_defs']: "ec_mem_extends \<equiv>
  (\<forall> ge vargs m1 t vres m2 m1' vargs'.
    sem ge vargs m1 t vres m2 \<longrightarrow>
    Mem.extends m1 m1' \<longrightarrow>
    Val.lessdef_list vargs vargs' \<longrightarrow>
    (\<exists> vres'. \<exists> m2'.
       sem ge vargs' m1' t vres' m2'
    \<and> Val.lessdef vres vres'
    \<and> Mem.extends m2 m2'
    \<and> Mem.unchanged_on (loc_out_of_bounds m1) m1' m2'))"

(** External calls must commute with memory injections,
  in the following sense. *)
definition [extcall_properties_defs']: "ec_mem_inject \<equiv>
  (\<forall> ge1 ge2 vargs m1 t vres m2 f m1' vargs'.
    symbols_inject f ge1 ge2 \<longrightarrow>
    sem ge1 vargs m1 t vres m2 \<longrightarrow>
    Mem.inject f m1 m1' \<longrightarrow>
    Val.inject_list f vargs vargs' \<longrightarrow>
    (\<exists> f' vres' m2'.
       sem ge2 vargs' m1' t vres' m2'
    \<and> Val.inject f' vres vres'
    \<and> Mem.inject f' m2 m2'
    \<and> Mem.unchanged_on (loc_unmapped f) m1 m2
    \<and> Mem.unchanged_on (loc_out_of_reach f m1) m1' m2'
    \<and> inject_incr f f'
    \<and> inject_separated f f' m1 m1'))"

(** External calls produce at most one event. *)
definition [extcall_properties_defs']: "ec_trace_length \<equiv>
  (\<forall> ge vargs m t vres m'.
    sem ge vargs m t vres m' \<longrightarrow> (length t \<le> 1))"

(** External calls must be receptive to changes of traces by another, matching trace. *)
definition [extcall_properties_defs']: "ec_receptive \<equiv>
  (\<forall> ge vargs m t1 vres1 m1 t2.
    sem ge vargs m t1 vres1 m1 \<longrightarrow> match_traces ge t1 t2 \<longrightarrow>
    (\<exists> vres2. \<exists> m2. sem ge vargs m t2 vres2 m2))"

(** External calls must be deterministic up to matching between traces. *)
definition [extcall_properties_defs']: "ec_determ \<equiv>
  (\<forall> ge vargs m t1 vres1 m1 t2 vres2 m2.
    sem ge vargs m t1 vres1 m1 \<longrightarrow> sem ge vargs m t2 vres2 m2 \<longrightarrow>
    match_traces ge t1 t2 \<and> (t1 = t2 \<longrightarrow> vres1 = vres2 \<and> m1 = m2))"

inductive extcall_properties where
  "\<lbrakk> ec_well_typed;
    ec_symbols_preserved;
    ec_valid_block;
    ec_max_perm;
    ec_readonly;
    ec_mem_extends;
    ec_mem_inject;
    ec_trace_length;
    ec_receptive;
    ec_determ \<rbrakk> \<Longrightarrow>
  extcall_properties"

lemmas extcall_properties_def = extcall_properties_defs' extcall_properties.simps[simplified]
end

subsection \<open>Semantics of dynamic memory allocation (malloc)\<close>

inductive extcall_malloc_sem :: "Senv_t \<Rightarrow> val list \<Rightarrow> mem \<Rightarrow> trace \<Rightarrow> val \<Rightarrow> mem \<Rightarrow> bool" where
    extcall_malloc_sem_intro:
      "Mem.alloc m (- size_chunk Mptr) (Int64.unsigned sz) = (m', b) \<Longrightarrow>
      Mem.store Mptr m' b (- size_chunk Mptr) (Vptrofs sz) = Some m'' \<Longrightarrow>
      extcall_malloc_sem ge [Vptrofs sz] m E0 (Vptr b 0) m''"

lemma extcall_malloc_unchanged_on:
  assumes "Mem.mem_invariants m"
  assumes "extcall_malloc_sem ge vargs m t vres m''"
  shows "extcall_malloc_sem ge vargs m t vres m'' \<and> Mem.unchanged_on P m m''"
  apply (simp add: assms(2))
  using assms(2)
proof (cases rule: extcall_malloc_sem.cases)
  case (extcall_malloc_sem_intro sz m' b)

  from \<open>Mem.alloc m (- size_chunk Mptr) (Int64.unsigned sz) = (m', b)\<close>
  have b'b: "\<And>b'. Mem.valid_block m b' \<Longrightarrow> b' \<noteq> b"
    using Mem.alloc_valid_block(2) by auto

  have unchanged1: "Mem.unchanged_on P m m'"
    using Mem.alloc_unchanged_on assms(1) local.extcall_malloc_sem_intro(4) by auto

  from \<open>Mem.store Mptr m' b (- size_chunk Mptr) (Vptrofs sz) = Some m''\<close>
  have unchanged2: "Mem.unchanged_on (\<lambda>b ofs. P b ofs \<and> Mem.valid_block m b) m' m''"
    apply (rule Mem.store_unchanged_on)
    using b'b by simp

  note rule = Mem.unchanged_on_trans[OF assms(1), OF unchanged1 unchanged2]

  then show "Mem.unchanged_on P m m''"
    by simp
qed

lemma extcall_malloc_ok:
  "extcall_properties extcall_malloc_sem
                     (mksignature (Tptr # []) (Tret Tptr) cc_default)"
  unfolding extcall_properties_def
  apply (safe elim!: extcall_malloc_sem.cases intro: extcall_malloc_sem_intro)
proof (goal_cases)
  case (1 ge vargs m1 t vres m2 m sz m' b m'' gea)
  then show ?case
    by (simp add: signature.defs)
next
  case (2 ge1 ge2 vargs m1 t vres m2 m sz m' b m'' ge)
  then show ?case
    using "2"(2) "2"(3) extcall_malloc_sem_intro by blast
next
  case (3 ge vargs m1 t vres m2 b m sz m' ba m'' gea)

  then show ?case
    by (meson Mem'.alloc_valid_block(1) Mem'.store_valid_block)
next
  case (4 ge vargs m1 t vres m2 b ofs p m sz m' ba m'' gea)

  then show ?case
    by (meson Mem.alloc_max_perm Mem.store_max_perm)
next
  case (5 ge vargs m1 t vres m2 b ofs n bytes m sz m' ba m'' gea)
  then show ?case sorry
next
  case (6 ge vargs m1 t vres m2 m1' vargs' m sz m' b m'' gea)
  then show ?case sorry
next
  case (7 ge1 ge2 vargs m1 t vres m2 f m1' vargs' m sz m' b m'' ge)
  then show ?case sorry
next
  case (8 ge vargs m t vres m' ma sz m'a b m'' gea)
then show ?case sorry
next
  case (9 ge vargs m t1 vres1 m1 t2 ma sz m' b m'' gea)
  then show ?case sorry
next
  case (10 ge vargs m t1 vres1 m1 t2 vres2 m2 ma sz m' b m'' gea mb sza m'a ba m''a geb)
  then show ?case sorry
next
  case (11 ge vargs m t1 vres1 m1 t2 vres2 m2 ma sz m' b m'' gea mb sza m'a ba m''a geb)
  then show ?case sorry
next
  case (12 ge vargs m t1 vres1 m1 t2 vres2 m2 ma sz m' b m'' gea mb sza m'a ba m''a geb)
  then show ?case sorry
qed

subsection \<open>Semantics of dynamic memory deallocation (free)\<close>

inductive extcall_free_sem :: "Senv_t \<Rightarrow> val list \<Rightarrow> mem \<Rightarrow> trace \<Rightarrow> val \<Rightarrow> mem \<Rightarrow> bool" where
    extcall_free_sem_ptr:
      "Mem.load Mptr m b (Int64.unsigned lo - size_chunk Mptr) = Some (Vptrofs sz) \<Longrightarrow>
      Int64.unsigned sz > 0 \<Longrightarrow>
      Mem.free m b (Int64.unsigned lo - size_chunk Mptr) (Int64.unsigned lo + Int64.unsigned sz) = Some m' \<Longrightarrow>
      extcall_free_sem ge (Vptr b lo # []) m E0 Vundef m'"
  | extcall_free_sem_null:
      "extcall_free_sem ge (Vnullptr # []) m E0 Vundef m"

lemma extcall_free_ok:
  "extcall_properties extcall_free_sem
                     (mksignature (Tptr # []) (Tvoid) cc_default)"
  sorry

subsection \<open>Semantics of [memcpy] operations\<close>

inductive extcall_memcpy_sem :: "Z \<Rightarrow> Z \<Rightarrow> Senv_t \<Rightarrow> val list \<Rightarrow> mem \<Rightarrow> trace \<Rightarrow> val \<Rightarrow> mem \<Rightarrow> bool" where
    extcall_memcpy_sem_intro:
      "al = 1 \<or> al = 2 \<or> al = 4 \<or> al = 8 \<Longrightarrow> sz \<ge> 0 \<Longrightarrow> (al dvd sz) \<Longrightarrow>
      (sz > 0 \<Longrightarrow> (al dvd Int64.unsigned osrc)) \<Longrightarrow>
      (sz > 0 \<Longrightarrow> (al dvd Int64.unsigned odst)) \<Longrightarrow>
      bsrc \<noteq> bdst \<or> Int64.unsigned osrc = Int64.unsigned odst
                   \<or> Int64.unsigned osrc + sz <= Int64.unsigned odst
                   \<or> Int64.unsigned odst + sz <= Int64.unsigned osrc \<Longrightarrow>
      Mem.loadbytes m bsrc (Int64.unsigned osrc) sz = Some bytes \<Longrightarrow>
      Mem.storebytes m bdst (Int64.unsigned odst) bytes = Some m' \<Longrightarrow>
      extcall_memcpy_sem sz al ge (Vptr bdst odst # Vptr bsrc osrc # []) m E0 Vundef m'"

lemma extcall_memcpy_ok:
  "extcall_properties (extcall_memcpy_sem sz al)
                     (mksignature (Tptr # Tptr # []) (Tvoid) cc_default)"
  sorry

(** Combining the semantics given above for the various kinds of external calls,
  we define the predicate [external_call] that relates:
- the external function being invoked
- the values of the arguments passed to this function
- the memory state before the call
- the result value of the call
- the memory state after the call
- the trace generated by the call (can be empty).

This predicate is used in the semantics of all CompCert languages. *)

inductive extcall_dummy_sem :: "extcall_sem" where
    extcall_dummy_sem_intro: "extcall_dummy_sem ge args m E0 sp m"

fun external_call :: "external_function \<Rightarrow> extcall_sem" where
(* TODO: not implemented for now
  "external_call (EF_external name sg) = external_functions_sem name sg"
| "external_call (EF_builtin name sg) = builtin_or_external_sem name sg"
| "external_call (EF_runtime name sg) = builtin_or_external_sem name sg"
| "external_call (EF_vload chunk) = volatile_load_sem chunk"
| "external_call (EF_vstore chunk) = volatile_store_sem chunk" *)
  "external_call EF_malloc = extcall_malloc_sem"
| "external_call EF_free = extcall_free_sem"
| "external_call (EF_memcpy sz al) = extcall_memcpy_sem sz al"
(* TODO: not implemented for now
| "external_call (EF_annot kind txt targs) = extcall_annot_sem txt targs"
| "external_call (EF_annot_val kind txt targ) = extcall_annot_val_sem txt targ"
| "external_call (EF_inline_asm txt sg clb) = inline_assembly_sem txt sg"
| "external_call (EF_debug kind txt targs) = extcall_debug_sem" *)

lemmas extcall_simps =
  extcall_malloc_sem.simps extcall_free_sem.simps extcall_memcpy_sem.simps
lemmas extcall_intros =
  extcall_malloc_sem.intros extcall_free_sem.intros extcall_memcpy_sem.intros

lemmas external_call_intros = extcall_intros[folded external_call.simps]

lemma external_call_spec:
  "extcall_properties (external_call ef) (ef_sig ef)"
  apply (cases ef)
  using extcall_malloc_ok extcall_free_ok extcall_memcpy_ok
  by auto

definition "external_call_well_typed_gen ef \<equiv> ec_well_typed (external_call ef) (ef_sig ef)"
definition "external_call_symbols_preserved ef \<equiv> ec_symbols_preserved (external_call ef)"
definition "external_call_valid_block ef \<equiv> ec_valid_block (external_call ef)"
definition "external_call_max_perm ef \<equiv> ec_max_perm (external_call ef)"
definition "external_call_readonly ef \<equiv> ec_readonly (external_call ef)"
definition "external_call_mem_extends ef \<equiv> ec_mem_extends (external_call ef)"
definition "external_call_mem_inject_gen ef \<equiv> ec_mem_inject (external_call ef)"
definition "external_call_trace_length ef \<equiv> ec_trace_length (external_call ef)"
definition "external_call_receptive ef \<equiv> ec_receptive (external_call ef)"
definition "external_call_determ ef \<equiv> ec_determ (external_call ef)"

(** Corollaries of [external_call_determ]. *)

lemma external_call_match_traces:
  assumes "external_call ef ge vargs m t1 vres1 m1"
  assumes "external_call ef ge vargs m t2 vres2 m2"
  shows "match_traces ge t1 t2"
proof -
  have "external_call_determ ef"
    unfolding external_call_determ_def
    using extcall_properties.cases external_call_spec by auto

  then show ?thesis
    unfolding external_call_determ_def ec_determ_def
    using assms by simp
qed

lemma external_call_deterministic:
  assumes "external_call ef ge vargs m t vres1 m1"
  assumes "external_call ef ge vargs m t vres2 m2"
  shows "vres1 = vres2 \<and> m1 = m2"
proof -
  have "external_call_determ ef"
    unfolding external_call_determ_def
    using extcall_properties.cases external_call_spec by auto

  then show ?thesis
    unfolding external_call_determ_def ec_determ_def
    using assms by simp
qed

section \<open>Additions\<close>

(* modeling results of deterministic external_calls *)
definition external_call_result :: "external_function \<Rightarrow> Senv_t \<Rightarrow> val list \<Rightarrow> mem \<Rightarrow> (event list \<times> val \<times> mem) option" where
  "external_call_result ef ge vargs m \<equiv>
    if \<exists>t vres m'. external_call ef ge vargs m t vres m'
    then Some (THE (t, vres, m'). external_call ef ge vargs m t vres m')
    else None"

declare external_call_result_def[code del]

lemma external_call_resultI:
  assumes "\<And>t vres m'. external_call ef ge vargs m t vres m' \<Longrightarrow> res_fun ge vargs m = Some (t, vres, m')"
  assumes "(\<And>t vres m'. \<not>external_call ef ge vargs m t vres m') \<Longrightarrow> res_fun ge vargs m = None"
  shows "external_call_result ef ge vargs m = res_fun ge vargs m"
  unfolding external_call_result_def
  apply (split if_splits)
  by (smt (z3) Collect_cong The_split_eq assms(1) assms(2) case_prodE case_prodI in_rel_Collect_case_prod_eq option.inject)

print_statement extcall_malloc_sem.simps[simplified]

lemma extcall_malloc_result:
  notes align_Mptr = align_dvd_size_mult[of Mptr "-1"]
  notes store_valid = Mem.store_after_alloc[OF _ _ _ align_Mptr]
  shows
    "external_call_result EF_malloc ge [Vptrofs sz] m =
      (case Mem.alloc m (- size_chunk Mptr) (Int64.unsigned sz) of (m', b) \<Rightarrow>
      (case Mem.store Mptr m' b (- size_chunk Mptr) (Vptrofs sz) of Some m'' \<Rightarrow>
      Some (E0, Vptr b 0, m'') | _ \<Rightarrow> None))"
  apply (rule external_call_resultI; split prod.splits; split option.splits)
   apply (simp)
   apply (erule extcall_malloc_sem.cases)
  unfolding Vptrofs_def
   apply force
  using Vptrofs_def extcall_malloc_sem_intro by fastforce

print_statement extcall_free_sem.simps[simplified]

lemma extcall_free_result:
  shows
    "external_call_result EF_free ge vargs m =
      (if vargs = [Vnullptr] then Some (E0, Vundef, m) else
      (case vargs of [Vptr b lo] \<Rightarrow>
      (case Mem.load Mptr m b (Int64.unsigned lo - size_chunk Mptr) of Some (Vlong sz) \<Rightarrow>
      (if Int64.unsigned sz = 0 then None else
      (case Mem.free m b (Int64.unsigned lo - size_chunk Mptr) (Int64.unsigned lo + Int64.unsigned sz) of Some m' \<Rightarrow>
      Some (E0, Vundef, m') | _ \<Rightarrow> None)) | _ \<Rightarrow> None) | _ \<Rightarrow> None))"
  apply (rule external_call_resultI)
   apply (auto elim!: extcall_free_sem.cases split: option.splits val.splits if_splits list.splits simp: Vptrofs_def Vnullptr_def)
   apply (metis Vnullptr_def extcall_free_sem_null)
  apply (simp add: extcall_free_sem.simps)
  unfolding Vptrofs_def Vnullptr_def
  by (metis linorder_neqE_linordered_idom uint_lt_0)

print_statement extcall_memcpy_sem.simps[simplified]

lemma extcall_memcpy_result:
  shows
    "external_call_result (EF_memcpy sz al) ge vargs m =
      (case vargs of [Vptr bdst odst, Vptr bsrc osrc] \<Rightarrow>
      (if a2 = 1 \<or> a2 = 2 \<or> a2 = 4 \<or> a2 = 8 then
      (if 0 \<le> sz \<or> (al dvd sz) then
      (if 0 < a1 \<longrightarrow> a2 dvd Int64.unsigned osrc then
      (if 0 < a1 \<longrightarrow> a2 dvd Int64.unsigned odst then
      (if bsrc = bdst \<longrightarrow>
          Int64.unsigned osrc = Int64.unsigned odst \<or>
          Int64.unsigned osrc + a1 \<le> Int64.unsigned odst \<or>
          Int64.unsigned odst + a1 \<le> Int64.unsigned osrc then
      (case Mem.loadbytes m bsrc (Int64.unsigned osrc) sz of Some bytes \<Rightarrow>
      (case Mem.storebytes m bdst (Int64.unsigned odst) bytes of Some m' \<Rightarrow>
      Some (E0, Vundef, m') | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None) else None) else None) else None) else None) | _ \<Rightarrow> None)"
proof -
  {
    fix osrc odst bsrc bdst bytes m'

    assume [simp]: "vargs = [Vptr bdst odst, Vptr bsrc osrc]"
    assume [iff]: "a2 = 1 \<or> a2 = 2 \<or> a2 = 4 \<or> a2 = 8"
    assume sz[iff]: "0 \<le> sz \<or> (al dvd sz)"
    assume [iff]: "0 < a1 \<longrightarrow> a2 dvd Int64.unsigned osrc"
    assume [iff]: "0 < a1 \<longrightarrow> a2 dvd Int64.unsigned odst"
    assume [iff]: "bsrc = bdst \<longrightarrow>
          Int64.unsigned osrc = Int64.unsigned odst \<or>
          Int64.unsigned osrc + a1 \<le> Int64.unsigned odst \<or>
          Int64.unsigned odst + a1 \<le> Int64.unsigned osrc"

    assume bytes[simp]: "Mem.loadbytes m bsrc (Int64.unsigned osrc) sz = Some bytes"
    assume m'[simp]: "Mem.storebytes m bdst (Int64.unsigned odst) bytes = Some m'"

    have bytes_len[simp]: "length bytes = nat sz"
      using Mem.loadbytes_len[OF bytes]
      by simp

    have sz_0[iff]: "sz = 0 \<Longrightarrow> m' = m"
      using Mem.storebytes_0 Mem.loadbytes_0 bytes m' by auto

    then have ?thesis
      apply (simp)
      sorry
  }

  then show ?thesis
    sorry

qed

subsection \<open>Determinism\<close>

(*
  all external calls are guaranteed to be deterministic modulo their trace;
  so extcalls not generating a trace are fully deterministic
*)

definition "determ_extfun ef \<equiv>
  \<forall>ge vargs m t vres m'. (external_call ef ge vargs m t vres m' \<longrightarrow> t = E0)"

(* for now, all the external functions we implement are deterministic *)
lemma determ_extfun[iff]: "determ_extfun ef"
  unfolding determ_extfun_def
  apply (cases ef)
  by (auto elim: extcall_malloc_sem.cases extcall_free_sem.cases extcall_memcpy_sem.cases)

lemma determ_extfun_notrace:
  "determ_extfun ef \<Longrightarrow> external_call ef ge vargs m t vres m' \<Longrightarrow> t = E0"
  unfolding determ_extfun_def
  by blast

lemma extcall_determ:
  assumes "determ_extfun ef"
  assumes "external_call ef ge vargs m t vres m'"
  shows "external_call ef ge vargs m t' vres' m'' \<Longrightarrow> t' = t \<and> vres' = vres \<and> m'' = m'"
  using determ_extfun_notrace[OF assms]
  using assms(1) assms(2) determ_extfun_notrace external_call_deterministic by blast

subsection \<open>Equivalance\<close>

lemma extcall_result_equiv:
  assumes "determ_extfun ef"
  shows
    "external_call ef ge vargs m t vres m' \<longleftrightarrow> external_call_result ef ge vargs m = Some (t, vres, m')"
  unfolding external_call_result_def
  apply standard
  using extcall_determ apply auto[1]
  apply (auto split: if_splits)
  by (smt (verit, ccfv_threshold) assms case_prodD case_prodE case_prodI extcall_determ theI')

subsection \<open>Deterministic world\<close>

locale deterministic_world
begin
lemmas extcall_determ = extcall_determ[OF determ_extfun]
lemmas extcall_result_equiv = extcall_result_equiv[OF determ_extfun]
end

end