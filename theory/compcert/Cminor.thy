theory Cminor
  imports
    Cminor_Syntax
    Values
    Globalenvs
    Events
    Switch
    Memory
    Smallstep
begin

section \<open>Operational Semantics\<close>

(** Two kinds of evaluation environments are involved:
- [genv]: global environments, define symbols and functions;
- [env]: local environments, map local variables to values.
*)

type_synonym genv = "(fundef, unit) Genv_t"
type_synonym env = "val ITree"

interpretation Genv: Genv' "TYPE(fundef)" "TYPE(unit)" .

(** The following functions build the initial local environment at
  function entry, binding parameters to the provided arguments and
  initializing local variables to [Vundef]. *)

fun set_params :: "(val list) \<Rightarrow> (ident list) \<Rightarrow> env" where
  "set_params (v1 # vs) (i1 # is) = ITree.set i1 v1 (set_params vs is)"
| "set_params [] (i1 # is) = ITree.set i1 Vundef (set_params [] is)"
| "set_params _ _ = ITree.empty"

fun set_locals :: "(ident list) \<Rightarrow> env \<Rightarrow> env" where
  "set_locals [] e = e"
| "set_locals (i1 # is) e = ITree.set i1 Vundef (set_locals is e)"

fun set_optvar :: "(ident option) \<Rightarrow> val \<Rightarrow> env \<Rightarrow> env" where
  "set_optvar None v e = e"
| "set_optvar (Some ident) v e = ITree.set ident v e"

(** Continuations *)

datatype cont =
    Kstop (* stop program execution *)
  | Kseq stmt cont (* execute stmt, then cont *)
  | Kblock cont (* exit a block, then do cont *)
  | Kcall "ident option" func val env cont (* return to caller *)

(** States *)

datatype state =
    State (* Execution within a function *)
      func (* currently executing function *)
      stmt (* statement under consideration *)
      cont (* its continuation -- what to do next *)
      val (* current stack pointer *)
      env (* current local environment *)
      mem (* current memory state *)
  | Callstate (* Invocation of a function *)
      fundef (* function to invoke *)
      "val list" (* arguments provided by caller *)
      cont (* what to do next *)
      mem (* memory state *)
  | Returnstate (* Return from a function *)
      val (* Return value *)
      cont (* what to do next *)
      mem (* memory state *)

context
  fixes ge :: genv
begin

(** Evaluation of constants and operator applications.
    [None] is returned when the computation is undefined, e.g.
    if arguments are of the wrong types, or in case of an integer division
    by zero. *)

fun eval_constant :: "val \<Rightarrow> const \<Rightarrow> val option" where
  "eval_constant _ (Ointconst n) = Some (Vint n)"
| "eval_constant _ (Ofloatconst n) = Some (Vfloat n)"
| "eval_constant _ (Osingleconst n) = Some (Vsingle n)"
| "eval_constant _ (Olongconst n) = Some (Vlong n)"
| "eval_constant _ (Oaddrsymbol s ofs) = Some (Genv.symbol_address ge s ofs)"
| "eval_constant sp (Oaddrstack ofs) = Some (Val.offset_ptr sp ofs)"

fun eval_unop :: "unary_operation \<Rightarrow> val \<Rightarrow> (val option)" where
  "eval_unop Ocast8unsigned v = Some (Val.zero_ext TYPE(8) v)"
| "eval_unop Ocast8signed v = Some (Val.sign_ext TYPE(8) v)"
| "eval_unop Ocast16unsigned v = Some (Val.zero_ext TYPE(16) v)"
| "eval_unop Ocast16signed v = Some (Val.sign_ext TYPE(16) v)"
| "eval_unop Onegint v = Some (Val.negint v)"
| "eval_unop Onotint v = Some (Val.notint v)"
| "eval_unop Onegf v = Some (Val.negf v)"
| "eval_unop Oabsf v = Some (Val.absf v)"
| "eval_unop Onegfs v = Some (Val.negfs v)"
| "eval_unop Oabsfs v = Some (Val.absfs v)"
(* | "eval_unop Osingleoffloat v = Some (Val.singleoffloat v)"
| "eval_unop Ofloatofsingle v = Some (Val.floatofsingle v)"
| "eval_unop Ointoffloat v = Val.intoffloat v"
| "eval_unop Ointuoffloat v = Val.intuoffloat v"
| "eval_unop Ofloatofint v = Val.floatofint v"
| "eval_unop Ofloatofintu v = Val.floatofintu v"
| "eval_unop Ointofsingle v = Val.intofsingle v"
| "eval_unop Ointuofsingle v = Val.intuofsingle v"
| "eval_unop Osingleofint v = Val.singleofint v"
| "eval_unop Osingleofintu v = Val.singleofintu v" *)
| "eval_unop Onegl v = Some (Val.negl v)"
| "eval_unop Onotl v = Some (Val.notl v)"
| "eval_unop Ointoflong v = Some (Val.loword v)"
| "eval_unop Olongofint v = Some (Val.longofint v)"
| "eval_unop Olongofintu v = Some (Val.longofintu v)"
(*| "eval_unop Olongoffloat v = Val.longoffloat v"
| "eval_unop Olonguoffloat v = Val.longuoffloat v"
| "eval_unop Ofloatoflong v = Val.floatoflong v"
| "eval_unop Ofloatoflongu v = Val.floatoflongu v"
| "eval_unop Olongofsingle v = Val.longofsingle v"
| "eval_unop Olonguofsingle v = Val.longuofsingle v"
| "eval_unop Osingleoflong v = Val.singleoflong v"
| "eval_unop Osingleoflongu v = Val.singleoflongu v" *)
| "eval_unop _ _ = None"

fun eval_binop :: "binary_operation \<Rightarrow> val \<Rightarrow> val \<Rightarrow> mem \<Rightarrow> (val option)" where
  "eval_binop Oadd arg1 arg2 m = Some (Val.add arg1 arg2)"
| "eval_binop Osub arg1 arg2 m = Some (Val.sub arg1 arg2)"
| "eval_binop Omul arg1 arg2 m = Some (Val.mul arg1 arg2)"
| "eval_binop Odiv arg1 arg2 m = Val.divs arg1 arg2"
| "eval_binop Odivu arg1 arg2 m = Val.divu arg1 arg2"
| "eval_binop Omod arg1 arg2 m = Val.mods arg1 arg2"
| "eval_binop Omodu arg1 arg2 m = Val.modu arg1 arg2"
| "eval_binop Oand arg1 arg2 m = Some (Val.and' arg1 arg2)"
| "eval_binop Oor arg1 arg2 m = Some (Val.or arg1 arg2)"
| "eval_binop Oxor arg1 arg2 m = Some (Val.xor' arg1 arg2)"
| "eval_binop Oshl arg1 arg2 m = Some (Val.shl arg1 arg2)"
| "eval_binop Oshr arg1 arg2 m = Some (Val.shr arg1 arg2)"
| "eval_binop Oshru arg1 arg2 m = Some (Val.shru arg1 arg2)"
| "eval_binop Oaddf arg1 arg2 m = Some (Val.addf arg1 arg2)"
| "eval_binop Osubf arg1 arg2 m = Some (Val.subf arg1 arg2)"
| "eval_binop Omulf arg1 arg2 m = Some (Val.mulf arg1 arg2)"
| "eval_binop Odivf arg1 arg2 m = Some (Val.divf arg1 arg2)"
| "eval_binop Oaddfs arg1 arg2 m = Some (Val.addfs arg1 arg2)"
| "eval_binop Osubfs arg1 arg2 m = Some (Val.subfs arg1 arg2)"
| "eval_binop Omulfs arg1 arg2 m = Some (Val.mulfs arg1 arg2)"
| "eval_binop Odivfs arg1 arg2 m = Some (Val.divfs arg1 arg2)"
| "eval_binop Oaddl arg1 arg2 m = Some (Val.addl arg1 arg2)"
| "eval_binop Osubl arg1 arg2 m = Some (Val.subl arg1 arg2)"
| "eval_binop Omull arg1 arg2 m = Some (Val.mull arg1 arg2)"
| "eval_binop Odivl arg1 arg2 m = Val.divls arg1 arg2"
| "eval_binop Odivlu arg1 arg2 m = Val.divlu arg1 arg2"
| "eval_binop Omodl arg1 arg2 m = Val.modls arg1 arg2"
| "eval_binop Omodlu arg1 arg2 m = Val.modlu arg1 arg2"
| "eval_binop Oandl arg1 arg2 m = Some (Val.andl arg1 arg2)"
| "eval_binop Oorl arg1 arg2 m = Some (Val.orl arg1 arg2)"
| "eval_binop Oxorl arg1 arg2 m = Some (Val.xorl arg1 arg2)"
| "eval_binop Oshll arg1 arg2 m = Some (Val.shll arg1 arg2)"
| "eval_binop Oshrl arg1 arg2 m = Some (Val.shrl arg1 arg2)"
| "eval_binop Oshrlu arg1 arg2 m = Some (Val.shrlu arg1 arg2)"
| "eval_binop (Ocmp c) arg1 arg2 m = Some (Val.cmp c arg1 arg2)"
| "eval_binop (Ocmpu c) arg1 arg2 m = Some (Val.cmpu (Mem.valid_pointer m) c arg1 arg2)"
| "eval_binop (Ocmpf c) arg1 arg2 m = Some (Val.cmpf c arg1 arg2)"
| "eval_binop (Ocmpfs c) arg1 arg2 m = Some (Val.cmpfs c arg1 arg2)"
| "eval_binop (Ocmpl c) arg1 arg2 m = Val.cmpl c arg1 arg2"
| "eval_binop (Ocmplu c) arg1 arg2 m = Val.cmplu (Mem.valid_pointer m) c arg1 arg2"

(** Evaluation of an expression: [eval_expr ge sp e m a v]
  states that expression [a] evaluates to value [v].
  [ge] is the global environment, [e] the local environment,
  and [m] the current memory state.  They are unchanged during evaluation.
  [sp] is the pointer to the memory block allocated for this function
  (stack frame).
*)

context
  fixes sp :: val
  and e :: env
  and m :: mem
begin

inductive eval_expr :: "expr \<Rightarrow> val \<Rightarrow> bool" where
  eval_Evar: "\<And>ident v.
    ITree.get ident e = Some v\<Longrightarrow>
    eval_expr (Evar ident) v"
| eval_Econst: "\<And>cst v.
    eval_constant sp cst = Some v\<Longrightarrow>
    eval_expr (Econst cst) v"
| eval_Eunop: "\<And>op a1 v1 v.
    eval_expr a1 v1\<Longrightarrow>
    eval_unop op v1 = Some v\<Longrightarrow>
    eval_expr (Eunop op a1) v"
| eval_Ebinop: "\<And>op a1 a2 v1 v2 v.
    eval_expr a1 v1\<Longrightarrow>
    eval_expr a2 v2\<Longrightarrow>
    eval_binop op v1 v2 m = Some v\<Longrightarrow>
    eval_expr (Ebinop op a1 a2) v"
| eval_Eload: "\<And>chunk addr vaddr v.
    eval_expr addr vaddr\<Longrightarrow>
    Mem.loadv chunk m vaddr = Some v\<Longrightarrow>
    eval_expr (Eload chunk addr) v"

inductive eval_exprlist :: "(expr list) \<Rightarrow> (val list) \<Rightarrow> bool" where
  eval_Enil: "eval_exprlist [] []"
| eval_Econs: "\<And>a1 al v1 vl.
    eval_expr a1 v1\<Longrightarrow>
    eval_exprlist al vl\<Longrightarrow>
    eval_exprlist (a1 # al) (v1 # vl)"

end

(** Pop continuation until a call or stop *)

fun call_cont :: "cont \<Rightarrow> cont" where
  "call_cont (Kseq s k) = call_cont k"
| "call_cont (Kblock k) = call_cont k"
| "call_cont k = k"

inductive is_call_cont :: "cont \<Rightarrow> bool" where
  "is_call_cont Kstop"
| "is_call_cont (Kcall _ _ _ _ _)"

lemmas [simp] = is_call_cont.simps

lemma call_cont_is_call_cont[iff]: "is_call_cont (call_cont k)"
  by (induction k; simp)

(** Find the statement and manufacture the continuation
  corresponding to a label *)

fun find_label :: "label \<Rightarrow> stmt \<Rightarrow> cont \<Rightarrow> ((stmt * cont) option)" where
  "find_label lbl s k =
  (case s of
    Sseq s1 s2 \<Rightarrow>
      (case find_label lbl s1 (Kseq s2 k) of
        Some sk \<Rightarrow> Some sk
      | None \<Rightarrow> find_label lbl s2 k
      )
  | Sifthenelse a s1 s2 \<Rightarrow>
      (case find_label lbl s1 k of
        Some sk \<Rightarrow> Some sk
      | None \<Rightarrow> find_label lbl s2 k
      )
  | Sloop s1 \<Rightarrow>
      find_label lbl s1 (Kseq (Sloop s1) k)
  | Sblock s1 \<Rightarrow>
      find_label lbl s1 (Kblock k)
  | Slabel lbl' s' \<Rightarrow>
      (if lbl = lbl' then Some(s', k) else find_label lbl s' k)
  | _ \<Rightarrow> None
  )"

(** One step of execution *)

inductive step :: "state \<Rightarrow> trace \<Rightarrow> state \<Rightarrow> bool" where
  step_skip_seq: "\<And>f s k sp e m.
    step (State f Sskip (Kseq s k) sp e m) E0 (State f s k sp e m)"
| step_skip_block: "\<And>f k sp e m.
    step (State f Sskip (Kblock k) sp e m) E0 (State f Sskip k sp e m)"
| step_skip_call: "\<And>f k sp e m m'.
    is_call_cont k \<Longrightarrow>
    Mem.free m sp 0 (fn_stackspace f) = Some m' \<Longrightarrow>
    step (State f Sskip k (Vptr sp 0) e m) E0 (Returnstate Vundef k m')"
| step_assign: "\<And>f ident a k sp e m v.
    eval_expr sp e m a v \<Longrightarrow>
    step (State f (Sassign ident a) k sp e m) E0 (State f Sskip k sp (ITree.set ident v e) m)"
| step_store: "\<And>f chunk addr a k sp e m vaddr v m'.
    eval_expr sp e m addr vaddr \<Longrightarrow>
    eval_expr sp e m a v \<Longrightarrow>
    Mem.storev chunk m vaddr v = Some m' \<Longrightarrow>
    step (State f (Sstore chunk addr a) k sp e m) E0 (State f Sskip k sp e m')"
| step_call: "\<And>f optid sig a bl k sp e m vf vargs fd.
    eval_expr sp e m a vf \<Longrightarrow>
    eval_exprlist sp e m bl vargs \<Longrightarrow>
    Genv.find_funct ge vf = Some fd \<Longrightarrow>
    funsig fd = sig \<Longrightarrow>
    step (State f (Scall optid sig a bl) k sp e m) E0 (Callstate fd vargs (Kcall optid f sp e k) m)"
| step_tailcall: "\<And>f sig a bl k sp e m vf vargs fd m'.
    eval_expr (Vptr sp 0) e m a vf \<Longrightarrow>
    eval_exprlist (Vptr sp 0) e m bl vargs \<Longrightarrow>
    Genv.find_funct ge vf = Some fd \<Longrightarrow>
    funsig fd = sig \<Longrightarrow>
    Mem.free m sp 0 (fn_stackspace f) = Some m' \<Longrightarrow>
    step (State f (Stailcall sig a bl) k (Vptr sp 0) e m) E0 (Callstate fd vargs (call_cont k) m')"
| step_builtin: "\<And>f optid ef bl k sp e m vargs t vres m'.
    eval_exprlist sp e m bl vargs \<Longrightarrow>
    external_call ef (Genv.to_senv ge) vargs m t vres m' \<Longrightarrow>
    step (State f (Sbuiltin optid ef bl) k sp e m) t (State f Sskip k sp (set_optvar optid vres e) m')"
| step_seq: "\<And>f s1 s2 k sp e m.
    step (State f (Sseq s1 s2) k sp e m) E0 (State f s1 (Kseq s2 k) sp e m)"
| step_ifthenelse: "\<And>f a s1 s2 k sp e m v b.
    eval_expr sp e m a v \<Longrightarrow>
    Val.bool_of_val v b \<Longrightarrow>
    step (State f (Sifthenelse a s1 s2) k sp e m) E0 (State f (if b then s1 else s2) k sp e m)"
| step_loop: "\<And>f s k sp e m.
    step (State f (Sloop s) k sp e m) E0 (State f s (Kseq (Sloop s) k) sp e m)"
| step_block: "\<And>f s k sp e m.
    step (State f (Sblock s) k sp e m) E0 (State f s (Kblock k) sp e m)"
| step_exit_seq: "\<And>f n s k sp e m.
    step (State f (Sexit n) (Kseq s k) sp e m) E0 (State f (Sexit n) k sp e m)"
| step_exit_block_0: "\<And>f k sp e m.
    step (State f (Sexit 0) (Kblock k) sp e m) E0 (State f Sskip k sp e m)"
| step_exit_block_S: "\<And>f n k sp e m.
    step (State f (Sexit (Suc n)) (Kblock k) sp e m) E0 (State f (Sexit n) k sp e m)"
| step_switch: "\<And>f islong a cases default k sp e m v n.
    eval_expr sp e m a v \<Longrightarrow>
    switch_argument islong v n \<Longrightarrow>
    step (State f (Sswitch islong a cases default) k sp e m) E0 (State f (Sexit (switch_target n default cases)) k sp e m)"
| step_return_0: "\<And>f k sp e m m'.
    Mem.free m sp 0 (fn_stackspace f) = Some m' \<Longrightarrow>
    step (State f (Sreturn None) k (Vptr sp 0) e m) E0 (Returnstate Vundef (call_cont k) m')"
| step_return_1: "\<And>f a k sp e m v m'.
    eval_expr (Vptr sp 0) e m a v \<Longrightarrow>
    Mem.free m sp 0 (fn_stackspace f) = Some m' \<Longrightarrow>
    step (State f (Sreturn (Some a)) k (Vptr sp 0) e m) E0 (Returnstate v (call_cont k) m')"
| step_label: "\<And>f lbl s k sp e m.
    step (State f (Slabel lbl s) k sp e m) E0 (State f s k sp e m)"
| step_goto: "\<And>f lbl k sp e m s' k'.
    find_label lbl (fn_body f) (call_cont k) = Some (s', k') \<Longrightarrow>
    step (State f (Sgoto lbl) k sp e m) E0 (State f s' k' sp e m)"
| step_internal_function: "\<And>f vargs k m m' sp e.
    Mem.alloc m 0 (fn_stackspace f) = (m', sp) \<Longrightarrow>
    set_locals (fn_vars f) (set_params vargs (fn_params f)) = e \<Longrightarrow>
    step (Callstate (Internal f) vargs k m) E0 (State f (fn_body f) k (Vptr sp 0) e m')"
| step_external_function: "\<And>ef vargs k m t vres m'.
    external_call ef (Genv.to_senv ge) vargs m t vres m' \<Longrightarrow>
    step (Callstate (External ef) vargs k m) t (Returnstate vres k m')"
| step_return: "\<And>v optid f sp e k m.
    step (Returnstate v (Kcall optid f sp e k) m) E0 (State f Sskip k sp (set_optvar optid v e) m)"

end

(* Remove exec simps from default simp-set *)
lemmas exec_simps[simp del] = Genv.find_funct.simps set_locals.simps Genv.to_senv.simps

(** Execution of whole programs are described as sequences of transitions
  from an initial state to a final state.  An initial state is a [Callstate]
  corresponding to the invocation of the ``main'' function of the program
  without arguments and with an empty continuation. *)

inductive initial_state :: "program \<Rightarrow> state \<Rightarrow> bool" where
    initial_state_intro:
      "Genv.globalenv p = ge \<Longrightarrow>
      Genv.init_mem p = Some m0 \<Longrightarrow>
      Genv.find_funct_ptr ge b = Some f \<Longrightarrow>
      Genv.find_symbol ge (prog_main p) = Some b \<Longrightarrow>
      funsig f = signature_main \<Longrightarrow>
      initial_state p (Callstate f [] Kstop m0)"

(** A final state is a [Returnstate] with an empty continuation. *)

inductive final_state :: "state \<Rightarrow> m_int \<Rightarrow> bool" where
    final_state_intro:
      "final_state (Returnstate (Vint r) Kstop m) r"

subsection \<open>Addition: Determinism\<close>

(** This semantics is determinate. *)

lemma eval_expr_determ:
  assumes "eval_expr ge sp e m a v1" "eval_expr ge sp e m a v2"
  shows "v1 = v2"
  using assms
proof (induct arbitrary: v2 rule: eval_expr.induct[OF assms(1)])
case (1 ident v)
  then show ?case
    using eval_expr.cases by force
next
  case (2 cst v)
  then show ?case
    using eval_expr.cases by force
next
  case (3 a1 v1 op v)
  show ?case
    apply (cases rule: eval_expr.cases[OF 3(5)])
        apply auto
    using "3.hyps" by auto
next
  case (4 a1 v1 a2 v2 op v)
  show ?case
    apply (cases rule: eval_expr.cases[OF 4(7)])
        apply auto
    using "4.hyps" by auto
next
  case (5 addr vaddr chunk v)
  show ?case
    apply (cases rule: eval_expr.cases[OF 5(5)])
        apply auto
    using "5.hyps" by auto
qed

lemma eval_exprlist_determ:
  assumes "eval_exprlist ge sp e m as vs1" "eval_exprlist ge sp e m as vs2"
  shows "vs1 = vs2"
  using assms apply (induct arbitrary: vs2 rule: eval_exprlist.induct)
  using eval_exprlist.cases apply blast
  by (metis eval_expr_determ eval_exprlist.cases list.discI list.sel(1) list.sel(3))

lemma bool_of_val_determ:
  assumes "Val.bool_of_val v b1" "Val.bool_of_val v b2"
  shows "b1 = b2"
  by (metis (full_types) assms(1) assms(2) Val.bool_of_val.cases val.inject(1))
lemma switch_argument_determ:
  assumes "switch_argument islong v n1" "switch_argument islong v n2"
  shows "n1 = n2"
  using assms(1) assms(2) switch_argument.simps by auto
lemma switch_argument_determ_elim:
  assumes "switch_argument islong v n1" "switch_argument islong v n2"
  shows "(n1 = n2 \<Longrightarrow> P) \<Longrightarrow> P"
  using assms(1) assms(2) switch_argument.simps by auto

theorem eval_expr_determ':
  assumes "eval_expr ge sp e m a v"
  shows "\<And>v'. eval_expr ge sp e m a v' = (v = v')"
  using eval_expr_determ assms by auto

theorem eval_expr_determ_elim:
  assumes "eval_expr ge sp e m a v" "eval_expr ge sp e m a v'"
  shows "(v=v' \<Longrightarrow> P) \<Longrightarrow> P"
  using eval_expr_determ assms by auto

theorem eval_exprlist_determ':
  assumes "eval_exprlist ge sp e m a v"
  shows "\<And>v'. eval_exprlist ge sp e m a v' = (v = v')"
  using eval_exprlist_determ assms by auto

theorem eval_exprlist_determ_elim:
  assumes "eval_exprlist ge sp e m as vs" "eval_exprlist ge sp e m as vs'"
  shows "(vs=vs' \<Longrightarrow> P) \<Longrightarrow> P"
  using eval_exprlist_determ assms by auto

lemma bool_of_val_determ':
  assumes "Val.bool_of_val v b"
  shows "\<And>b'. Val.bool_of_val v b' = (b = b')"
  using bool_of_val_determ assms by auto

lemma switch_argument_determ':
  assumes "switch_argument islong v n" 
  shows "\<And>n'. switch_argument islong v n' = (n = n')"
  using switch_argument_determ assms by auto

lemmas exprs_determ = eval_expr_determ' eval_exprlist_determ' bool_of_val_determ' switch_argument_determ'

section \<open>Alternate operational semantics (big-step)\<close>

datatype outcome =
    Out_normal              (* continue in sequence *)
  | Out_exit nat            (* terminate [n+1] enclosing blocks *)
  | Out_return "val option" (* return immediately to caller *)
  | Out_tailcall_return val (* already returned to caller via a tailcall *)

fun outcome_block :: "outcome \<Rightarrow> outcome" where
  "outcome_block (Out_exit 0) = Out_normal"
| "outcome_block (Out_exit (Suc n)) = Out_exit n"
| "outcome_block out = out"

fun outcome_result_value :: "outcome \<Rightarrow> val \<Rightarrow> bool" where
  "outcome_result_value Out_normal vres = (vres = Vundef)"
| "outcome_result_value (Out_return None) vres = (vres = Vundef)"
| "outcome_result_value (Out_return ( Some v )) vres = (vres = v)"
| "outcome_result_value (Out_tailcall_return v) vres = (vres = v)"
| "outcome_result_value _ vres = False"

fun outcome_result_value_func :: "outcome \<Rightarrow> val option" where
  "outcome_result_value_func Out_normal = Some Vundef"
| "outcome_result_value_func (Out_return None) = Some Vundef"
| "outcome_result_value_func (Out_return (Some v)) = Some v"
| "outcome_result_value_func (Out_tailcall_return v) =  Some v"
| "outcome_result_value_func _ = None"

lemma outcome_result_value_func:
  "outcome_result_value_func out = Some vres \<longleftrightarrow> outcome_result_value out vres"
  apply (cases out; auto)
   apply (metis option.exhaust outcome_result_value.simps(2) outcome_result_value.simps(3) outcome_result_value_func.simps(2) outcome_result_value_func.simps(3))
  by (metis option.exhaust outcome_result_value.simps(2) outcome_result_value.simps(3) outcome_result_value_func.simps(2) outcome_result_value_func.simps(3))

fun outcome_free_mem :: "outcome \<Rightarrow> mem \<Rightarrow> block \<Rightarrow> Z \<Rightarrow> mem \<Rightarrow> bool" where
  "outcome_free_mem (Out_tailcall_return _) m sp sz m' = (m' = m)"
| "outcome_free_mem _ m sp sz m' = (Mem.free m sp 0 sz = Some m')"

fun outcome_free_mem_func :: "outcome \<Rightarrow> mem \<Rightarrow> block \<Rightarrow> Z \<Rightarrow> mem option" where
  "outcome_free_mem_func out m sp sz
    = (case out of Out_tailcall_return x \<Rightarrow> Some m | _ \<Rightarrow> Mem.free m sp 0 sz)"

lemma outcome_free_mem_func:
  "outcome_free_mem_func out m sp sz = Some m' \<longleftrightarrow> outcome_free_mem out m sp sz m'"
  by (cases out; auto)

context
  fixes ge :: genv
begin

inductive
    eval_funcall :: "mem \<Rightarrow> fundef \<Rightarrow> val list \<Rightarrow> trace \<Rightarrow> mem \<Rightarrow> val \<Rightarrow> bool" and
    exec_stmt :: "func \<Rightarrow> val \<Rightarrow> env \<Rightarrow> mem \<Rightarrow> stmt \<Rightarrow> trace \<Rightarrow> env \<Rightarrow> mem \<Rightarrow> outcome \<Rightarrow> bool" where

(** Evaluation of a function invocation: [eval_funcall ge m f args t m' res]
  means that the function [f], applied to the arguments [args] in
  memory state [m], returns the value [res] in modified memory state [m'].
  [t] is the trace of observable events generated during the invocation.
*)

  eval_funcall_internal: "\<And>m f vargs m1 sp e t e2 m2 out vres m3.
    Mem.alloc m 0 (fn_stackspace f) = (m1, sp) \<Longrightarrow>
    set_locals (fn_vars f) (set_params vargs (fn_params f)) = e \<Longrightarrow>
    exec_stmt f (Vptr sp 0) e m1 (fn_body f) t e2 m2 out \<Longrightarrow>
    outcome_result_value out vres \<Longrightarrow>
    outcome_free_mem out m2 sp (fn_stackspace f) m3 \<Longrightarrow>
    eval_funcall m (Internal f) vargs t m3 vres"
| eval_funcall_external: "\<And>ef m args t res m'.
    external_call ef (Genv.to_senv ge) args m t res m' \<Longrightarrow>
    eval_funcall m (External ef) args t m' res"

(** Execution of a statement: [exec_stmt ge f sp e m s t e' m' out]
  means that statement [s] executes with outcome [out].
  [e] is the initial environment and [m] is the initial memory state.
  [e'] is the final environment, reflecting variable assignments performed
  by [s].  [m'] is the final memory state, reflecting memory stores
  performed by [s].  [t] is the trace of I/O events performed during
  the execution.  The other parameters are as in [eval_expr]. *)

| exec_Sskip: "\<And>f sp e m.
    exec_stmt f sp e m Sskip E0 e m Out_normal"
| exec_Sassign: "\<And>f sp e m ident a v.
    eval_expr ge sp e m a v \<Longrightarrow>
    exec_stmt f sp e m (Sassign ident a) E0 (ITree.set ident v e) m Out_normal"
| exec_Sstore: "\<And>f sp e m chunk addr a vaddr v m'.
    eval_expr ge sp e m addr vaddr \<Longrightarrow>
    eval_expr ge sp e m a v \<Longrightarrow>
    Mem.storev chunk m vaddr v = Some m' \<Longrightarrow>
    exec_stmt f sp e m (Sstore chunk addr a) E0 e m' Out_normal"
| exec_Scall: "\<And>f sp e m optid sig a bl vf vargs fd t m' vres e'.
    eval_expr ge sp e m a vf \<Longrightarrow>
    eval_exprlist ge sp e m bl vargs \<Longrightarrow>
    Genv.find_funct ge vf = Some fd \<Longrightarrow>
    funsig fd = sig \<Longrightarrow>
    eval_funcall m fd vargs t m' vres \<Longrightarrow>
    e' = set_optvar optid vres e \<Longrightarrow>
    exec_stmt f sp e m (Scall optid sig a bl) t e' m' Out_normal"
| exec_Sbuiltin: "\<And>f sp e m optid ef bl t m' vargs vres e'.
    eval_exprlist ge sp e m bl vargs \<Longrightarrow>
    external_call ef (Genv.to_senv ge) vargs m t vres m' \<Longrightarrow>
    e' = set_optvar optid vres e \<Longrightarrow>
    exec_stmt f sp e m (Sbuiltin optid ef bl) t e' m' Out_normal"
| exec_Sifthenelse: "\<And>f sp e m a s1 s2 v b t e' m' out.
    eval_expr ge sp e m a v \<Longrightarrow>
    Val.bool_of_val v b \<Longrightarrow>
    exec_stmt f sp e m (if b then s1 else s2) t e' m' out \<Longrightarrow>
    exec_stmt f sp e m (Sifthenelse a s1 s2) t e' m' out"
| exec_Sseq_continue: "\<And>f sp e m t s1 t1 e1 m1 s2 t2 e2 m2 out.
    exec_stmt f sp e m s1 t1 e1 m1 Out_normal \<Longrightarrow>
    exec_stmt f sp e1 m1 s2 t2 e2 m2 out \<Longrightarrow>
    t = t1 @ t2 \<Longrightarrow>
    exec_stmt f sp e m (Sseq s1 s2) t e2 m2 out"
| exec_Sseq_stop: "\<And>f sp e m t s1 s2 e1 m1 out.
    exec_stmt f sp e m s1 t e1 m1 out \<Longrightarrow>
    out \<noteq> Out_normal \<Longrightarrow>
    exec_stmt f sp e m (Sseq s1 s2) t e1 m1 out"
| exec_Sloop_loop: "\<And>f sp e m s t t1 e1 m1 t2 e2 m2 out.
    exec_stmt f sp e m s t1 e1 m1 Out_normal \<Longrightarrow>
    exec_stmt f sp e1 m1 (Sloop s) t2 e2 m2 out \<Longrightarrow>
    t = t1 @ t2 \<Longrightarrow>
    exec_stmt f sp e m (Sloop s) t e2 m2 out"
| exec_Sloop_stop: "\<And>f sp e m t s e1 m1 out.
    exec_stmt f sp e m s t e1 m1 out \<Longrightarrow>
    out \<noteq> Out_normal \<Longrightarrow>
    exec_stmt f sp e m (Sloop s) t e1 m1 out"
| exec_Sblock: "\<And>f sp e m s t e1 m1 out.
    exec_stmt f sp e m s t e1 m1 out \<Longrightarrow>
    exec_stmt f sp e m (Sblock s) t e1 m1 (outcome_block out)"
| exec_Sexit: "\<And>f sp e m n.
    exec_stmt f sp e m (Sexit n) E0 e m (Out_exit n)"
| exec_Sswitch: "\<And>f sp e m islong a cases default v n.
    eval_expr ge sp e m a v \<Longrightarrow>
    switch_argument islong v n \<Longrightarrow>
    exec_stmt f sp e m (Sswitch islong a cases default) E0 e m (Out_exit (switch_target n default cases))"
| exec_Sreturn_none: "\<And>f sp e m.
    exec_stmt f sp e m (Sreturn None) E0 e m (Out_return None)"
| exec_Sreturn_some: "\<And>f sp e m a v.
    eval_expr ge sp e m a v \<Longrightarrow>
    exec_stmt f sp e m (Sreturn (Some a)) E0 e m (Out_return (Some v))"
| exec_Stailcall: "\<And>f sp e m sig a bl vf vargs fd t m' m'' vres.
    eval_expr ge (Vptr sp 0) e m a vf \<Longrightarrow>
    eval_exprlist ge (Vptr sp 0) e m bl vargs \<Longrightarrow>
    Genv.find_funct ge vf = Some fd \<Longrightarrow>
    funsig fd = sig \<Longrightarrow>
    Mem.free m sp 0 (fn_stackspace f) = Some m' \<Longrightarrow>
    eval_funcall m' fd vargs t m'' vres \<Longrightarrow>
    exec_stmt f (Vptr sp 0) e m (Stailcall sig a bl) t e m'' (Out_tailcall_return vres)"

named_theorems eval_funcall_simps
named_theorems eval_funcall_elims

inductive_simps eval_funcall_internal_simp[eval_funcall_simps]: "eval_funcall m (Internal f) vargs t m' vres"
inductive_simps eval_funcall_external_simp[eval_funcall_simps]: "eval_funcall m (External ef) vargs t m' vres"

inductive_cases eval_funcall_internalE[eval_funcall_elims]: "eval_funcall m (Internal f) vargs t m' vres"
inductive_cases eval_funcall_externalE[eval_funcall_elims]: "eval_funcall m (External ef) vargs t m' vres"

named_theorems exec_stmt_simps
named_theorems exec_stmt_elims

inductive_simps exec_stmt_Sskip_simp[exec_stmt_simps]: "exec_stmt f sp e m Sskip t e' m' out"
inductive_simps exec_stmt_Sstore_simp[exec_stmt_simps]: "exec_stmt f sp e m (Sstore chunk addr a) t e' m' out"
inductive_simps exec_stmt_Scall_simp[exec_stmt_simps]: "exec_stmt f sp e m (Scall optid sig a bl) t e' m' out"
inductive_simps exec_stmt_Stailcall_simp[exec_stmt_simps]: "exec_stmt f sp e m (Stailcall sig a bl) t e' m' out"
inductive_simps exec_stmt_Sbuiltin_simp[exec_stmt_simps]: "exec_stmt f sp e m (Sbuiltin optid ef bl) t e' m' out"
inductive_simps exec_stmt_Sseq_simp[exec_stmt_simps]: "exec_stmt f sp e m (Sseq s1 s2) t e' m' out"
inductive_simps exec_stmt_Sifthenelse_simp[exec_stmt_simps]: "exec_stmt f sp e m (Sifthenelse a s1 s2) t e' m' out"
inductive_simps exec_stmt_Sloop_simp[exec_stmt_simps]: "exec_stmt f sp e m (Sloop s) t e' m' out"
inductive_simps exec_stmt_Sblock_simp[exec_stmt_simps]: "exec_stmt f sp e m (Sblock s) t e' m' out"
inductive_simps exec_stmt_Sexit_simp[exec_stmt_simps]: "exec_stmt f sp e m (Sexit n) t e' m' out"
inductive_simps exec_stmt_Sswitch_simp[exec_stmt_simps]: "exec_stmt f sp e m (Sswitch islong a cases def) t e' m' out"
inductive_simps exec_stmt_Sreturn_simp[exec_stmt_simps]: "exec_stmt f sp e m (Sreturn ma) t e' m' out"

inductive_cases SskipE[exec_stmt_elims]: "exec_stmt f sp e m Sskip t e' m' out"
inductive_cases SstoreE[exec_stmt_elims]: "exec_stmt f sp e m (Sstore chunk addr a) t e' m' out"
inductive_cases ScallE[exec_stmt_elims]: "exec_stmt f sp e m (Scall optid sig a bl) t e' m' out"
inductive_cases StailcallE[exec_stmt_elims]: "exec_stmt f sp e m (Stailcall sig a bl) t e' m' out"
inductive_cases SbuiltinE[exec_stmt_elims]: "exec_stmt f sp e m (Sbuiltin optid ef bl) t e' m' out"
inductive_cases SseqE[exec_stmt_elims]: "exec_stmt f sp e m (Sseq s1 s2) t e' m' out"
inductive_cases SifthenelseE[exec_stmt_elims]: "exec_stmt f sp e m (Sifthenelse a s1 s2) t e' m' out"
inductive_cases SblockE[exec_stmt_elims]: "exec_stmt f sp e m (Sblock s) t e' m' out"
inductive_cases SexitE[exec_stmt_elims]: "exec_stmt f sp e m (Sexit n) t e' m' out"
inductive_cases SswitchE[exec_stmt_elims]: "exec_stmt f sp e m (Sswitch islong a cases def) t e' m' out"
inductive_cases SreturnE[exec_stmt_elims]: "exec_stmt f sp e m (Sreturn ma) t e' m' out"

inductive_cases SloopE[elim]: "exec_stmt f sp e m (Sloop s) t e' m' out"

lemmas exec_stmt_intros[intro] = eval_funcall_exec_stmt.intros(2-)
declare exec_stmt_elims[elim!]

(** Coinductive semantics for divergence.
  [evalinf_funcall ge m f args t]
  means that the function [f] diverges when applied to the arguments [args] in
  memory state [m].  The infinite trace [t] is the trace of
  observable events generated during the invocation.
*)

coinductive evalinf_funcall ::
        "mem \<Rightarrow> fundef \<Rightarrow> val list \<Rightarrow> traceinf \<Rightarrow> bool"
and execinf_stmt  ::
        "func \<Rightarrow> val \<Rightarrow> env \<Rightarrow> mem \<Rightarrow> stmt \<Rightarrow> traceinf \<Rightarrow> bool"
where
    evalinf_funcall_internal:
      "Mem.alloc m 0 (fn_stackspace f) = (m1, sp) \<Longrightarrow>
      set_locals (fn_vars f) (set_params vargs (fn_params f)) = e \<Longrightarrow>
      execinf_stmt f (Vptr sp 0) e m1 (fn_body f) t \<Longrightarrow>
      evalinf_funcall m (Internal f) vargs t"

(** [execinf_stmt ge sp e m s t] means that statement [s] diverges.
  [e] is the initial environment, [m] is the initial memory state,
  and [t] the trace of observable events performed during the execution. *)

  | execinf_Scall:
      "eval_expr ge sp e m a vf \<Longrightarrow>
      eval_exprlist ge sp e m bl vargs \<Longrightarrow>
      Genv.find_funct ge vf = Some fd \<Longrightarrow>
      funsig fd = sig \<Longrightarrow>
      evalinf_funcall m fd vargs t \<Longrightarrow>
      execinf_stmt f sp e m (Scall optid sig a bl) t"
  | execinf_Sifthenelse:
      "eval_expr ge sp e m a v \<Longrightarrow>
      Val.bool_of_val v b \<Longrightarrow>
      execinf_stmt f sp e m (if b then s1 else s2) t \<Longrightarrow>
      execinf_stmt f sp e m (Sifthenelse a s1 s2) t"
  | execinf_Sseq_1:
      "execinf_stmt f sp e m s1 t \<Longrightarrow>
      execinf_stmt f sp e m (Sseq s1 s2) t"
  | execinf_Sseq_2:
      "exec_stmt f sp e m s1 t1 e1 m1 Out_normal \<Longrightarrow>
      execinf_stmt f sp e1 m1 s2 t2 \<Longrightarrow>
      t = Eappinf t1 t2 \<Longrightarrow>
      execinf_stmt f sp e m (Sseq s1 s2) t"
  | execinf_Sloop_body:
      "execinf_stmt f sp e m s t \<Longrightarrow>
      execinf_stmt f sp e m (Sloop s) t"
  | execinf_Sloop_loop:
      "exec_stmt f sp e m s t1 e1 m1 Out_normal \<Longrightarrow>
      execinf_stmt f sp e1 m1 (Sloop s) t2 \<Longrightarrow>
      t = Eappinf t1 t2 \<Longrightarrow>
      execinf_stmt f sp e m (Sloop s) t"
  | execinf_Sblock:
      "execinf_stmt f sp e m s t \<Longrightarrow>
      execinf_stmt f sp e m (Sblock s) t"
  | execinf_Stailcall:
      "eval_expr ge (Vptr sp 0) e m a vf \<Longrightarrow>
      eval_exprlist ge (Vptr sp 0) e m bl vargs \<Longrightarrow>
      Genv.find_funct ge vf = Some fd \<Longrightarrow>
      funsig fd = sig \<Longrightarrow>
      Mem.free m sp 0 (fn_stackspace f) = Some m' \<Longrightarrow>
      evalinf_funcall m' fd vargs t \<Longrightarrow>
      execinf_stmt f (Vptr sp 0) e m (Stailcall sig a bl) t"
end

subsection \<open>Addition: Determinism\<close>

lemma outcome_result_value_determ:
  assumes "outcome_result_value out v"
  shows   "outcome_result_value out v2 = (v = v2)"
  apply (cases rule: outcome_result_value.cases[of "(out, v)"])
      using assms by auto

lemma outcome_free_mem_determ:
  assumes "outcome_free_mem out m sp b m1'"
  shows   "outcome_free_mem out m sp b m2' = (m1' = m2')"
  apply (cases rule: outcome_free_mem.cases[of "(out, m, sp, b, m1')"])
  using assms by auto

lemmas outcome_determ = outcome_result_value_determ outcome_free_mem_determ

section \<open>Big-step execution of a whole program\<close>

inductive bigstep_program_terminates :: "program \<Rightarrow> trace \<Rightarrow> m_int \<Rightarrow> bool" where
    bigstep_program_terminates_intro:
      "let ge = Genv.globalenv p in
      Genv.init_mem p = Some m0 \<Longrightarrow>
      Genv.find_symbol ge (prog_main p) = Some b \<Longrightarrow>
      Genv.find_funct_ptr ge b = Some f \<Longrightarrow>
      funsig f = signature_main \<Longrightarrow>
      eval_funcall ge m0 f [] t m (Vint r) \<Longrightarrow>
      bigstep_program_terminates p t r"

inductive bigstep_program_diverges :: "program \<Rightarrow> traceinf \<Rightarrow> bool" where
    bigstep_program_diverges_intro:
      "let ge = Genv.globalenv p in
      Genv.init_mem p = Some m0 \<Longrightarrow>
      Genv.find_symbol ge (prog_main p) = Some b \<Longrightarrow>
      Genv.find_funct_ptr ge b = Some f \<Longrightarrow>
      funsig f = signature_main \<Longrightarrow>
      evalinf_funcall ge m0 f [] t \<Longrightarrow>
      bigstep_program_diverges p t"

(** ** Correctness of the big-step semantics with respect to the transition semantics *)
section \<open>Bigstep to Transition\<close>

context
  fixes p :: program and ge :: genv
begin

inductive outcome_state_match :: "val \<Rightarrow> env \<Rightarrow> mem \<Rightarrow> func \<Rightarrow> cont \<Rightarrow> outcome \<Rightarrow> state \<Rightarrow> bool" where
    osm_normal:
      "outcome_state_match sp e m f k
                          Out_normal
                          (State f Sskip k sp e m)"
  | osm_exit:
      "outcome_state_match sp e m f k
                          (Out_exit n)
                          (State f (Sexit n) k sp e m)"
  | osm_return_none:
      "call_cont k' = call_cont k \<Longrightarrow>
      outcome_state_match sp e m f k
                          (Out_return None)
                          (State f (Sreturn None) k' sp e m)"
  | osm_return_some:
      "call_cont k' = call_cont k \<Longrightarrow>
      eval_expr ge sp e m a v \<Longrightarrow>
      outcome_state_match sp e m f k
                          (Out_return (Some v))
                          (State f (Sreturn (Some a)) k' sp e m)"
  | osm_tail:
      "outcome_state_match sp e m f k
                          (Out_tailcall_return v)
                          (Returnstate v (call_cont k) m)"

lemma conj_left: "(x \<Longrightarrow> y \<and> z) \<Longrightarrow> (x \<Longrightarrow> y)"
  by auto
lemma conj_right: "(x \<Longrightarrow> y \<and> z) \<Longrightarrow> (x \<Longrightarrow> z)"
  by auto

thm eval_funcall_exec_stmt.induct

lemmas exec_stmt_induct = conj_right[OF eval_funcall_exec_stmt.induct, of True, simplified]
lemmas eval_funcall_induct = conj_left[OF eval_funcall_exec_stmt.induct, of True, simplified]

end

section \<open>Additions\<close>

subsection \<open>Functions for predicates\<close>

context
  fixes ge :: genv
begin

context
  fixes sp :: val
  and e :: env
  and m :: mem
begin

fun eval_expr_fun :: "expr \<Rightarrow> val option" where
  "eval_expr_fun ( Evar ident ) = (case (ITree.get ident e) of (Some v) \<Rightarrow> Some v | _ \<Rightarrow> None)"
| "eval_expr_fun ( Econst cst ) = (case (eval_constant ge sp cst) of (Some v) \<Rightarrow> Some v | _ \<Rightarrow> None)"
| "eval_expr_fun ( Eunop op a1 ) = (case (eval_expr_fun a1) of (Some v1) \<Rightarrow> (case (eval_unop op v1) of (Some v) \<Rightarrow> Some v | _ \<Rightarrow> None) | _ \<Rightarrow> None)"
| "eval_expr_fun ( Ebinop op a1 a2 ) = (case (eval_expr_fun a1) of (Some v1) \<Rightarrow> (case (eval_expr_fun a2) of (Some v2) \<Rightarrow> (case (eval_binop op v1 v2 m) of (Some v) \<Rightarrow> Some v | _ \<Rightarrow> None) | _ \<Rightarrow> None) | _ \<Rightarrow> None)"
| "eval_expr_fun ( Eload chunk addr ) = (case (eval_expr_fun addr) of (Some vaddr) \<Rightarrow> (case (Mem.loadv chunk m vaddr) of (Some v) \<Rightarrow> Some v | _ \<Rightarrow> None) | _ \<Rightarrow> None)"

fun eval_exprlist_fun :: "expr list \<Rightarrow> val list option" where
  "eval_exprlist_fun [] = Some []"
| "eval_exprlist_fun ( a1 # al ) = (case (eval_expr_fun a1) of (Some v1) \<Rightarrow> (case (eval_exprlist_fun al) of (Some vl) \<Rightarrow> Some ( v1 # vl ) | _ \<Rightarrow> None) | _ \<Rightarrow> None)"

end

subsection \<open>Equivalences\<close>

lemma equiv_none:
  assumes "\<And>x y. Pf = Some y \<longleftrightarrow> P y"
  shows "Pf = None \<longleftrightarrow> (\<forall>y. \<not>P y)"
  using assms
  by (metis not_None_eq)

lemma eval_expr_fun_equiv:
  "eval_expr_fun sp e m a = Some v \<longleftrightarrow> eval_expr ge sp e m a v"
  apply standard
  apply (induct arbitrary: v rule: eval_expr_fun.induct)
  apply (auto split: option.splits intro: eval_expr.intros)
   apply (induct rule: eval_expr.induct)
  by auto

lemmas eval_expr_fun_equivs = eval_expr_fun_equiv equiv_none[OF eval_expr_fun_equiv]

lemma eval_exprlist_fun_equiv: "eval_exprlist_fun sp e m as = Some vs \<longleftrightarrow> eval_exprlist ge sp e m as vs"
  apply standard
   apply (induct arbitrary: vs rule: eval_exprlist_fun.induct)
  apply (auto split: option.splits intro: eval_exprlist.intros simp: eval_expr_fun_equiv)
   apply (induct rule: eval_exprlist.induct)
  by (auto split: option.splits simp: eval_expr_fun_equiv eval_expr_determ)

lemmas eval_exprlist_fun_equivs = eval_exprlist_fun_equiv equiv_none[OF eval_exprlist_fun_equiv]

lemma bool_of_val_fun_equiv: "Val.bool_of_val_func v = Some b \<longleftrightarrow> Val.bool_of_val v b"
  apply (cases v)
  by (auto simp add: Val.bool_of_val.simps)

lemmas bool_of_val_fun_equivs = bool_of_val_fun_equiv equiv_none[OF bool_of_val_fun_equiv]

lemma switch_argument_fun_equiv: "switch_argument_fun islong v = Some n \<longleftrightarrow> switch_argument islong v n"
  apply (cases v; cases islong)
  by (auto simp add: switch_argument.simps)

lemmas switch_argument_fun_equivs = switch_argument_fun_equiv equiv_none[OF switch_argument_fun_equiv]

end

subsection \<open>Determinism of semantics (assuming deterministic extcalls)\<close>

context deterministic_world
begin

context
  fixes ge :: genv
begin

lemma step_determ:
  assumes "step ge s t1 s1'" "step ge s t2 s2'"
  shows "t1 = t2 \<and> s1' = s2'"
proof -
  show ?thesis using assms(2)
    apply (cases rule: step.cases[OF assms(1)]; cases rule: step.cases[OF assms(2)])
                        apply (auto simp add: exprs_determ extcall_determ)
    using extcall_determ by blast
qed

lemma step_determ':
  assumes "step ge s t s'" 
  shows "\<And>t' s''. step ge s t' s'' = (t = t' \<and> s' = s'')"
  using step_determ assms by auto

lemma eval_funcall_exec_stmt_determ:
  "(eval_funcall ge mf fd args t1f m1'f res1 \<longrightarrow> 
    (\<forall> t2 m2' res2. eval_funcall ge mf fd args t2 m2' res2 = (t1f = t2 \<and> m1'f = m2' \<and> res1 = res2))) \<and>
  ((exec_stmt ge f sp e ms s t1s e1' m1's out1 \<longrightarrow>
    (\<forall> t2 e2' m2' out2. exec_stmt ge f sp e ms s t2 e2' m2' out2 = (t1s = t2 \<and> e1' = e2' \<and> m1's = m2' \<and> out1 = out2))))"
  apply (induction rule: eval_funcall_exec_stmt.induct; (subst eval_funcall.simps[simplified] | subst exec_stmt.simps[simplified]))
                 apply simp_all
                 prefer 8
  subgoal for f sp e m a s1 s2 v b t e' m' out
    apply (cases b)
    by (auto simp: exprs_determ intro: Val.bool_of_val_one)
  using outcome_determ exprs_determ apply (auto elim: switch_argument_determ_elim simp add: extcall_determ)
  by (metis extcall_determ)

lemma eval_funcall_determ:
  assumes "eval_funcall ge mf fd args t1f m1'f res1"
  shows "\<And>t2 m2' res2. eval_funcall ge mf fd args t2 m2' res2 = (t1f = t2 \<and> m1'f = m2' \<and> res1 = res2)"
  using eval_funcall_exec_stmt_determ assms by auto

lemma exec_stmt_determ:
  assumes "exec_stmt ge f sp e ms s t1s e1' m1's out1"
  shows "\<And>t2 e2' m2' out2. exec_stmt ge f sp e ms s t2 e2' m2' out2 = (t1s = t2 \<and> e1' = e2' \<and> m1's = m2' \<and> out1 = out2)"
  using eval_funcall_exec_stmt_determ assms by auto

interpretation transition: smallstep_determ "step ge"
  apply (unfold_locales)
  using step_determ by simp

lemma one_step_E0:
  assumes "step ge s1 E0 s1'"
    "\<exists>S. transition.star s1' t S \<and> P S"
  shows "\<exists>S. transition.star s1 t S \<and> P S"
  using assms(1) assms(2) transition.star_step by blast

lemma eval_funcall_exec_stmt_steps:
  "((eval_funcall ge m fd args t m' res \<longrightarrow>
   (\<forall> k.
   is_call_cont k \<longrightarrow>
   transition.star (Callstate fd args k m) t (Returnstate res k m')))) \<and>
  ((exec_stmt ge f sp e m s t e' m' out \<longrightarrow>
   (\<forall> k. (\<exists> S.
   transition.star (State f s k sp e m) t S \<and> outcome_state_match ge sp e' m' f k out S))))"
proof (induction rule: eval_funcall_exec_stmt.induct)
  case (eval_funcall_internal m f vargs m1 sp e t e2 m2 out vres m3)

  note star_step = transition.star_one[OF step_internal_function, OF eval_funcall_internal(1,2)]

  show ?case
  proof (standard; rule impI; goal_cases)
    case (1 k)

    obtain S where S_def:
      "transition.star (State f (fn_body f) k (Vptr sp 0) e m1) t S"
      "outcome_state_match ge (Vptr sp 0) e2 m2 f k out S"
      using eval_funcall_internal by auto

    note combined = transition.star_trans[OF star_step S_def(1), simplified]

    note star_skip = transition.star_one[OF step_skip_call]
    note star_return = transition.star_one[OF step_return]
    note star_return_0 = transition.star_one[OF step_return_0]
    note star_return_1 = transition.star_one[OF step_return_1]

    note combined_trans = transition.star_trans[OF combined, simplified]

    show ?case
      using eval_funcall_internal(3,4)
      apply (cases rule: outcome_state_match.cases[OF S_def(2)]; cases rule: is_call_cont.cases[OF 1(1)])
               apply auto
      using combined_trans star_skip is_call_cont.intros(1) apply fastforce
      using "1" combined_trans star_skip apply fastforce
      using combined_trans star_return_0 apply fastforce
      using combined_trans star_return_0 apply fastforce
      using combined_trans star_return_1 apply fastforce
      using combined_trans star_return_1 apply fastforce
      using combined apply blast
      using combined by blast
  qed
next
  case (eval_funcall_external ef m args t res m')
  then show ?case
    by (simp add: step_external_function transition.star_one)
next
  case (exec_Sskip f sp e m)
  then show ?case
    using osm_normal transition.star_refl by blast
next
  case (exec_Sassign f sp e m ident a v)
  also note transition.star_one[OF step_assign]
  ultimately show ?case
    by (meson osm_normal)
next
  case (exec_Sstore f sp e m chunk addr a vaddr v m')
  also note transition.star_one[OF step_store]
  ultimately show ?case
    by (meson osm_normal)
next
  case (exec_Scall f sp e m optid sig a bl vf vargs fd t m' vres e')
  show ?case
  proof (standard; rule one_step_E0[OF step_call, OF exec_Scall(1,2,3,6)]; goal_cases)
    case (1 k)
    show ?case
      by (metis osm_normal append_Nil2 exec_Scall.IH(5) exec_Scall.hyps(2) is_call_cont.simps step_return transition.star_one transition.star_trans)
  qed
next
  case (exec_Sbuiltin f sp e m optid ef bl t m' vargs vres e')
  then show ?case
    by (metis osm_normal step_builtin transition.star_one)
next
  case (exec_Sifthenelse f sp e m a s1 s2 v b t e' m' out)
  note step_rule = step_ifthenelse[OF this(1) this(4), of f s1 s2]
  show ?case
    by (cases b; metis append.left_neutral exec_Sifthenelse.IH(3) transition.star_step step_rule)
next
  case (exec_Sseq_continue f sp e m t s1 t1 e1 m1 s2 t2 e2 m2 out)
  show ?case
  proof (standard; rule one_step_E0[OF step_seq]; goal_cases)
    case (1 k)
    let ?k1 = "Kseq s2 k"
  
    obtain S1 where
          S1_def: "transition.star (State f s1 ?k1 sp e m) t1 S1" "outcome_state_match ge sp e1 m1 f ?k1 Out_normal S1"
      using exec_Sseq_continue.IH(2) by blast

    have "S1 = (State f Sskip ?k1 sp e1 m1)"
      apply (cases rule: outcome_state_match.cases[OF S1_def(2)])
      by auto

    then have S1_s2: "transition.star S1 E0 (State f s2 k sp e1 m1)"
      by (simp add: step_skip_seq transition.star_one)
  
    obtain S2 where
        S2_def: "transition.star (State f s2 k sp e1 m1) t2 S2" "outcome_state_match ge sp e2 m2 f k out S2"
      using exec_Sseq_continue.IH(4) by blast
  
    then show ?case
      using transition.star_trans2[OF S1_def(1) S1_s2 S2_def(1), simplified] exec_Sseq_continue(5)
      by auto
  qed
next
  case (exec_Sseq_stop f sp e m t s1 s2 e1 m1 out)
  show ?case
  proof (standard; rule one_step_E0[OF step_seq]; goal_cases)
    case (1 k)
    let ?k1 = "Kseq s2 k"
  
    obtain S where
          S_def: "transition.star (State f s1 ?k1 sp e m) t S" "outcome_state_match ge sp e1 m1 f ?k1 out S"
      using exec_Sseq_stop.IH(2) by auto

    obtain S' where S'_def: "transition.star S E0 S'" "outcome_state_match ge sp e1 m1 f k out S'"
      using S_def(2) exec_Sseq_stop(3)
      apply (cases rule: outcome_state_match.cases)
          apply auto
         apply (meson osm_exit transition.star_one step_exit_seq)
        apply (meson osm_return_none transition.star_refl)
       apply (meson osm_return_some transition.star_refl)
      by (meson osm_tail transition.star_refl)
  
    then show ?case using transition.star_trans[OF S_def(1) S'_def(1), simplified]
      by auto
  qed
next
  case (exec_Sloop_loop f sp e m s t t1 e1 m1 t2 e2 m2 out)
  show ?case
  proof (standard; rule one_step_E0[OF step_loop]; goal_cases)
    case (1 k)
    let ?k1 = "Kseq (Sloop s) k"
  
    obtain S1 where
          S1_def: "transition.star (State f s ?k1 sp e m) t1 S1" "outcome_state_match ge sp e1 m1 f ?k1 Out_normal S1"
      using exec_Sloop_loop.IH(2) by blast

    have "S1 = (State f Sskip ?k1 sp e1 m1)"
      apply (cases rule: outcome_state_match.cases[OF S1_def(2)])
      by auto

    then have S1_s2: "transition.star S1 E0 (State f (Sloop s) k sp e1 m1)"
      by (simp add: step_skip_seq transition.star_one)
  
    obtain S2 where
        S2_def: "transition.star (State f (Sloop s) k sp e1 m1) t2 S2" "outcome_state_match ge sp e2 m2 f k out S2"
      using exec_Sloop_loop.IH(4) by blast
  
    then show ?case
      using transition.star_trans2[OF S1_def(1) S1_s2 S2_def(1), simplified] exec_Sloop_loop(5)
      by blast
  qed
next
  case (exec_Sloop_stop f sp e m t s e1 m1 out)
  show ?case
  proof (standard; rule one_step_E0[OF step_loop]; goal_cases)
    case (1 k)
    let ?k1 = "Kseq (Sloop s) k"
  
    obtain S where
          S_def: "transition.star (State f s ?k1 sp e m) t S" "outcome_state_match ge sp e1 m1 f ?k1 out S"
      using exec_Sloop_stop.IH(2) by auto

    obtain S' where S'_def: "transition.star S E0 S'" "outcome_state_match ge sp e1 m1 f k out S'"
      using S_def(2) exec_Sloop_stop(3)
      apply (cases rule: outcome_state_match.cases)
          apply auto
         apply (meson osm_exit transition.star_one step_exit_seq)
        apply (meson osm_return_none transition.star_refl)
       apply (meson osm_return_some transition.star_refl)
      by (meson osm_tail transition.star_refl)

    show ?case
      using transition.star_trans[OF S_def(1) S'_def(1), simplified] S'_def(2) by auto
  qed
next
  case (exec_Sblock f sp e m s t e1 m1 out)
  show ?case
  proof (standard; rule one_step_E0[OF step_block]; goal_cases)
    case (1 k)

    note IH = allE[OF exec_Sblock(2), of "Kblock k"]

    then obtain S where S_def:
      "transition.star (State f s (Kblock k) sp e m) t S"
      "outcome_state_match ge sp e1 m1 f (Kblock k) out S"
      by blast

    obtain S' where S'_def:
      "transition.star S E0 S'"
      "outcome_state_match ge sp e1 m1 f k (outcome_block out) S'"
      apply (cases rule: outcome_state_match.cases[OF S_def(2)])
          apply auto
      using osm_normal step_skip_block transition.star_one apply blast
      subgoal for n
        apply (cases n)
        using osm_normal step_exit_block_0 transition.star_one apply fastforce
        using osm_exit step_exit_block_S transition.star_one by fastforce
      using osm_return_none transition.star_refl apply blast
      using osm_return_some transition.star_refl apply blast
      using osm_tail transition.star_refl by blast

    note combined = transition.star_trans[OF S_def(1) S'_def(1), simplified]

    then show ?case
      using S'_def(2) by auto
  qed
next
case (exec_Sexit f sp e m n)
  then show ?case
    using osm_exit transition.star_refl by blast
next
  case (exec_Sswitch f sp e m islong a cases default v n)
  then show ?case
    by (meson osm_exit step_switch transition.star_one)
next
  case (exec_Sreturn_none f sp e m)
  then show ?case
    using osm_return_none transition.star_refl by blast
next
  case (exec_Sreturn_some f sp e m a v)
  then show ?case
    using osm_return_some transition.star_refl by blast
next
  case (exec_Stailcall f sp e m sig a bl vf vargs fd t m' m'' vres)

  then have IH: "\<And>k. is_call_cont k \<Longrightarrow> transition.star (Callstate fd vargs k m') t (Returnstate vres k m'')"
    by auto

  show ?case
  proof (standard; rule one_step_E0[OF step_tailcall, OF exec_Stailcall(1,2,3,6,7)]; goal_cases)
    case (1 k)

    from IH
    show ?case
      using osm_tail by blast
  qed
qed

subsection \<open>Step Function\<close>

definition step_fun :: "state \<Rightarrow> (state * trace) option" where
  "step_fun s = (if (EX s' t. step ge s t s')
    then Some (THE (s',t). step ge s t s')
    else None)"

lemma step_fun_equivs:
  "step_fun s = Some (s', t) \<longleftrightarrow> step ge s t s'"
  "step_fun s = None \<longleftrightarrow> (\<forall>t s'. \<not>step ge s t s')"
  unfolding step_fun_def
  apply standard
  using step_determ
   apply auto
  by (smt (verit, ccfv_threshold) handy_if_lemma internal_case_prod_conv internal_case_prod_def old.prod.exhaust the_equality)

subsection \<open>Step Fun. Simps\<close>

lemmas splits = cont.split option.split val.split prod.split
lemmas equivs = step_fun_equivs eval_expr_fun_equivs eval_exprlist_fun_equivs bool_of_val_fun_equivs
  switch_argument_fun_equivs extcall_result_equiv

named_theorems step_fun_simps \<open>Simp Rules for step_fun\<close>

lemma step_fun_Sskip[step_fun_simps]: "step_fun ( State f Sskip k sp e m ) =
  (case k of
    Kseq s k' \<Rightarrow> Some (State f s k' sp e m, E0)
  | Kblock k' \<Rightarrow> Some (State f Sskip k' sp e m, E0)
  | _ \<Rightarrow> (case sp of
            (Vptr sp_b ofs) \<Rightarrow>
              (if ofs \<noteq> 0 then None else
              (case (Mem.free m sp_b 0 (fn_stackspace f)) of
                (Some m') \<Rightarrow> Some ( Returnstate Vundef k m', E0 )
              | None \<Rightarrow> None))
          | _ \<Rightarrow> None))"
  by (auto split: splits simp add: equivs step.simps)

lemma step_fun_Sassign[step_fun_simps]: "step_fun ( State f ( Sassign ident a ) k sp e m ) =
  (case (eval_expr_fun ge sp e m a) of (Some v) \<Rightarrow>
  Some (State f Sskip k sp ( ITree.set ident v e ) m, E0) | _ \<Rightarrow> None)"
  by (auto split: splits simp add: equivs step.simps)

lemma step_fun_Sstore[step_fun_simps]: "step_fun ( State f ( Sstore chunk addr a ) k sp e m ) =
  (case (eval_expr_fun ge sp e m addr) of (Some vaddr) \<Rightarrow>
  (case (eval_expr_fun ge sp e m a) of (Some v) \<Rightarrow>
  (case (Mem.storev chunk m vaddr v) of (Some m') \<Rightarrow>
  Some ( State f Sskip k sp e m', E0 ) | _ \<Rightarrow> None) | _ \<Rightarrow> None) | _ \<Rightarrow> None)"
  apply (auto split: splits simp add: equivs step.simps)
  by (metis eval_expr_determ option.distinct(1))

lemma step_fun_Scall[step_fun_simps]: "step_fun ( State f ( Scall optid sig a bl ) k sp e m ) =
  (case (eval_expr_fun ge sp e m a) of (Some vf) \<Rightarrow>
  (case (eval_exprlist_fun ge sp e m bl) of (Some vargs) \<Rightarrow>
  (case (Genv.find_funct ge vf) of (Some fd) \<Rightarrow>
  (if (funsig fd) \<noteq> sig then None else
  Some (Callstate fd vargs ( Kcall optid f sp e k ) m, E0)) | _ \<Rightarrow> None) | _ \<Rightarrow> None) | _ \<Rightarrow> None)"
  apply (auto split: splits simp add: equivs step.simps)
  using eval_expr_determ by force+

lemma step_fun_Stailcall[step_fun_simps]: "step_fun ( State f ( Stailcall sig a bl ) k sp e m ) =
  (case sp of (Vptr sp_b ofs) \<Rightarrow>
  (if ofs \<noteq> 0 then None else
  (case (eval_expr_fun ge sp e m a) of (Some vf) \<Rightarrow>
  (case (eval_exprlist_fun ge sp e m bl) of (Some vargs) \<Rightarrow>
  (case (Genv.find_funct ge vf) of (Some fd) \<Rightarrow>
  (case (Mem.free m sp_b 0 (fn_stackspace f)) of (Some m') \<Rightarrow>
  (if (funsig fd) \<noteq> sig then None else
  Some (Callstate fd vargs ( call_cont k ) m', E0)) | _ \<Rightarrow> None) | _ \<Rightarrow> None) | _ \<Rightarrow> None) | _ \<Rightarrow> None)) | _ => None)"
  apply (auto split: splits simp add: equivs step.simps)
  using eval_expr_determ by force+

schematic_goal step_fun_Sbuiltin[step_fun_simps]: "step_fun ( State f ( Sbuiltin optid ef bl ) k sp e m ) =
  (case (eval_exprlist_fun ge sp e m bl) of (Some vargs) \<Rightarrow>
  (case (external_call_result ef (Genv.to_senv ge) vargs m) of (Some (t, vres, m')) \<Rightarrow>
  Some (State f Sskip k sp (set_optvar optid vres e) m', t) | _ \<Rightarrow> None) | _ \<Rightarrow> None)"
  apply (auto split: splits simp add: equivs step.simps)
  by (metis eval_exprlist_determ option.distinct(1))

lemma step_fun_Sseq[step_fun_simps]: "step_fun ( State f ( Sseq s1 s2 ) k sp e m ) =
  Some (State f s1 ( Kseq s2 k ) sp e m, E0)"
  by (auto split: splits simp add: equivs step.simps)

lemma step_fun_Sifthenelse[step_fun_simps]: "step_fun ( State f ( Sifthenelse a s1 s2 ) k sp e m ) =
  (case (eval_expr_fun ge sp e m a) of (Some v) \<Rightarrow>
  (case (Val.bool_of_val_func v) of (Some b) \<Rightarrow>
  (Some ( State f ( if b then s1 else s2 ) k sp e m, E0)) | _ \<Rightarrow> None) | _ \<Rightarrow> None)"
  apply (auto split: splits simp add: equivs step.simps)
  using eval_expr_determ by blast+

lemma step_fun_Sloop[step_fun_simps]: "step_fun ( State f ( Sloop s ) k sp e m ) =
  Some ( State f s ( Kseq ( Sloop s ) k ) sp e m, E0)"
  by (auto split: splits simp add: equivs step.simps)

lemma step_fun_Sblock[step_fun_simps]: "step_fun ( State f ( Sblock s ) k sp e m ) =
  Some ( State f s ( Kblock k ) sp e m, E0)"
  by (auto split: splits simp add: equivs step.simps)

lemma step_fun_Sexit[step_fun_simps]: "step_fun ( State f ( Sexit n ) k sp e m ) =
  (case k of (Kseq s k') \<Rightarrow> Some ( State f ( Sexit n ) k' sp e m, E0)
           | (Kblock k') \<Rightarrow> (case n of (Suc n') \<Rightarrow> Some ( State f ( Sexit n' ) k' sp e m, E0 )
                                     | 0 \<Rightarrow> Some ( State f Sskip k' sp e m, E0))
           | _ \<Rightarrow> None)"
  by (auto split: splits nat.split simp add: equivs step.simps)

lemma step_fun_Sswitch[step_fun_simps]: "step_fun ( State f ( Sswitch islong a cases def ) k sp e m ) =
  (case (eval_expr_fun ge sp e m a) of (Some v) \<Rightarrow>
  (case (switch_argument_fun islong v) of (Some n) \<Rightarrow>
  (Some ( State f ( Sexit ( switch_target n def cases ) ) k sp e m, E0 )) | _ \<Rightarrow> None) | _ \<Rightarrow> None)"
  apply (auto split: splits simp add: equivs step.simps)
  using eval_expr_determ by blast

lemma step_fun_Sreturn[step_fun_simps]: "step_fun ( State f (Sreturn r) k sp e m ) =
  (case sp of (Vptr sp_b ofs) \<Rightarrow>
  (if ofs \<noteq> 0 then None else
  (case (Mem.free m sp_b 0 (fn_stackspace f)) of (Some m') \<Rightarrow>
  (case r of None \<Rightarrow> Some ( Returnstate Vundef ( call_cont k ) m', E0 )
          | Some a \<Rightarrow> (case (eval_expr_fun ge sp e m a) of 
                        (Some v) \<Rightarrow> Some ( Returnstate v ( call_cont k ) m', E0 )
                      | None \<Rightarrow> None)) | _ \<Rightarrow> None)) | _ \<Rightarrow> None)"
  by (auto split: splits simp add: equivs step.simps)

lemma step_fun_Slabel[step_fun_simps]: "step_fun ( State f ( Slabel lbl s ) k sp e m ) =
  Some ( State f s k sp e m, E0 )"
  by (auto split: splits simp add: equivs step.simps)

lemma step_fun_Sgoto[step_fun_simps]: "step_fun ( State f ( Sgoto lbl ) k sp e m ) =
  (case (find_label lbl (fn_body f) (call_cont k)) of (Some(s', k')) \<Rightarrow>
  Some ( State f s' k' sp e m, E0 ) | _ \<Rightarrow> None)"
  by (auto split: splits simp add: equivs step.simps)

lemma step_fun_CallstateInternal[step_fun_simps]: "step_fun ( Callstate ( Internal f ) vargs k m ) =
  (case (Mem.alloc m 0 (fn_stackspace f)) of (m', sp) \<Rightarrow>
  (Some (State f (fn_body f) k (Vptr sp 0) (set_locals (fn_vars f) (set_params vargs (fn_params f))) m', E0)))"
  by (auto split: splits simp: equivs step.simps)

lemma step_fun_CallstateExternal[step_fun_simps]: "step_fun ( Callstate ( External ef ) vargs k m ) =
  (case external_call_result ef (Genv.to_senv ge) vargs m of Some (t, vres, m') \<Rightarrow>
  Some (Returnstate vres k m', t) | _ \<Rightarrow> None)"
  by (auto split: splits simp add: equivs step.simps)

lemma step_fun_Returnstate[step_fun_simps]: "step_fun ( Returnstate v k m ) =
  (case k of ( Kcall optid f sp e k ) \<Rightarrow> Some ( State f Sskip k sp ( set_optvar optid v e ) m, E0 )
           | _ \<Rightarrow> None)"
  by (auto split: splits simp add: equivs step.simps)

declare step_fun_simps[simp]
declare step_fun_simps[code]

(* make sure the rules cover everything *)

lemma "\<exists>x. step_fun (State f s k sp e m) = x"
  by (cases s; clarify; ((subst step_fun_simps; simp)?))

lemma "\<exists>x. step_fun ( Callstate f vargs k m ) = x"
  by (cases f; clarify; ((subst step_fun_simps; simp)?))

lemma "\<exists>x. step_fun ( Returnstate v k m ) = x"
  by (((subst step_fun_simps; simp)?))

(* With Kstop/Kcall, a Sskip is equivalent to a Sreturn *)
lemma assumes "is_call_cont k" shows "step_fun ( State f Sskip k sp e m ) = step_fun ( State f (Sreturn None) k sp e m )"
  apply (cases rule: is_call_cont.cases[OF assms])
  by (auto split: val.split option.split)

end
end

end