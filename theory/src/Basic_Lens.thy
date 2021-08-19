theory Basic_Lens
imports Main "Separation_Algebra.Separation_Algebra" "../lib/Sep_Algebra_Add"
begin

datatype ('a, 's) basic_lens = BLENS (get\<^sub>b: "'s \<Rightarrow> 'a") (put\<^sub>b: "'a \<Rightarrow> 's \<Rightarrow> 's")
type_notation basic_lens (infixr "\<lhd>" 0)

section \<open>Definite Sep Algebra Values\<close>
(*
  this specifies that a sep. algebra value is 'fully defined', i.e. doesn't contain ambiguities,
  so only 0 can be disjoint with it
*)
inductive sep_definite :: "'a::sep_algebra \<Rightarrow> bool" where
  "(\<And>a'. a ## a' \<Longrightarrow> a' = 0) \<Longrightarrow> sep_definite a"

(* a sep_algebra type that is either 0 or 'definite' in the above sense *)
class definite_sep_algebra = stronger_sep_algebra +
  assumes definite: "a \<noteq> 0 \<Longrightarrow> a ## a' \<Longrightarrow> a' = 0"
begin

subclass unique_zero_sep_algebra
  apply standard
  using local.definite by auto
end

lemma definite_algebra_is_definite[iff]:
  "(a::_::definite_sep_algebra) \<noteq> 0 \<Longrightarrow> sep_definite a"
  by (simp add: definite sep_definite.intros)

instantiation tsa_opt :: (_) definite_sep_algebra
begin
instance
  apply standard
  by (simp add: sep_disj_tsa_opt_def zero_tsa_opt_def)
end

section \<open>Basic Lens\<close>

locale basic_lens =
  fixes L :: "'a \<lhd> 's"
  assumes get_put': "get\<^sub>b L (put\<^sub>b L x s) = x"
  assumes put_get': "put\<^sub>b L (get\<^sub>b L s) s = s"
  assumes put_put': "put\<^sub>b L x (put\<^sub>b L y s) = put\<^sub>b L x s"
begin

definition "get \<equiv> get\<^sub>b L"
definition "put \<equiv> put\<^sub>b L"

definition "is x s \<equiv> get s = x"

definition "update f s \<equiv> put (f (get s)) s"

definition "update_maybe f s \<equiv> case f (get s) of Some a' \<Rightarrow> Some (put a' s) | None \<Rightarrow> None"

lemmas base_defs = get_def put_def
lemmas defs = base_defs is_def[unfolded base_defs] update_def[unfolded base_defs] update_maybe_def[unfolded base_defs]
lemmas ground_defs = defs

lemma unfold:
  assumes "L \<equiv> BLENS get_f put_f"
  shows
    "get s \<equiv> get_f s" "put x s \<equiv> put_f x s" "is x s \<equiv> get_f s = x"
    "update f s \<equiv> put_f (f (get_f s)) s"
    "update_maybe f' s \<equiv> case f' (get_f s) of Some a' \<Rightarrow> Some (put_f a' s) | None \<Rightarrow> None"
  unfolding defs
  unfolding assms
  by (auto simp only: basic_lens.sel)

lemma get_put: "get (put x s) = x"
  unfolding get_def put_def using get_put' by simp

lemma put_get: "put (get s) s = s"
  unfolding get_def put_def using put_get' by simp

lemma put_put: "put x (put y s) = put x s"
  unfolding get_def put_def using put_put' by simp

lemma put_put_comp:
  "put x o put y = put x"
  by (auto simp add: put_put)

lemma is_get: "is x s \<longleftrightarrow> get s = x"
  unfolding is_def by simp

lemma is_put: "is x (put x s)"
  unfolding is_def using get_put by simp

lemma update_id:
  "update id = id" "update (\<lambda>a. a) = id"
  unfolding update_def
  using put_get by auto

lemma update_ignore:
  "update (\<lambda>_. x) = put x"
  unfolding update_def by simp

lemma get_update:
  "get (update f s) = f (get s)"
  unfolding update_def using get_put by simp

lemma update_comp:
  "update f (update g s) = update (f o g) s"
  unfolding update_def
  by (simp add: get_put put_put)

lemma update_equality:
  "update f = update f' \<longleftrightarrow> f = f'"
  unfolding update_def
  apply standard+
   apply (metis get_put)
  by simp

lemma update_maybeE[elim!]:
  assumes "update_maybe f s = Some s'"
  obtains a' where "f (get s) = Some a'" "s' = put a' s"
  using get_put assms
  unfolding update_maybe_def
  by (auto split: option.splits)

lemma update_comp':
  "update f o update g = update (f o g)"
  using update_comp
  unfolding comp_def
  by simp

lemma put_equality:
  "put a s = put a' s \<longleftrightarrow> a = a'"
  by (metis get_put)

lemmas laws = get_put put_get put_put put_put_comp is_get is_put update_id update_ignore get_update
  update_comp update_equality update_maybeE update_comp' put_equality

end

section \<open>Basic Pointer Lens\<close>

locale basic_ptr_lens =
  fixes F :: "'p \<Rightarrow> 'a \<lhd> 's" (* F for 'factory', since it produces lenses *)
  assumes is_lens: "basic_lens (F p)"
  assumes put_focused': "p \<noteq> p' \<Longrightarrow> get\<^sub>b (F p) (put\<^sub>b (F p') a s) = get\<^sub>b (F p) s"
begin
definition "get p \<equiv> basic_lens.get (F p)"
definition "put p \<equiv> basic_lens.put (F p)"

definition "is p \<equiv> \<lambda>x s. basic_lens.is (F p) x s"
definition "update p \<equiv> \<lambda>f s. basic_lens.update (F p) f s"

definition "update_maybe p \<equiv> \<lambda>f s. case f (basic_lens.get (F p) s) of Some a' \<Rightarrow> Some (basic_lens.put (F p) a' s) | None \<Rightarrow> None"

lemmas defs = get_def put_def is_def update_def update_maybe_def

lemma put_focused: "p \<noteq> p' \<Longrightarrow> get p (put p' a s) = get p s"
  by (simp add: basic_lens.get_def basic_lens.put_def get_def is_lens put_def put_focused')

lemmas laws = basic_lens.laws[OF is_lens, folded defs] put_focused

lemmas parent_defs = basic_lens.defs[OF is_lens]
lemmas ground_defs = defs[unfolded parent_defs]

lemma unfold:
  assumes "F \<equiv> \<lambda>p. (BLENS (get_f p) (put_f p))"
  shows "get p s \<equiv> get_f p s" "put p x s \<equiv> put_f p x s"
    "is p x s \<equiv> (get_f p s = x)"
    "update p f s \<equiv> put_f p (f (get_f p s)) s"
    "update_maybe p f' s \<equiv> case f' (get_f p s) of Some a' \<Rightarrow> Some (put_f p a' s) | None \<Rightarrow> None"
  unfolding ground_defs
  unfolding assms
  by (auto simp only: basic_lens.sel)

end

section \<open>Basic Lens Equivalence\<close>

locale basic_lens_equiv =
  L: basic_lens L + L': basic_lens L'
  for L  :: "'a \<lhd> 's"
  and L' :: "'b \<lhd> 't" +
  fixes embed_a :: "'v \<Rightarrow> 'a"
  fixes embed_b :: "'v \<Rightarrow> 'b"
  fixes transl_s :: "'s \<Rightarrow> 't"
  assumes get_transl: "L'.get (transl_s s) = embed_b x \<longleftrightarrow> L.get s = embed_a x"
  assumes put_transl: "L'.put (embed_b x) (transl_s s) = transl_s (L.put (embed_a x) s)"
begin

lemma is_transl: "L'.is (embed_b x) (transl_s s) = L.is (embed_a x) s"
  by (simp add: L'.is_def L.is_def get_transl)

lemmas laws = get_transl put_transl is_transl

end

section \<open>Basic Pointer Lens Equivalence\<close>

locale basic_ptr_lens_equiv =
  F: basic_ptr_lens F + F': basic_ptr_lens F'
  for F  :: "'p \<Rightarrow> 'a \<lhd> 's"
  and F' :: "'p \<Rightarrow> 'b \<lhd> 't" +
  fixes embed_a :: "'v \<Rightarrow> 'a"
  fixes embed_b :: "'v \<Rightarrow> 'b"
  fixes transl_s :: "'s \<Rightarrow> 't"
  assumes is_lens_equiv: "basic_lens_equiv (F p) (F' p) embed_a embed_b transl_s"
begin

lemmas laws = basic_lens_equiv.laws[OF is_lens_equiv, folded F.defs, folded F'.defs]

end

section \<open>Composition\<close>

locale compose_basic_lenses =
  L_inner: basic_lens L_inner +
  L_outer: basic_lens L_outer
  for L_inner :: "'a \<lhd> 's"
  and L_outer :: "'s \<lhd> 't"
begin
definition "L \<equiv> BLENS (L_inner.get o L_outer.get) (\<lambda>a. L_outer.update (L_inner.put a))"

lemma update_put_get:
  "L_outer.update (L_inner.put (L_inner.get (L_outer.get s))) s = s"
  using L_inner.put_get L_outer.put_get L_outer.update_def by auto

sublocale basic_lens L
  unfolding L_def
  apply standard
  by (auto simp: L_inner.laws L_outer.laws update_put_get)

lemmas compose_defs = defs[unfolded L_def, simplified, folded L_def]
lemmas compose_ground_defs = compose_defs[unfolded L_inner.ground_defs, unfolded L_outer.ground_defs]

schematic_goal inner_unfold:
  assumes "L_inner \<equiv> BLENS get_f_inner put_f_inner"
  shows
    "get s \<equiv> ?get" "put a s \<equiv> ?put" "is a s \<equiv> ?is"
    "update f s \<equiv> ?update" "update_maybe f' s \<equiv> ?update_maybe"
  unfolding unfold[OF L_def[abs_def]]
  unfolding L_inner.unfold[OF assms]
  by auto

schematic_goal outer_unfold:
  assumes "L_outer \<equiv> BLENS get_f_outer put_f_outer"
  shows
    "get s \<equiv> ?get" "put a s \<equiv> ?put" "is a s \<equiv> ?is"
    "update f s \<equiv> ?update" "update_maybe f' s \<equiv> ?update_maybe"
  unfolding unfold[OF L_def[abs_def]]
  unfolding L_outer.unfold[OF assms]
  by auto

schematic_goal compose_unfold:
  assumes "L_inner \<equiv> BLENS get_f_inner put_f_inner"
  assumes "L_outer \<equiv> BLENS get_f_outer put_f_outer"
  shows
    "get s \<equiv> ?get" "put a s \<equiv> ?put" "is a s \<equiv> ?is"
    "update f s \<equiv> ?update" "update_maybe f' s \<equiv> ?update_maybe"
  unfolding unfold[OF L_def[abs_def]]
  unfolding L_inner.unfold[OF assms(1)] L_outer.unfold[OF assms(2)]
  by auto

end

subsection \<open>Pointer Lens Composition\<close>

locale compose_basic_ptr_lens =
  F_inner: basic_ptr_lens F_inner +
  L_outer: basic_lens L_outer
  for F_inner :: "'p \<Rightarrow> 'a \<lhd> 's"
  and L_outer :: "'s \<lhd> 't"
begin
definition "F p \<equiv> BLENS (F_inner.get p o L_outer.get) (\<lambda>a. L_outer.update (F_inner.put p a))"

lemma update_put_get:
  "L_outer.update (F_inner.put p (F_inner.get p (L_outer.get s))) s = s"
  by (simp add: F_inner.laws(2) L_outer.put_get L_outer.update_def)

sublocale basic_ptr_lens F
  unfolding F_def
  apply standard
  by (auto simp: F_inner.laws L_outer.laws update_put_get)

lemmas compose_defs = ground_defs[unfolded F_def, simplified, folded F_def]
lemmas compose_ground_defs = compose_defs[unfolded F_inner.ground_defs, unfolded L_outer.ground_defs]

schematic_goal compose_unfold:
  assumes "F_inner \<equiv> \<lambda>p. BLENS (get_f_inner p) (put_f_inner p)"
  assumes "L_outer \<equiv> BLENS get_f_outer put_f_outer"
  shows
    "get p s \<equiv> ?get" "put p a s \<equiv> ?put" "is p a s \<equiv> ?is"
    "update p f s \<equiv> ?update" "update_maybe p f' s \<equiv> ?update_maybe"
  unfolding unfold[OF F_def[abs_def]]
  unfolding F_inner.unfold[OF assms(1)] L_outer.unfold[OF assms(2)]
  by auto

schematic_goal compose_inner_unfold:
  assumes "F_inner \<equiv> \<lambda>p. BLENS (get_f_inner p) (put_f_inner p)"
  shows
    "get p s \<equiv> ?get" "put p a s \<equiv> ?put" "is p a s \<equiv> ?is"
    "update p f s \<equiv> ?update" "update_maybe p f' s \<equiv> ?update_maybe"
  unfolding unfold[OF F_def[abs_def]]
  unfolding F_inner.unfold[OF assms(1)]
  by auto

end

section \<open>Combination\<close>

locale combine_basic_lenses = left: basic_lens Ll + right: basic_lens Lr
  for Ll :: "'al \<lhd> 's"
  and Lr :: "'ar \<lhd> 's"  +
assumes separate:
  "right.get (left.put al s) = right.get s"
  "left.get (right.put ar s) = left.get s"
  "left.put al (right.put ar s) = right.put ar (left.put al s)"
begin

definition "L \<equiv> BLENS (\<lambda>s. (left.get s, right.get s)) (\<lambda>(vl', vr'). left.put vl' o right.put vr')"

sublocale basic_lens L
  unfolding L_def
  apply standard
  by (auto simp: left.laws right.laws separate)

lemmas combine_defs = ground_defs[unfolded L_def, simplified basic_lens.sel, folded L_def]
lemmas combine_ground_defs = combine_defs[unfolded left.ground_defs, unfolded right.ground_defs]
end

section \<open>Sep Algebra Lens\<close>

locale sep_algebra_lens = basic_lens L
  for L :: "'a::stronger_sep_algebra \<lhd> 's::stronger_sep_algebra" +
  assumes get_zero: "get 0 = 0"
  assumes put_zero: "put 0 0 = 0"
  assumes get_split: "x ## y \<Longrightarrow> get (x + y) = get x + get y"
  assumes put_split: "x ## y \<Longrightarrow> ax ## ay \<Longrightarrow> put (ax + ay) (x + y) = put ax x + put ay y"
  assumes disj_consistent:
    "x ## y \<Longrightarrow> get x ## get y"
    "x ## y \<Longrightarrow> ax ## ay \<Longrightarrow> put ax x ## put ay y"
    "put 0 x ## put 0 y \<Longrightarrow> ax ## ay \<Longrightarrow> put ax x ## put ay y"
  assumes zero_split: "x ## y \<Longrightarrow> x + y = put (get x + get y) 0 \<Longrightarrow> x = put (get x) 0"
begin
definition lift :: "'a \<Rightarrow> 's" where
  "lift a \<equiv> put a 0"

definition del :: "'s \<Rightarrow> 's" where
  "del \<equiv> put 0"

definition discard_rest :: "'s \<Rightarrow> 's" where
  "discard_rest s \<equiv> lift (get s)"

definition zero_otherwise :: "'s \<Rightarrow> bool" where
  "zero_otherwise s \<equiv> s = discard_rest s"

lemmas sep_defs = lift_def discard_rest_def[unfolded lift_def]
  zero_otherwise_def[unfolded discard_rest_def, unfolded lift_def]
lemmas sep_ground_defs = sep_defs[unfolded defs]

lemma zero_zero: "zero_otherwise 0"
  unfolding zero_otherwise_def discard_rest_def lift_def
  by (simp add: get_zero put_zero)

lemma lift_zero: "lift 0 = 0"
  unfolding lift_def
  by (simp add: put_zero)

lemma get_lift: "get (lift a) = a"
  unfolding lift_def
  by (simp add: get_put)

lemma zero_lift: "zero_otherwise (lift a)"
  unfolding zero_otherwise_def discard_rest_def lift_def
  by (simp add: get_put)

lemma zero_if_zero_otherwise: "get fa = 0 \<Longrightarrow> zero_otherwise fa \<Longrightarrow> fa = 0"
  unfolding zero_otherwise_def discard_rest_def lift_def
  by (simp add: put_zero)

lemma zero_otherwiseE:
  "zero_otherwise s \<Longrightarrow> s = lift (get s)"
  unfolding zero_otherwise_def discard_rest_def lift_def by simp

lemma zero_split': "x ## y \<Longrightarrow> zero_otherwise (x + y) \<Longrightarrow> zero_otherwise x"
  by (simp add: discard_rest_def get_split lift_def zero_otherwise_def zero_split)

lemma lift_disj: "ax ## ay \<Longrightarrow> lift ax ## lift ay"
  unfolding lift_def
  by (simp add: disj_consistent(2) put_zero)

lemma lift_split: "ax ## ay \<Longrightarrow> lift (ax + ay) = lift ax + lift ay"
  unfolding lift_def
  by (metis disjoint_zero_sym put_split sep_add_zero_sym)

lemma split_zero: "ax ## ay \<Longrightarrow> get s = ax + ay \<Longrightarrow> zero_otherwise s \<Longrightarrow> s = lift ax + lift ay"
  unfolding zero_otherwise_def discard_rest_def lift_def
  using lift_def lift_split by auto

lemma lift_del_disj:
  "lift a ## del s"
  by (simp add: del_def lift_def put_zero sep_algebra_lens.disj_consistent(3) sep_algebra_lens_axioms)

lemma del_put: "del (put v s) = del (put v' s)"
  by (simp add: del_def put_put)

lemma del_zero: "zero_otherwise s \<Longrightarrow> del s = 0"
  by (metis del_def del_put sep_ground_defs(3) put_def put_zero)

lemma lift_get_disj: "lift a ## s \<longleftrightarrow> a ## get s"
  unfolding lift_def
  by (metis disj_consistent(1) disj_consistent(2) disjoint_zero_sym get_put put_get)

lemma del_lift_definite:
  assumes "sep_definite a" (* meaning: a is completely defined, only 0 can be disj with it *)
  shows "lift a ## s \<Longrightarrow> del (lift a + s) = s"
  apply (rule sep_definite.cases[OF assms])
  by (metis del_def lift_def lift_get_disj put_get put_put put_split sep_add_zero_sym sep_disj_commuteI sep_disj_zero)

lemma is_split: "is a s \<Longrightarrow> s = lift a + del s"
  by (metis basic_lens.put_get basic_lens_axioms del_def disjoint_zero_sym is_def lift_def put_split sep_add_zero sep_add_zero_sym sep_disj_zero)

lemmas sep_laws = get_zero put_zero get_split put_split disj_consistent zero_split
  zero_zero lift_zero get_lift zero_lift zero_if_zero_otherwise zero_split' lift_disj lift_split split_zero
  lift_del_disj del_put del_zero del_lift_definite is_split

lemma lift_alt_def: "s = lift a \<longleftrightarrow> get s = a \<and> zero_otherwise s"
  using discard_rest_def get_lift zero_otherwise_def by auto

end

section \<open>Sep Algebra Pointer Lens\<close>

locale sep_algebra_ptr_lens = basic_ptr_lens F
  for F :: "'p \<Rightarrow> 'a::stronger_sep_algebra \<lhd> 's::stronger_sep_algebra" +
  assumes is_sep_lens: "sep_algebra_lens (F p)"
begin

definition lift :: "'p \<Rightarrow> 'a \<Rightarrow> 's" where
  "lift p = sep_algebra_lens.lift (F p)"

definition zero_otherwise :: "'p \<Rightarrow> 's \<Rightarrow> bool" where
  "zero_otherwise p \<equiv> sep_algebra_lens.zero_otherwise (F p)"

definition del :: "'p \<Rightarrow> 's \<Rightarrow> 's" where
  "del p = sep_algebra_lens.del (F p)"

lemmas underlying_ground_defs = sep_algebra_lens.sep_ground_defs[OF is_sep_lens]

lemmas sep_defs = lift_def del_def zero_otherwise_def
lemmas sep_ground_defs = sep_defs[unfolded underlying_ground_defs]

lemmas sep_laws = sep_algebra_lens.sep_laws[OF is_sep_lens, folded defs, folded sep_defs]
end

section \<open>Compose Sep Algebra Pointer Lens\<close>

locale compose_sep_algebra_ptr_lens =
  F_inner: sep_algebra_ptr_lens F_inner +
  L_outer: sep_algebra_lens L_outer
  for F_inner :: "'p \<Rightarrow> 'a::stronger_sep_algebra \<lhd> 's::stronger_sep_algebra"
  and L_outer :: "'s::stronger_sep_algebra \<lhd> 't::stronger_sep_algebra"
begin

sublocale compose_basic_ptr_lens F_inner L_outer
  by standard

lemma have_lens_axioms: "\<And>p. sep_algebra_lens_axioms (F p)"
  unfolding sep_algebra_lens_axioms_def parent_defs
  apply (simp add: F_def L_outer.update_def F_inner.laws L_outer.laws)
  by (smt (z3) F_inner.sep_laws(1) F_inner.sep_laws(2) F_inner.sep_laws(3) F_inner.sep_laws(4) F_inner.sep_laws(5) F_inner.sep_laws(6) F_inner.sep_laws(7) F_inner.sep_laws(8) L_outer.get_def L_outer.get_put' L_outer.get_split L_outer.get_zero L_outer.put_def L_outer.put_put' L_outer.put_split L_outer.put_zero L_outer.sep_laws(5) L_outer.sep_laws(6) L_outer.zero_split)

sublocale sep_algebra_ptr_lens F
  unfolding sep_algebra_ptr_lens_def
  apply standard
   apply (simp add: basic_ptr_lens_axioms)
  unfolding sep_algebra_ptr_lens_axioms_def sep_algebra_lens_def
  apply standard
  apply standard
  by (auto simp add: is_lens have_lens_axioms)
end

section \<open>Lens-Assertion Connection\<close>

locale lens_assertion =
  concrete: basic_ptr_lens Fc + abstract: sep_algebra_ptr_lens F\<alpha> +
  basic_ptr_lens_equiv Fc F\<alpha> embed_c embed_\<alpha> \<alpha>
  for Fc :: "'p \<Rightarrow> 'vc \<lhd> 'c" (* access to elements in concrete realm *)
  and F\<alpha> :: "'p \<Rightarrow> 'va::stronger_sep_algebra \<lhd> 'a::stronger_sep_algebra" (* access to elements in abstract realm *)
  and embed_c :: "'v \<Rightarrow> 'vc"
  and embed_\<alpha> :: "'v \<Rightarrow> 'va"
  and \<alpha> :: "'c \<Rightarrow> 'a" +
assumes embed_\<alpha>_notnull:
  "\<not>(\<exists>v. embed_\<alpha> v = va) \<Longrightarrow> va = 0"
assumes valid_embed: "sep_definite (embed_\<alpha> v)"
fixes is_null_value :: "'vc \<Rightarrow> bool"
assumes null_value: "is_null_value vc \<longleftrightarrow> \<not>(\<exists>v. embed_c v = vc)"
begin

lemma abstract_is_null: "is_null_value (concrete.get p s) \<Longrightarrow> abstract.get p (\<alpha> s) = 0"
  apply (simp add: null_value)
  using laws(1) embed_\<alpha>_notnull
  by metis

(* the abstract state that models exactly the p\<rightarrow>v relationship *)
definition exact_is :: "'p \<Rightarrow> 'v \<Rightarrow> 'a" where
  "exact_is p v \<equiv> abstract.lift p (embed_\<alpha> v)"

(* the 'rest' of an abstract state without any information about p *)
definition rest_is :: "'p \<Rightarrow> 'a \<Rightarrow> 'a" where
  "rest_is p \<equiv> abstract.del p"

lemma exact_rest_disj: "exact_is p v ## rest_is p m"
  unfolding exact_is_def rest_is_def
  by (simp add: abstract.sep_laws)

lemma rest_filter: "exact_is p v ## y \<Longrightarrow> rest_is p (exact_is p v + y) = y"
  unfolding exact_is_def rest_is_def
  by (simp add: abstract.sep_laws(21) valid_embed)

lemma rest_set_determ: "rest_is p (abstract.put p v m) = rest_is p (abstract.put p v' m)"
  unfolding rest_is_def
  by (simp add: abstract.sep_laws)

lemma rest_is_0:
  assumes "is_null_value (concrete.get p c)"
  shows "rest_is p (\<alpha> c) = \<alpha> c"
  unfolding rest_is_def
  by (metis abstract.laws(2) abstract.laws(6) abstract.sep_laws(10) abstract.sep_laws(22) abstract_is_null assms sep_add_zero_sym)

definition assn_is :: "'p \<Rightarrow> 'v \<Rightarrow> 'a \<Rightarrow> bool" where
  "assn_is p v \<equiv> EXACT (exact_is p v)"

lemma assn_is_split:
  "(assn_is p v ** F) a \<longleftrightarrow> a = exact_is p v + rest_is p a \<and> F (rest_is p a)"
  unfolding assn_is_def
  apply standard
   apply (erule sep_conjE)
   apply (simp add: pred_lift_extract_simps(2) rest_filter)
  by (metis EXACT_def exact_rest_disj sep_conjI)

lemma assn_is_concrete: 
  "(assn_is p v ** F) (\<alpha> c) \<longleftrightarrow> concrete.is p (embed_c v) c \<and> F (rest_is p (\<alpha> c))"
  unfolding assn_is_split
  by (metis abstract.del_def abstract.ground_defs(1) abstract.is_lens abstract.is_sep_lens abstract.laws(5) abstract.parent_defs(1) abstract.sep_laws(11) abstract.sep_laws(22) abstract.sep_laws(3) basic_lens.get_put exact_is_def laws(3) lens_assertion.exact_rest_disj lens_assertion_axioms rest_is_def sep_algebra_lens.del_def)

lemma assn_is_update:
  assumes "(assn_is p v \<and>* F) (\<alpha> c)"
  shows "(assn_is p v' \<and>* F) (\<alpha> (concrete.put p (embed_c v') c))"
  by (metis abstract.del_def abstract.is_sep_lens abstract.laws(3) abstract.put_def assms(1) assn_is_concrete concrete.laws(6) laws(2) rest_is_def sep_algebra_lens.del_def)

lemma assn_is_create:
  assumes "is_null_value (concrete.get p c)"
  assumes "F (\<alpha> c)"
  shows "(assn_is p v' \<and>* F) (\<alpha> (concrete.put p (embed_c v') c))"
  unfolding assn_is_concrete
  by (metis abstract.laws(2) assms(1) assms(2) concrete.laws(6) laws(2) rest_is_0 rest_set_determ)

lemma assn_is_destroy:
  assumes "is_null_value v'"
  assumes "(assn_is p v \<and>* F) (\<alpha> c)"
  shows "F (\<alpha> (concrete.put p v' c))"
  unfolding assn_is_concrete
  by (metis abstract.laws(2) assms(1) assms(2) assn_is_split concrete.laws(1) concrete.laws(3) laws(2) rest_is_0 rest_set_determ)

end

locale compose_lens_assertion =
  base: lens_assertion Fc F\<alpha> + Lc: basic_lens Lc + L\<alpha>: sep_algebra_lens L\<alpha>
  for Fc :: "'p \<Rightarrow> 'vc \<lhd> 'c"
  and F\<alpha> :: "'p \<Rightarrow> 'va::stronger_sep_algebra \<lhd> 'a::stronger_sep_algebra"
  and Lc :: "'c \<lhd> 'fc"
  and L\<alpha> :: "'a \<lhd> 'fa::stronger_sep_algebra" +
  fixes \<alpha>_full :: "'fc \<Rightarrow> 'fa"
  assumes \<alpha>s: "L\<alpha>.get (\<alpha>_full s) = \<alpha> (Lc.get s)" "L\<alpha>.put (\<alpha> a) (\<alpha>_full s) = \<alpha>_full (Lc.put a s)"
begin

sublocale concrete: compose_basic_ptr_lens Fc Lc
  by standard

sublocale abstract: compose_sep_algebra_ptr_lens F\<alpha> L\<alpha>
  by standard

sublocale lens_assertion concrete.F abstract.F embed_c embed_\<alpha> \<alpha>_full
  unfolding lens_assertion_def basic_ptr_lens_equiv_def basic_ptr_lens_equiv_axioms_def basic_lens_equiv_def
  apply (auto simp add: concrete.basic_ptr_lens_axioms abstract.sep_algebra_ptr_lens_axioms abstract.basic_ptr_lens_axioms
      concrete.is_lens abstract.is_lens)
  unfolding basic_lens_equiv_axioms_def
  apply (auto simp: concrete.parent_defs abstract.parent_defs)
     apply (auto simp: concrete.F_def abstract.F_def L\<alpha>.update_def Lc.update_def \<alpha>s base.laws)
  using base.lens_assertion_axioms lens_assertion.axioms(4) by blast

end

section \<open>Common Interpretations\<close>

definition func_lens :: "'p \<Rightarrow> ('v \<lhd> 'p \<Rightarrow> 'v)" where
  "func_lens \<equiv> \<lambda>p. BLENS (\<lambda>f. f p) (\<lambda>v' f. f(p := v'))"

interpretation func_lens: basic_ptr_lens func_lens
  unfolding func_lens_def
  apply standard
  by auto

lemmas func_lens_unfold = func_lens.unfold[OF func_lens_def]

abbreviation sep_algebra_func_lens :: "'p \<Rightarrow> ('v::unique_zero_sep_algebra \<lhd> 'p \<Rightarrow> 'v)" where
  "sep_algebra_func_lens \<equiv> func_lens"

interpretation sep_algebra_func_lens: sep_algebra_ptr_lens sep_algebra_func_lens
  unfolding sep_algebra_ptr_lens_def
  apply standard
proof -
  show "basic_ptr_lens sep_algebra_func_lens"
    by (simp add: func_lens.basic_ptr_lens_axioms)

  note unfold = basic_ptr_lens.parent_defs[OF this]

  show "sep_algebra_ptr_lens_axioms sep_algebra_func_lens"
    apply standard
    unfolding unfold
              apply (auto simp: func_lens_def)
      apply (simp add: sep_disj_funD)
     apply (metis fun_upd_upd sep_disj_fun_updI)
    unfolding plus_fun_def zero_fun_def sep_disj_fun_def
    apply standard
    by (metis fun_upd_other fun_upd_same unique_zero_simps(4))
qed

lemmas sep_algebra_func_lens_unfold = func_lens_unfold

end