#!/usr/bin/env python3

import re
import itertools
from lark import Lark
import lark

import transl_simple

lark_common = \
"""
_separated{x, sep}: x (sep x)*

IDENT: /[\w']+/

%ignore /\s+/ // Disregard spaces

"""

lark_typexpr_def = \
"""
typexpr: _LPAR_NOCOMMENT typexpr _RPAR_NOCOMMENT -> parenthesized
				| typexpr ("*" typexpr)+ -> tuple
				| TYPECONSTR typexpr? -> constr

TYPECONSTR: [MODULE_NAME "."] TYPECONSTR_NAME
MODULE_NAME: CAPITALIZED_IDENT
TYPECONSTR_NAME: IDENT

CAPITALIZED_IDENT: /[A-Z][A-Za-z0-9_']*/
LOWERCASE_IDENT: /[a-z_][A-Za-z0-9_']*/

_LPAR_NOCOMMENT: /\((?!\*)/
_RPAR_NOCOMMENT: /(?<!\*)\)/
"""

def match_tree_type(t, ty):
		if isinstance(t, lark.Tree):
				if t.data == ty:
						return True
		elif isinstance(t, lark.Token):
				if t.type == ty:
						return True
		return False

class Typexpr:
		def __init__(self, t):
				self.is_parenthesized = match_tree_type(t, "parenthesized")
				self.is_typeconstr = match_tree_type(t, "constr")
				self.is_tuple = match_tree_type(t, "tuple")

				assert (self.is_parenthesized + self.is_typeconstr + self.is_tuple) == 1

				cs = t.children
				if self.is_parenthesized:
						self.child = Typexpr(cs[0])
				if self.is_typeconstr:
						self.full_name = cs[0]

						if "." in self.full_name:
								self.module, self.typeconstr = self.full_name.split(".")
						else:
								self.module, self.typeconstr = "", self.full_name

						self.typeconstr_args = list(map(Typexpr, cs[1:]))
				if self.is_tuple:
						self.children = list(map(Typexpr, cs))

		def translate(self, space_in_quotes = False):
			if self.is_parenthesized:
				return self.child.translate(space_in_quotes)

			if self.is_typeconstr:
				t = " ".join([arg.translate(False) for arg in self.typeconstr_args] + [transl_simple.replace_token(self.full_name)])

			if self.is_tuple:
				t = " * ".join(c.translate(False) for c in self.children)

			if " " in t:
				if space_in_quotes:
					return f'"{t}"'
				else:
					return f'({t})'
			else:
				return t

lark_func_def = \
"""
// first, parse func definition into INNERFUNC terminal
func_def: _func_start IDENT arg+ _struct_hint? [":" ret] ":=" INNERFUNC "."

_func_start: "Definition"|"Fixpoint"

arg: "(" name+ ":" typexpr ")"
name: IDENT
ret: typexpr

_struct_hint: "{" IDENT+ "}"

// then, try parsing contents further with inner_func
inner_func: "match" _separated{item, ","} "with" case+ "end"
case: "|" _separated{pattern, ","} "=>" NOT_NEWLINE

item: IDENT

pattern: _pattern_part+
!_pattern_part: "(" _pattern_part+ ")" | PATTERN_PART

INNERFUNC: /.+?(?=\.$)/ms
PATTERN_PART: /[\w:']+/
NOT_BRACE: /[^())]+/
NOT_NEWLINE: /.+/
"""

"""
Inductive init_data: Type :=
	| Init_int8: int -> init_data
	| Init_int16: int -> init_data
	| Init_int32: int -> init_data
	| Init_int64: int64 -> init_data
	| Init_float32: float32 -> init_data
	| Init_float64: float -> init_data
	| Init_space: Z -> init_data
	| Init_addrof: ident -> ptrofs -> init_data. 
"""

lark_type_def = \
"""
type_def: "Inductive" IDENT ":" "Type" ":=" constr_decl+

constr_decl: "|" CONSTRUCTOR_NAME [":" _separated{typexpr_start, "->"}] ["."] [comment]

typexpr_start: typexpr

comment: "(**r" /.+(?=\s*\*\))/ "*)"

CONSTRUCTOR_NAME: IDENT
"""

"""
Inductive eval_expr: expr -> val -> Prop :=
  | eval_Evar: forall id v,
      PTree.get id e = Some v ->
      eval_expr (Evar id) v
  | eval_Econst: forall cst v,
      eval_constant sp cst = Some v ->
      eval_expr (Econst cst) v
  | eval_Eunop: forall op a1 v1 v,
      eval_expr a1 v1 ->
      eval_unop op v1 = Some v ->
      eval_expr (Eunop op a1) v
  | eval_Ebinop: forall op a1 a2 v1 v2 v,
      eval_expr a1 v1 ->
      eval_expr a2 v2 ->
      eval_binop op v1 v2 m = Some v ->
      eval_expr (Ebinop op a1 a2) v
  | eval_Eload: forall chunk addr vaddr v,
      eval_expr addr vaddr ->
      Mem.loadv chunk m vaddr = Some v ->
      eval_expr (Eload chunk addr) v.
"""

lark_inductive_def =\
"""
inductive_def: "Inductive" IDENT ":" _separated{param_type, "->"} ":=" rule_decl+

param_type: typexpr

rule_decl: "|" RULE_NAME ":" ["forall" rule_var+ ","] _separated{rule_part, "->"} ["."]

rule_var: IDENT
rule_part: ind_term

ind_term: QUAL_IDENT ind_term*
		| "(" ind_term+ ")" -> parenthesized
		| "(" _separated{ind_term, ","} ")" -> tuple
		| ind_term OPERATOR ind_term -> op
		| RECORD_ACCESS -> record_access

OPERATOR: /[=:*<>]+/
QUAL_IDENT: /([\w']+\.)?[\w']+/
RECORD_ACCESS: /[\w']+\.\([\w']+\)/
RULE_NAME: IDENT
"""

class InductiveTerm:
	def __init__(self, t):
		self.is_qual_id = match_tree_type(t, "ind_term")
		self.is_parenthesized = match_tree_type(t, "parenthesized")
		self.is_op = match_tree_type(t, "op")
		self.is_record_access = match_tree_type(t, "record_access")
		self.is_tuple = match_tree_type(t, "tuple")


		assert (self.is_qual_id + self.is_parenthesized + self.is_op + self.is_record_access + self.is_tuple == 1)

		self.t = t

	def translate(self):
		if self.is_parenthesized:
			return "({})".format(" ".join(InductiveTerm(c).translate() for c in self.t.children))
		if self.is_tuple:
			return "({})".format(", ".join(InductiveTerm(c).translate() for c in self.t.children))
		elif self.is_op:
			return "{} {} {}".format(
				InductiveTerm(self.t.children[0]).translate(),
				transl_simple.replace(self.t.children[1]),
				InductiveTerm(self.t.children[2]).translate())
		elif self.is_record_access:
			return transl_simple.replace(self.t.children[0])
		else:
			t = transl_simple.replace(self.t.children[0])
			if (len(self.t.children) > 1):
				t += " " + " ".join(InductiveTerm(c).translate() for c in self.t.children[1:])

			return t

lark_term_def = \
"""
term: "forall" binders "," term -> forall
		| "fun" binders "=>" term -> lambda
		| "if" term "then" term "else" term -> if
		| term term+ -> application
		| "match" _separated{match_item, ","} "with" ["|"] _separated{equation, "|"} "end" -> match
		| QUALID -> qualid
		| "_" -> dummy
		| "(" term ")" -> parenthesized

binders: IDENT+

match_item: term
equation: _separated{mult_pattern, "|"} "=>" term

mult_pattern: _separated{pattern, ","}

pattern: QUALID pattern* -> qualid | "(" _separated{or_pattern, ","} ")" -> tuple
or_pattern: _separated{pattern, "|"}

QUALID: /[\w']+([\w'.]+[\w'])?/
"""

def all_equal(l):
	return l.count(l[0]) == len(l)

class Pattern:
	def __init__(self, t):
		self.type = t.data
		self.children = t.children

		assert self.type in ["equation", "mult_pattern", "tuple", "or_pattern", "qualid"]

		if self.type == "equation":
			sub_patterns = t.children[:-1]
		elif self.type == "qualid":
			sub_patterns = t.children[1:]
		else:
			sub_patterns = t.children

		self.sub = [Pattern(sp).resulting_patterns() for sp in sub_patterns]

	def resulting_patterns(self):
		if self.type == "qualid":
			qi = transl_simple.replace_token(self.children[0])
			sub_prod = itertools.product([qi], *self.sub)
			return [" ".join(prod) for prod in sub_prod]

		if self.type == "tuple":
			sub_prod = itertools.product(*self.sub)
			return ["({}".format(", ".join(prod)) for prod in sub_prod]

		if self.type == "or_pattern":
			return itertools.chain(*self.sub)

		if self.type == "mult_pattern":
			sub_prod = itertools.product(*self.sub)
			return [tuple(prod) for prod in sub_prod]

		if self.type == "equation":
			assert all_equal([len(t) for t in self.sub])
			return itertools.chain(*self.sub)

class Term:
	def __init__(self, t):
		self.type = t.data
		self.children = t.children

		assert self.type in ["forall", "lambda", "if", "application", "match", "qualid", "dummy", "parenthesized"]

		self.match_items = [Term(mi.children[0]).translate() for mi in t.find_data("match_item")]
		self.equations = [(Pattern(eq).resulting_patterns(), Term(eq.children[-1]).translate()) for eq in t.find_data("equation")]

	def translated_match_items(self):
		assert self.type == "match"
		return self.match_items

	def translated_equations(self):
		assert self.type == "match"
		return self.equations

	def translate(self):
		if self.type == "forall":
			binders = self.children[0]
			return "∀{}. {}".format(" ".join(binders), Term(self.children[1]).translate())

		if self.type == "lambda":
			binders = self.children[0]
			return "λ{}. {}".format(" ".join(binders), Term(self.children[1]).translate())

		if self.type == "if":
			terms = [Term(c) for c in self.children]
			return "(if {} then {} else {})".format(*[t.translate() for t in terms])

		if self.type == "application":
			terms = [Term(c) for c in self.children]
			return " ".join(t.translate() for t in terms)

		if self.type == "match":
			case = "case ({}) of ".format(", ".join(self.match_items))
			cases = []
			for patterns, term in self.equations:
				for pattern in patterns:
					cases.append("({}) ⇒ {}".format(", ".join(pattern), term))

			return "(case ({}) of {})".format(", ".join(self.match_items), " | ".join(cases))

		if self.type == "qualid":
			return transl_simple.replace_token(self.children[0])

		if self.type == "dummy":
			return "_"

		if self.type == "parenthesized":
			return "({})".format(Term(self.children[0]).translate())

	def translate_match_to_fun(self, func_name, func_vars):
		assert self.type == "match"

		mi_order = []
		for mi in self.match_items:
			assert mi in func_vars
			mi_order.append(func_vars.index(mi))

		cases = []
		for match_patterns, term in self.equations:
			for match_pattern in match_patterns:
				var_patterns = []

				for fv in func_vars:
					if fv in self.match_items:
						corresp_pattern = match_pattern[self.match_items.index(fv)]
					else:
						corresp_pattern = fv

					if " " in corresp_pattern:
						corresp_pattern = "({})".format(corresp_pattern)

					var_patterns.append(corresp_pattern)

				cases.append('"{} {} = {}"'.format(func_name, " ".join(var_patterns), term))

		return "  " + "\n| ".join(cases)


lark_combined = \
"""
start: _def+
_def: func_def | type_def | inductive_def
""" + lark_common + lark_typexpr_def + lark_func_def + lark_type_def + lark_inductive_def

def_parser = Lark(lark_combined)
innerfunc_parser = Lark(lark_combined, start="inner_func")


def transl_func(func_name, arg_names, arg_types, ret_type, inner_func):
	types = " ⇒ ".join(arg_types + [ret_type])
	transl = f'fun {func_name} :: "{types}" where\n'

	try:
		res = innerfunc_parser.parse(inner_func)

		# print(res.pretty())

		item_pos = []
		for item in res.find_data("item"):
			item_pos.append(arg_names.index(item.children[0].value))

		cases = []

		for case in res.find_data("case"):
			args_case = [a for a in arg_names]

			for i, pattern in enumerate(case.find_data("pattern")):
				pat = " ".join(pattern.children)
				pat = transl_simple.replace(pat)

				if " " in pat:
					pat = f'({pat})'

				args_case[item_pos[i]] = pat

			args_case = " ".join(args_case)
			term = transl_simple.replace(case.children[-1].value).strip()

			cases.append(f'"{func_name} {args_case} = {term}"')

		transl += "  " + "\n| ".join(cases)

	except Exception as e:
		#print("Couldn't parse inner func: ", e)

		arg_names = " ".join(arg_names)

		inner_func = transl_simple.replace(inner_func)

		transl += "  " + f'"{func_name} {arg_names} = {inner_func}"'

	return transl

def handle_func(func_def):
	func_name = func_def.children[0]

	def get(n):
		try:
			return next(func_def.find_data(n))
		except StopIteration as e:
			print(f"Don't have {n}")
			return None

	arg_names = []
	arg_types = []

	for a in func_def.find_data("arg"):
		names = [n.children[0].value for n in a.find_data("name")]
		names = [transl_simple.replace_token(a) for a in names]

		t = Typexpr(a.children[-1])
		for arg_name in names:
			arg_names.append(arg_name)
			arg_types.append(t.translate())

	maybe_ret = get("ret")

	if maybe_ret is not None:
		ret_type = Typexpr(maybe_ret.children[0]).translate()
	else:
		ret_type = "dunno"

	inner_func = func_def.children[-1]

	print(transl_func(func_name, arg_names, arg_types, ret_type, inner_func))

def handle_type(type_def):
	type_name = type_def.children[0]

	def get(n):
		try:
			return next(type_def.find_data(n))
		except StopIteration as e:
			print(f"Don't have {n}")
			return None

	constrs = []
	for contr_decl in type_def.find_data("constr_decl"):
		constructor = contr_decl.children[0]
		types = [Typexpr(t.children[0]).translate(True) for t in contr_decl.find_data("typexpr_start")]
		if types != []:
			assert types[-1] == type_name
			types = types[:-1] # last part is type name

			types_str = " " + " ".join(types)
		else:
			types_str = ""

		comment = ""
		for comm in contr_decl.find_data("comment"):
			comment = " (* {} *)".format(comm.children[0].strip())

		#print(constructor, types)

		constrs.append(f"{constructor}{types_str}{comment}")

	print(f"datatype {type_name} =")
	print("    " + "\n  | ".join(constrs))

def handle_inductive(inductive_def):
	inductive_name = inductive_def.children[0]

	def get(n):
		try:
			return next(inductive_def.find_data(n))
		except StopIteration as e:
			print(f"Don't have {n}")
			return None

	param_types = []
	for param_type in inductive_def.find_data("param_type"):
		param_types.append(Typexpr(param_type.children[0]).translate())

	assert (param_types[-1] == "bool")

	param_types_str = " ⇒ ".join(param_types)

	rules = []
	for rule_decl in inductive_def.find_data("rule_decl"):
		rule_name = rule_decl.children[0]
		rule_vars = []
		rule_terms = []

		for c in rule_decl.children[1:]:
			if c.data == "rule_var":
				rule_vars.append(transl_simple.replace_token(c.children[0]))
			elif c.data == "rule_part":
				rule_terms.append(InductiveTerm(c.children[0]).translate())

		nl = "\n" + " "*4

		if rule_vars:
			rule_vars_str = f'⋀{" ".join(rule_vars)}.{nl}'
		else: rule_vars_str = ""
		term_terms_str = f" ⟹{nl}".join(rule_terms)

		rules.append(f'{rule_name}: "{rule_vars_str}{term_terms_str}"')

	print(f'inductive {inductive_name} :: "{param_types_str}" where')
	print("  " + "\n| ".join(rules))


def main():
	d = []

	last_l = None
	l = input()
	while not (last_l == "" and l == ""):
		d.append(l)
		last_l = l
		l = input()

	d = "\n".join(d)

	tree = def_parser.parse(d)
	print(tree.pretty())

	for c in tree.children:
		if c.data == "func_def":
			handle_func(c)
		elif c.data == "type_def":
			handle_type(c)
		elif c.data == "inductive_def":
			handle_inducitve(c)
		print()

if __name__ == '__main__':
	main()