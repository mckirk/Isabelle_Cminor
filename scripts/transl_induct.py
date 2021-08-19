#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import re
from lark import Lark
import lark

"""
inductive eval_expr :: "expr ⇒ val ⇒ bool" where
  eval_Evar:
    "PTree_get ident e = Some v ⟹ eval_expr (Evar ident) v"
| eval_Econst:
    "eval_constant sp cst = Some v ⟹
    eval_expr (Econst cst) v"
| eval_Eunop:
    "eval_expr a1 v1 ⟹
    eval_unop op v1 = Some v ⟹
    eval_expr (Eunop op a1) v"
| eval_Ebinop:
    "eval_expr a1 v1 ⟹
    eval_expr a2 v2 ⟹
    eval_binop op v1 v2 m = Some v ⟹
    eval_expr (Ebinop op a1 a2) v"
| eval_Eload:
    "eval_expr addr vaddr ⟹
    Mem.loadv chunk m vaddr = Some v ⟹
    eval_expr (Eload chunk addr) v"
"""

induct_def = \
r"""
_separated{x, sep}: x (sep x)*

start: "inductive" IDENT "::" "\"" args "\"" "where" _separated{case, "|"}
args: _separated{ARG_PART, "⇒"}
case: IDENT ":" "\"" _separated{CODE_PART, "⟹"} "\""

IDENT: /\w+/
ARG_PART: /[^"⇒]+/
CODE_PART: /[^"⟹]+/m

%ignore /\s+/
"""

term_def = \
r"""
start: part+

!part: "(" _inner_part+ ")" | PART
!_inner_part: "(" _inner_part+ ")" | PART

PART: /[^"()\s]+/


%ignore /\s+/
"""

# CODE_PART: /[\w\s=()[].#']+/m

induct_parser = Lark(induct_def)
term_parser = Lark(term_def)

transl_set = ["step", "eval_expr", "eval_exprlist"]

def handle(inp):
	parsed = induct_parser.parse(inp)

	#print(parsed.pretty())

	induct_name = parsed.children[0]
	args = list(parsed.children[1].children)

	cases = parsed.find_data("case")

	fun_name = f"{induct_name}_fun"

	args = args[:-1]
	args[-1] += " option"
	args_transl = "⇒".join(args)

	cases_transl = []
	for c in cases:
		parts = [p.strip() for p in c.children[1:]]

		conditions = parts[:-1]
		term = parts[-1]

		exprs, patterns = [], []

		for p in conditions:
			if "=" in p:
				exp, pat = p.split("=")
				exprs.append(exp.strip())
				patterns.append(pat.strip())
			else:
				cond_parsed = term_parser.parse(p)
				cond_parts = [" ".join(p.children) for p in cond_parsed.find_data("part")]

				print(cond_parts)

				if cond_parts[0] == induct_name or cond_parts[0] in transl_set:
					cond_parts[0] += "_fun"
					exprs.append(" ".join(cond_parts[:-1]))
					patterns.append(f"Some {cond_parts[-1]}")
				else:
					exprs.append(p)
					patterns.append(None)

		term_parsed = term_parser.parse(term)
		term_parts = [" ".join(p.children) for p in term_parsed.find_data("part")]

		print(term_parsed.pretty())
		print(term_parts)

		assert term_parts[0] == induct_name

		term_args = term_parts[1:-1]
		term_res = term_parts[-1]
		term_args_joined = " ".join(term_args)

		case_transl = f"Some {term_res}"

		for exp, pat in reversed(list(zip(exprs, patterns))):
			if pat is None:
				case_transl = f"(if ({exp}) then \n  ({case_transl}) else None)"
			else:
				case_transl = f"(case ({exp}) of ({pat}) ⇒ \n  {case_transl} | _ ⇒ None)"

#		exprs_joined, patterns_joined = ", ".join(exprs), ", ".join(patterns)
#		cases_transl.append(f'"{fun_name} {term_args_joined} = (case ({exprs_joined}) of ({patterns_joined}) ⇒ Some ({term_res}) | _ ⇒ None)"')

		cases_transl.append(f'"{fun_name} {term_args_joined} = \n  {case_transl}"')

	result = f'fun {induct_name}_fun :: "{args_transl}" where\n'
	result += "  " + "\n| ".join(cases_transl)

	print(result)

def main():
	d = []

	l = input()
	while l != "":
		d.append(l)
		l = input()

	d = "\n".join(d)

	handle(d)

if __name__ == '__main__':
	main()