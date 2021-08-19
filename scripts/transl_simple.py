#!/usr/bin/env python3

import re

replacements = {
	# "manual match conversion" as fallback
	r"match\s+(.*?)\s+with([\s\n]*)\|" : r"(case \1 of\2 ",
	r"match\s+(.*?)\s+with"            : r"(case \1 of",

	r"fun (.*?)\s+=>"   : r"λ\1.",
	r"(\w+)\.\((\w+)\)" : r"(\2 \1)", # record syntax
	r"forall([^,]+),"   : r"∀\1.",
	r"exists([^,]+),"   : r"∃\1.",
	r"=>"               : "⇒",
	r"\/\\"             : "∧",
	r"&&"               : "∧",
	r"\\\/"             : "∨",
	r"\|\|"             : "∨",
	r"::"               : "#",
	r"\*\*"             : "@",
	r"<->"              : "⟷",
	r"->"               : "⟶",
	r"<>"				: "≠",
	r":="               : "where",
	}

token_replacements = {
	"end"   : ")",
	"nil"   : "[]",
	"O"     : "0",
	"S"     : "Suc",
	"true"  : "True",
	"false" : "False",
	"Prop"  : "bool",
	"id"    : "ident",
	"typ"   : "type",
	"option_map": "map_option"
	}

def replace(s):
	r = s

	for pattern, repl in replacements.items():
		r = re.sub(pattern, repl, r)

	for pattern, repl in token_replacements.items():
		r = re.sub(fr"(?<!\w){pattern}(?!\w)", repl, r)

	# if r != s:
	# 	print(f"'{s}' -> '{r}")

	return r

def replace_token(t):
	r = token_replacements.get(t, t)

	# if r != t:
	# 	print(f"'{t}' -> '{r}")

	return r


def main():
	d = []

	l = input()
	while l != "":
		d.append(l)
		l = input()

	d = "\n".join(d)

	print(replace(d))

if __name__ == '__main__':
	main()