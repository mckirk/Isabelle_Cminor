#!/usr/bin/env python3

import lark

datatype_def = \
"""
_separated{x, sep}: x (sep x)*

start: "datatype" IDENT "=" _separated{constr, "|"}

constr: IDENT _constr_arg*
_constr_arg: IDENT | _APO /[\w() *]+/ _APO

IDENT: /\w+/

_APO: /"/

%ignore /\s+/
%ignore /\(\*.*?\*\)/
"""

def instantiation(name, lines):
	lines = "\n| ".join(lines)
	return \
f"""instantiation {name} :: jsonable
begin
fun to_json_{name} :: "{name} ⇒ JSON" where
  {lines}
instance by auto
end"""

def fun_line(name, constr, arg_types, no_args = False):
	if no_args:
		assert arg_types == []
		return f"\"to_json_{name} {constr} = String ''{constr}''\""

	args = []
	fields = [f"String ''{constr}''"]

	for i, at in enumerate(arg_types):
		args.append(f"a{i}")
		if at == "string":
			fields.append(f"String a{i}")
		else:
			fields.append(f"to_json a{i}")

	if args != []:
		args = " " + " ".join(args)
	else:
		args= ""

	fields = ", ".join(fields)

	return f"\"to_json_{name} ({constr}{args}) = Array [{fields}]\""

datatype_parser = lark.Lark(datatype_def)#, parser="lalr")

def main():
	d = ""

	l = input()
	while l != "":
		d += "\n" + l
		l = input()

	res = datatype_parser.parse(d)

	print(res.pretty())

	type_name = res.children[0]

	has_any_args = False
	for c in res.find_data("constr"):
		arg_types = c.children[1:]
		if len(arg_types) > 0:
			has_any_args = True

	lines = []
	for c in res.find_data("constr"):
		constr = c.children[0]
		arg_types = c.children[1:]
		lines.append(fun_line(type_name, constr, arg_types, no_args = not has_any_args))

	print(instantiation(type_name, lines))


if __name__ == '__main__':
	main()