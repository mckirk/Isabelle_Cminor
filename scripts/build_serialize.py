#!/usr/bin/env python3

import lark
import string
from collections import defaultdict

datatype_def = \
"""
_separated{x, sep}: x (sep x)*

type_definition: "type" ["nonrec"] typedef
typedef: [type_params] TYPECONSTR_NAME type_information
type_information: [type_equation] [type_representation]  type_constraint*
type_equation: "=" typexpr
type_representation:  "=" ["|"] _separated{constr_decl, "|"}
                    | "=" record_decl
                    | "=" "|"
type_params: type_param | "(" _separated{type_param, ","} ")"
type_param: [variance] TYPE_ARG
variance: "+"| "-"
record_decl: "{" _separated{field_decl, ";"} [";"] "}"
constr_decl: (CONSTR_NAME | "[]" | "(::)") [ "of" _constr_args ]
_constr_args: _separated{typexpr, "*"}
field_decl: ["mutable"] FIELD_NAME ":" poly_typexpr
type_constraint: "constraint" TYPE_ARG "=" typexpr

// give typexpr lower priority, to not confuse constr_args parsing with tuples
typexpr.-1: TYPE_ARG -> type_arg
      | "_" -> dummy
      | "(" typexpr ")" -> parenthesized
      | typexpr ("*" typexpr)+ -> tuple
      | TYPECONSTR -> constr
      | typexpr TYPECONSTR -> constr
      | "(" _separated{typexpr, ","} ")" TYPECONSTR -> constr

?poly_typexpr: typexpr
      | (TYPE_ARG)+ "." typexpr

IDENT: /[A-Za-z_][A-Za-z0-9_']*/
CAPITALIZED_IDENT: /[A-Z][A-Za-z0-9_']*/
LOWERCASE_IDENT: /[a-z_][A-Za-z0-9_']*/

TYPE_ARG: "'" IDENT

TYPECONSTR: [MODULE_NAME "."] TYPECONSTR_NAME
MODULE_NAME: CAPITALIZED_IDENT
TYPECONSTR_NAME: LOWERCASE_IDENT

CONSTR_NAME: CAPITALIZED_IDENT

FIELD_NAME: LOWERCASE_IDENT

%ignore /\s+/
%ignore /\(\*.*?\*\)/
"""

type_list_grammar = datatype_def + \
"""
files: [global_mods] file+

global_mods: mods
file_mods: mods
mods: mod+
mod: ("(" IDENT ":" TYPECONSTR "=n" TYPECONSTR ")") -> renaming
   | ("(" IDENT ":" typexpr  "=p" typexpr ")") -> alias

file: IDENT ":" [file_mods] types

types: "*" -> all | type+
type: IDENT

%ignore /#.*/"""

type_list_parser = lark.Lark(type_list_grammar, start="files")
datatype_parser = lark.Lark(datatype_def, start="type_definition")
typexpr_parser = lark.Lark(datatype_def, start="typexpr")

def match_tree_type(t, ty):
    if isinstance(t, lark.Tree):
        if t.data == ty:
            return True
    elif isinstance(t, lark.Token):
        if t.type == ty:
            return True
    return False

def match_tree_types(ts, tys):
    if len(ts) != len(tys):
        return False

    for t, ty in zip(ts, tys):
        if not match_tree_type(t, ty):
            return False

    return True

def join_par(j, elems, fmt = "{}", always_par = False):
    assert "{}" in fmt

    if elems == []:
        return ""
    if len(elems) == 1 and not always_par:
        return fmt.format(elems[0])
    else:
        return fmt.format(f"({j.join(elems)})")

def space_par(s):
    if " " in s:
        return f"({s})"
    else:
        return s

class Mods:
    def __init__(self, args = []):
        # keep mods in a single dict, to make __plus__ simple
        self.mods = defaultdict(lambda: dict())

        for c in args:
            self.add(c)

    def add(self, c):
        env = c.children[0].value
        if c.data == "renaming":
            name_from, name_to = c.children[1].value, c.children[2].value
            self.mods[(env, "n", name_from)] = name_to
        elif c.data == "alias":
            type_from, type_to = c.children[1:]
            self.mods[(env, "t", str(Typexpr(type_from)))] = Typexpr(type_to)

    def get_type_alias(self, env, t):
        return self.mods.get((env, "t", str(t)))

    def alias(self, env, t):
        return self.mods.get((env, "t", str(t)), t)

    def rename(self, env, n):
        return self.mods.get((env, "n", n), n)

    def __add__(self, o):
        new_mods = Mods()

        new_mods.mods = {**self.mods, **o.mods}

        return new_mods

    def __str__(self):
        return str(self.mods)


class ParseMods(lark.Transformer):
    def mods(self, args):
        return Mods(args)

class Typexpr:
    def __init__(self, t):
        self.is_parenthesized = match_tree_type(t, "parenthesized")
        self.is_dummy = match_tree_type(t, "dummy")
        self.is_typeconstr = match_tree_type(t, "constr")
        self.is_typearg = match_tree_type(t, "type_arg")
        self.is_tuple = match_tree_type(t, "tuple")

        assert (self.is_parenthesized + self.is_dummy + self.is_typeconstr + self.is_typearg + self.is_tuple) == 1

        cs = t.children
        if self.is_parenthesized:
            self.child = Typexpr(cs[0])
        if self.is_typeconstr:
            self.full_name = cs[-1]

            if "." in self.full_name:
                self.module, self.typeconstr = self.full_name.split(".")
            else:
                self.module, self.typeconstr = "", self.full_name

            self.typeconstr_args = list(map(Typexpr, cs[:-1]))
        if self.is_typearg:
            self.typearg = cs[0]
        if self.is_tuple:
            self.children = list(map(Typexpr, cs))

    def __str__(self):
        if self.is_parenthesized: return f"({str(self.child)})"
        if self.is_dummy: return "_"
        if self.is_typeconstr:
            return join_par(", ", [str(a) for a in self.typeconstr_args], "{} ") + self.full_name
        if self.is_typearg: return self.typearg
        if self.is_tuple:
            return join_par(" * ", [str(c) for c in self.children])

    def unpack(self):
        if self.is_parenthesized: return [self.child]
        if self.is_tuple: return self.children
        return [self]

    def build_parse_str(self, mods):
        assert not self.is_dummy

        type_alias = mods.get_type_alias("ocaml", self)
        if type_alias is not None:
            return type_alias.build_parse_str(mods)

        if self.is_parenthesized:
            return self.child.build_parse_str(mods)
        if self.is_typeconstr:
            if self.module != "":
                full_name = f"{self.module}.{self.typeconstr}"
            else:
                full_name = self.typeconstr

            renamed = mods.rename("ocaml", full_name)
            renamed = renamed.replace(".", "_")
            
            parse_parts = [f"parse_{renamed}"]
            parse_parts += [space_par(c.build_parse_str(mods)) for c in self.typeconstr_args]
            return " ".join(parse_parts)
        if self.is_typearg:
            return f"parse_{self.typearg[1:]}"
        if self.is_tuple:
            parse_parts = [f"parse_tuple{len(self.children)}"]
            parse_parts += [space_par(c.build_parse_str(mods)) for c in self.children]
            return " ".join(parse_parts)

    # def uses_typeconstr(self, constr, mods):
    #     if self.is_parenthesized: return self.child.uses_typeconstr(constr, mods)
    #     if self.is_typeconstr:
            

def get(res, n):
    try:
        return next(res.find_data(n)).children
    except StopIteration as e:
        #print(f"Don't have {n}")
        return None

def find(res, n):
    return res.find_data(n)

def isabelle_datatype_inst(name, type_arg_count, constrs, mods):
    name = mods.rename("isabelle", name)

    class_args = join_par(", ", ["jsonable"]*type_arg_count, "{} ", always_par = True)
    type_args = join_par(", ", [f"'{string.ascii_lowercase[i]}" for i in range(type_arg_count)], "{} ")

    no_constr_args = all([arg_types == [] for (_, arg_types) in constrs])
    lines = []
    for constr, arg_types in constrs:
        if no_constr_args:
            lines.append(f"\"to_json_{name} {constr} = String STR ''{constr}''\"")
            continue

        args, fields = [constr], [f"String STR ''{constr}''"]
        for i, at in enumerate(arg_types):
            args.append(f"a{i}")
            fields.append(f"to_json a{i}")

        args = join_par(" ", args)
        fields = ", ".join(fields)

        lines.append(f"\"to_json_{name} {args} = Array [{fields}]\"")

    lines = "\n| ".join(lines)

    return \
f"""instantiation {name} :: {class_args}jsonable
begin
fun to_json_{name} :: "{type_args}{name} ⇒ JSON" where
  {lines}
instance ..
end"""

def ocaml_datatype_parse(name, type_args, constrs, mods):
    name = mods.rename("ocaml", name)
    parse_name = name.replace(".", "_")

    no_constr_args = all([arg_types == [] for (_, arg_types) in constrs])
    is_recursive_type = any(any(str(at) == name for at in ats) for (_, ats) in constrs)

    parse_parts = [f"parse_{parse_name}"]
    parse_parts += [f"(parse_{t[1:]} : json -> {t})" for t in type_args]

    if is_recursive_type:
        parse_parts = ["rec"] + parse_parts

    parse_parts_joined = " ".join(parse_parts)
    type_args_joined = join_par(", ", type_args, "{} ")

    lines = []
    for constr, arg_types in constrs:
        if no_constr_args:
            lines.append(f"`String \"{constr}\" -> {constr}")
            continue

        pattern_parts = [f"(`String \"{constr}\")"] + [f"a{i}" for i,_ in enumerate(arg_types)] + ["[]"]
        pattern = " :: ".join(pattern_parts)
        constr_args = join_par(", ", [f"{at.build_parse_str(mods)} a{i}" for i,at in enumerate(arg_types)], fmt=" {}", always_par = True)
        lines.append(f"`List ({pattern}) -> {constr}{constr_args}")

    lines.append(f"_ -> fail_parse \"{name}\" j")

    lines = "\n  | ".join(lines)
    return \
f"""let {parse_parts_joined} (j : json) : {type_args_joined}{name} =
  match j with
  | {lines}"""

def handle_datatype(res, mods, streams):
    typedef = get(res, "typedef")
    type_name = typedef[-2]
    type_params = [tp.children[-1] for tp in res.find_data("type_param")]

    constrs = []
    for c in res.find_data("constr_decl"):
        constr_name = c.children[0]
        constr_args = []
        for t in c.children[1:]:
            # we don't want tuples at top level unless they're parenthesized
            constr_args += Typexpr(t).unpack()

        constrs.append((constr_name, constr_args))

    print(isabelle_datatype_inst(type_name, len(type_params), constrs, mods) + "\n", file=streams["isabelle"])
    print(ocaml_datatype_parse(type_name, type_params, constrs, mods) + "\n", file=streams["ocaml"])

def isabelle_record_inst(name, type_arg_count, fields, mods):
    name = mods.rename("isabelle", name)

    class_args = ", ".join(["jsonable"]*type_arg_count + ["_"])
    type_args = ", ".join(f"'{string.ascii_lowercase[i]}" for i in range(type_arg_count + 1))
    field_lines = ',\n    '.join(f"(STR ''{f}'', to_json ({f} v))" for f,_ in fields)
    return \
f"""instantiation {name}_ext :: ({class_args}) jsonable
begin
fun to_json_{name}_ext :: "({type_args}) {name}_scheme ⇒ JSON" where
  "to_json_{name}_ext v = Object [
    {field_lines}]"
instance ..
end"""

def ocaml_record_parse(name, type_args, fields, mods):
    name = mods.rename("ocaml", name)
    parse_name = name.replace(".", "_")

    parse_parts = [f"parse_{parse_name}"]
    parse_parts += [f"(parse_{t[1:]} : json -> {t})" for t in type_args]
    parse_parts_joined = " ".join(parse_parts)
    type_args_joined = join_par(", ", type_args, "{} ")

    lines = []
    for field, field_type in fields:
        lines.append(f"{field} = parse_assoc_key \"{field}\" {space_par(field_type.build_parse_str(mods))} j")

    lines = ";\n   ".join(lines)
    return \
f"""let {parse_parts_joined} (j : json) : {type_args_joined}{name} =
  {{{lines}}}"""

def handle_record(res, mods, streams):
    typedef = get(res, "typedef")
    type_name = typedef[-2]
    type_params = [tp.children[-1] for tp in res.find_data("type_param")]

    fields = [(f.children[0], Typexpr(f.children[1])) for f in res.find_data("field_decl")]

    print(isabelle_record_inst(type_name, len(type_params), fields, mods) + "\n", file=streams["isabelle"])
    print(ocaml_record_parse(type_name, type_params, fields, mods) + "\n", file=streams["ocaml"])

def handle_alias(res, mods, streams):
    typedef = get(res, "typedef")
    type_name = typedef[-2]
    type_params = [tp.children[-1] for tp in res.find_data("type_param")]

    alias_type = Typexpr(get(res, "type_equation")[0])

    type_name_ocaml = mods.rename("ocaml", type_name)

    parse_args = " ".join([f"parse_{type_name_ocaml}"] + [f"parse_{t[1:]}" for t in type_params])
    print(f"let {parse_args} = {alias_type.build_parse_str(mods)}\n", file=streams["ocaml"])


def handle_type(text, mods, streams):
    res = datatype_parser.parse(text)

    #print(res.pretty())

    if get(res, "constr_decl") is not None:
        handle_datatype(res, mods, streams)
    elif get(res, "field_decl") is not None:
        handle_record(res, mods, streams)
    else:
        handle_alias(res, mods, streams)

def extract_types(file, types, mods, streams):
    import re

    with open(f"{file}.mli", "r") as f:
        matches = re.finditer(r"(?ms)^type.*? (\w+) =.*?\n$", f.read())

    found_types = dict()
    for m in matches:
        name = m.group(1)
        found_types[name] = m.group(0)

    if types != "*":
        wanted = [t.children[0] for t in types]
    else:
        wanted = found_types.keys()

    for name in wanted:
        if not name in found_types.keys():
            print(f"Can't find {file}.{name}!")
            continue

        print(f"Handling {name}")
        handle_type(found_types[name], mods, streams)

def handle_type_list(filename, streams):
        with open(filename, "r") as f:
            parsed = type_list_parser.parse(f.read())

        parsed = ParseMods().transform(parsed)

        def get_mods(tree, n):
            r = get(tree, n)
            if r is not None:
                return r[0]
            else:
                return Mods()

        global_mods = get_mods(parsed, "global_mods")

        for fp in parsed.find_data("file"):
            file = fp.children[0]
            if get(fp, "all") is not None:
                types = "*"
            else:
                types = list(fp.find_data("type"))

            print(f"In file {file}")

            file_mods = get_mods(fp, "file_mods")
            combined_mods = global_mods + file_mods

            extract_types(file, types, combined_mods, streams)

def main():
    import sys

    streams = defaultdict(lambda: sys.stdout)

    if len(sys.argv) == 1:
        d = ""

        l = input()
        while l != "":
            d += "\n" + l
            l = input()

        handle_type(d, streams)
    else:
        streams["isabelle"] = open("isabelle.thy", "w", encoding="utf8")
        streams["ocaml"] = open("ocaml.ml", "w", encoding="utf8")

        handle_type_list(sys.argv[1], streams)

if __name__ == '__main__':
    main()