let parse_typ (j : json) : typ =
  match j with
  | `String "Tint" -> Tint
  | `String "Tfloat" -> Tfloat
  | `String "Tlong" -> Tlong
  | `String "Tsingle" -> Tsingle
  | `String "Tany32" -> Tany32
  | `String "Tany64" -> Tany64
  | _ -> fail_parse "typ" j

let parse_globvar (parse_v : json -> 'v) (j : json) : 'v globvar =
  {gvar_info = parse_assoc_key "gvar_info" parse_v j;
   gvar_init = parse_assoc_key "gvar_init" (parse_list parse_init_data) j;
   gvar_readonly = parse_assoc_key "gvar_readonly" parse_bool j;
   gvar_volatile = parse_assoc_key "gvar_volatile" parse_bool j}

let parse_globdef (parse_f : json -> 'f) (parse_v : json -> 'v) (j : json) : ('f, 'v) globdef =
  match j with
  | `List ((`String "Gfun") :: a0 :: []) -> Gfun (parse_f a0)
  | `List ((`String "Gvar") :: a0 :: []) -> Gvar (parse_globvar parse_v a0)
  | _ -> fail_parse "globdef" j

