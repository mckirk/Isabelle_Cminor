instantiation type :: jsonable
begin
fun to_json_type :: "type ⇒ JSON" where
  "to_json_type Tint = String STR ''Tint''"
| "to_json_type Tfloat = String STR ''Tfloat''"
| "to_json_type Tlong = String STR ''Tlong''"
| "to_json_type Tsingle = String STR ''Tsingle''"
| "to_json_type Tany32 = String STR ''Tany32''"
| "to_json_type Tany64 = String STR ''Tany64''"
instance ..
end

instantiation globvar_ext :: (jsonable, _) jsonable
begin
fun to_json_globvar_ext :: "('a, 'b) globvar_scheme ⇒ JSON" where
  "to_json_globvar_ext v = Object [
    (STR ''gvar_info'', to_json (gvar_info v)),
    (STR ''gvar_init'', to_json (gvar_init v)),
    (STR ''gvar_readonly'', to_json (gvar_readonly v)),
    (STR ''gvar_volatile'', to_json (gvar_volatile v))]"
instance ..
end

instantiation globdef :: (jsonable, jsonable) jsonable
begin
fun to_json_globdef :: "('a, 'b) globdef ⇒ JSON" where
  "to_json_globdef (Gfun a0) = Array [String STR ''Gfun'', to_json a0]"
| "to_json_globdef (Gvar a0) = Array [String STR ''Gvar'', to_json a0]"
instance ..
end

