let is_constant_blacklisted cnst =
  let (mod_path, label) = Names.Constant.repr2 cnst in
  let path = Names.ModPath.to_string mod_path in
  let label = Names.Label.to_string label in
  let cnst = path, label in
  cnst, (!Config.filter ~path ~label)

let constant_value_in env ((c, u) as t) =
  let (mod_path, label), decision = is_constant_blacklisted c in
  match decision  with
  | `KeepOpaque ->
   Environ.constant_value_in env t
  | `Subst name ->
    Environ.constant_value_in env (name, u)
  | `Unfold ->
    match Global.body_of_constant Library.indirect_accessor c with
    | Some (e, _, _) -> e
    | _ -> Environ.constant_value_in env t

(* A global const is evaluable if it is defined and not opaque *)
let evaluable_constant kn env =
  let cb = Environ.lookup_constant kn env in
  Feedback.msg_warning (Pp.str @@ "is evaluable: " ^ Names.Constant.to_string kn);
    match cb.const_body with
    | Def _ -> true
    | Undef _ | Primitive _ -> false
    | OpaqueDef _ ->
      let _, decision = is_constant_blacklisted kn in
      match decision with
      | `KeepOpaque -> false (* OPAQUE Defs are transparent; love is war *)
      | _ -> true
