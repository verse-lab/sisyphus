
module StringSet = Set.Make(String)

let whitelisted_modules = [
  "Verify_seq_to_array_new";
  "Coq.Init.Logic";
  "Coq.Arith.PeanoNat.Nat";
  "Coq.Classes.Morphisms"
] |> StringSet.of_list
let is_constant_blacklisted cnst =
  let (mod_path, label) = Names.Constant.repr2 cnst in
  (* Feedback.msg_warning @@ Pp.str @@ Format.sprintf "checking if [%s][%s] is blacklisted = %b"
   *                                     (Names.ModPath.to_string mod_path)
   *                                     (Names.Label.to_string label)
   * (not @@ StringSet.mem (Names.ModPath.to_string mod_path) whitelisted_modules); *)
  not @@ StringSet.mem (Names.ModPath.to_string mod_path) whitelisted_modules

let constant_value_in env ((c, _) as t) =
  (* Feedback.msg_warning (Pp.str @@ "evalling: " ^ Names.Constant.to_string c); *)
  if is_constant_blacklisted c
  then Environ.constant_value_in env t
  else
    match Global.body_of_constant Library.indirect_accessor c with
    | Some (e, _, _) -> e
    | _ -> Environ.constant_value_in env t

(* A global const is evaluable if it is defined and not opaque *)
let evaluable_constant kn env =
  let cb = Environ.lookup_constant kn env in
  Feedback.msg_warning (Pp.str @@ "is evaluable: " ^ Names.Constant.to_string kn);
    match cb.const_body with
    | Def _ -> true
    | OpaqueDef _ ->
      not (is_constant_blacklisted kn)
    (* OPAQUE Defs are transparent; love is war *)
    | Undef _ | Primitive _ -> false
