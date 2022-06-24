
module StringSet = Set.Make(String)

let whitelisted_modules = [
  "Verify_seq_to_array_new";
  "Coq.Init.Logic";
  "Coq.Init.Nat";
  "Coq.Arith.PeanoNat.Nat";
  "Proofs.Verify_seq_to_array_utils";
  "TLC.LibList";
  "CFML.Stdlib.List_ml";
  "CFML.WPTactics";
  "CFML.WPLifted";
  "CFML.SepBase.SepBasicSetup.SepSimplArgsCredits";
  "CFML.SepBase.SepBasicSetup.HS";
  "CFML.WPBase";
  "TLC.LibEqual";
  "CFML.SepBase.SepBasicCore";
  "CFML.SepBase.SepBasicSetup";
  "Coq.Init.Datatypes";
  "TLC.LibTactics";

  "Coq.Classes.Morphisms_Prop";

  "TLC.LibOperation";
  "CFML.SepLifted";
  "CFML.WPBuiltin";

  "Coq.Classes.Morphisms";
  "Coq.Program.Basics";
  "Coq.Init.Wf";
  "Coq.Classes.RelationClasses";
  (* "TLC.LibAxioms"; *)
] |> StringSet.of_list

let fun_ext_def =
  Names.Constant.make2
    (Names.ModPath.MPfile (Names.DirPath.make [Names.Id.of_string "Verify_seq_to_array_new"]))
    (Names.Label.make "fun_ext_def")
let prop_ext_def =
  Names.Constant.make2
    (Names.ModPath.MPfile (Names.DirPath.make [Names.Id.of_string "Verify_seq_to_array_new"]))
    (Names.Label.make "prop_ext_def")

let proof_irrelevance_def =
  Names.Constant.make2
    (Names.ModPath.MPfile (Names.DirPath.make [Names.Id.of_string "Verify_seq_to_array_new"]))
    (Names.Label.make "proof_irrelevance_def")

let is_constant_blacklisted cnst =
  let (mod_path, label) = Names.Constant.repr2 cnst in
  let mod_path_str = Names.ModPath.to_string mod_path in
  let label_str = Names.Label.to_string label in
  match mod_path_str, label_str with
  | "Coq.Init.Wf", "Acc_rect" -> `Blacklisted ((mod_path_str, label_str), false)
  (* | "TLC.LibAxioms", "fun_ext_dep" -> `Subst (fun_ext_def)
   * | "TLC.LibAxioms", "prop_ext" -> `Subst (prop_ext_def) *)
  | "ProofIrrelevance", "proof_irrelevance" -> `Subst (proof_irrelevance_def)
  | _ -> `Blacklisted ((mod_path_str, label_str), not @@ StringSet.mem mod_path_str whitelisted_modules)



let constant_value_in env ((c, u) as t) =
  (* Feedback.msg_warning (Pp.str @@ "evalling: " ^ Names.Constant.to_string c); *)
  match is_constant_blacklisted c with
  | `Blacklisted ((mod_path, label), true) ->
    Feedback.msg_warning @@ Pp.str @@ Format.sprintf "[%s][%s] is blacklisted"
                                        (mod_path)
                                        (label);
   Environ.constant_value_in env t
  | `Subst name ->
    Feedback.msg_warning @@ Pp.str @@ Format.sprintf "providing bogus definition for %s"
                                        (Names.Constant.to_string c);
    Environ.constant_value_in env (name, u)
  | `Blacklisted (_, false) ->
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
      match (is_constant_blacklisted kn) with
      | `Blacklisted (_, false) -> false (* OPAQUE Defs are transparent; love is war *)
      | _ -> true
