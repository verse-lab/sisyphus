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

let filter ~path:mod_path ~label =
  match mod_path, label with
  | "Coq.Init.Wf", "Acc_rect" -> `Unfold
  (* | "TLC.LibAxioms", "fun_ext_dep" -> `Subst (fun_ext_def)
   * | "TLC.LibAxioms", "prop_ext" -> `Subst (prop_ext_def) *)
  (* | "ProofIrrelevance", "proof_irrelevance" -> `Subst (proof_irrelevance_def) *)
  | _ ->
    if StringSet.mem mod_path whitelisted_modules
    then `Unfold
    else `KeepOpaque

let access cb =
  match Global.body_of_constant Library.indirect_accessor cb with
  | Some (e, _, _) -> e
  | None ->
    CErrors.user_err (Pp.str "term has no value")

(*
   Opaqueproof
 *)

let reduce e =
  match Constr.kind e with
  | Constr.Const (name, _) -> access name
  | _ -> e

let print_reduced (e: Constrexpr.constr_expr_r CAst.t) =
  let env = Global.env () in
  let evd = Evd.from_env env in
  let evd, t = Constrintern.interp_constr_evars env evd e in
  (* Ultimate_reduction *)
  Feedback.msg_warning (Pp.str "Forgive me sensei! I must go all out, just this once...");
  let (evd, t) = Proof_reduction.reduce ~filter env evd t in
  Feedback.msg_info (Printer.pr_econstr_env env evd t)

let print_reduced_tac (t: Evd.econstr) =
  Proofview.Goal.enter @@ fun gl ->
  let env = Proofview.Goal.env gl in
  let evd = Proofview.Goal.sigma gl in
  (* Ultimate_reduction *)
  Feedback.msg_warning (Pp.str "Forgive me sensei, for I must go all out, just this once...");
  (* let (evd, t) = Ultimate_tactics.reduce ~cbv:true env evd t in *)
  let (evd, t) = Proof_reduction.reduce ~filter env evd t in
  (* let (evd, t) = Ultimate_tactics.reduce ~cbv:true env evd t in *)
  (* Feedback.msg_info (Constr.debug_print (EConstr.Unsafe.to_constr t)); *)
  Feedback.msg_info (Printer.pr_econstr_env env evd t);
  Tacticals.tclIDTAC
