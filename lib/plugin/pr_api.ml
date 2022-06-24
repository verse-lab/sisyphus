
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
  let (evd, t) = Proof_reduction.reduce env evd t in
  Feedback.msg_info (Printer.pr_econstr_env env evd t)

let print_reduced_tac (t: Evd.econstr) =
  Proofview.Goal.enter @@ fun gl ->
  let env = Proofview.Goal.env gl in
  let evd = Proofview.Goal.sigma gl in
  (* Ultimate_reduction *)
  Feedback.msg_warning (Pp.str "Forgive me sensei, for I must go all out, just this once...");
  (* let (evd, t) = Ultimate_tactics.reduce ~cbv:true env evd t in *)
  let (evd, t) = Proof_reduction.reduce env evd t in
  (* let (evd, t) = Ultimate_tactics.reduce ~cbv:true env evd t in *)
  (* Feedback.msg_info (Constr.debug_print (EConstr.Unsafe.to_constr t)); *)
  Feedback.msg_info (Printer.pr_econstr_env env evd t);
  Tacticals.tclIDTAC
