
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
  let sigma, t = Constrintern.interp_constr_evars env evd e in
  Feedback.msg_warning (Pp.str "Forgive me sensei, for I must go all out, just this once...");
  let e = reduce (EConstr.Unsafe.to_constr t) in
  Feedback.msg_info (Constr.debug_print e)
