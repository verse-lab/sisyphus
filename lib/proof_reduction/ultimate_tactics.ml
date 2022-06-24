(* ultimate_tactics.ml is derived from coq/tactics/tactics.ml, extended with support for evaluating through opaque constants   *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Genredexpr


module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

(*********************************************)
(*                 Errors                    *)
(*********************************************)


exception Unhandled

let wrap_unhandled f e =
  try Some (f e)
  with Unhandled -> None

let tactic_interp_error_handler = function
  | _ -> raise Unhandled

let _ = CErrors.register_handler (wrap_unhandled tactic_interp_error_handler)


(*********************************************)
(*                 Tactics                   *)
(*********************************************)

(******************************************)
(*           Primitive tactics            *)
(******************************************)


(* Non primitive introduction tactics are treated by intro_then_gen
   There is possibly renaming, with possibly names to avoid and
   possibly a move to do after the introduction *)


(**************************************************************)
(*          Reduction and conversion tactics                  *)
(**************************************************************)



(* The main reduction function *)
(* let reduce redexp cl =
 *   let trace env sigma =
 *     let open Printer in
 *     let pr = ((fun e -> pr_econstr_env e), (fun e -> pr_leconstr_env e), pr_evaluable_reference, pr_constr_pattern_env) in
 *     Pp.(hov 2 (Ppred.pr_red_expr_env env sigma pr str redexp))
 *   in
 *   Proofview.Trace.name_tactic trace begin
 *   Proofview.Goal.enter begin fun gl ->
 *   let env = Proofview.Goal.env gl in
 *   let hyps = concrete_clause_of (fun () -> Tacmach.pf_ids_of_hyps gl) cl in
 *   let nbcl = (if cl.concl_occs = NoOccurrences then 0 else 1) + List.length hyps in
 *   let check = match redexp with Fold _ | Pattern _ -> true | _ -> false in
 *   let reorder = match redexp with
 *   | Fold _ | Pattern _ -> AnyHypConv
 *   | Simpl (flags, _) | Cbv flags | Cbn flags | Lazy flags ->
 *     if is_local_flag env flags then LocalHypConv else StableHypConv
 *   | Unfold flags ->
 *     if is_local_unfold env flags then LocalHypConv else StableHypConv
 *   | Red _ | Hnf | CbvVm _ | CbvNative _ -> StableHypConv
 *   | ExtraRedExpr _ -> StableHypConv (\* Should we be that lenient ?*\)
 *   in
 *   let redexp = Ultimate_redexpr.eval_red_expr env redexp in
 *   begin match cl.concl_occs with
 *   | NoOccurrences -> Proofview.tclUNIT ()
 *   | occs ->
 *     let redfun = Ultimate_redexpr.reduction_of_red_expr_val ~occs:(occs, nbcl) redexp in
 *     e_change_in_concl ~cast:true ~check redfun
 *   end
 *   <*>
 *   let f (id, occs, where) =
 *     let (redfun, _) = Ultimate_redexpr.reduction_of_red_expr_val ~occs:(occs, nbcl) redexp in
 *     let redfun _ env sigma c = redfun env sigma c in
 *     let redfun env sigma d = e_pf_change_decl redfun where env sigma d in
 *     (id, redfun)
 *   in
 *   e_change_in_hyps ~check ~reorder f hyps
 *   end
 *   end *)


let reduce ?(cbv=false) env evd cl =
  let redexp =
    if cbv
    then Cbv { rBeta=true; rMatch=true; rFix=true; rCofix=true; rZeta=true; rDelta=true; rConst=[] }
    else  Cbn { rBeta=true; rMatch=true; rFix=true; rCofix=true; rZeta=true; rDelta=true; rConst=[] } in
  let redexp = Ultimate_redexpr.eval_red_expr env redexp in
  let redfun, _ = Ultimate_redexpr.reduction_of_red_expr_val redexp in
  redfun env evd cl
