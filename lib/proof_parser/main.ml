open Containers
open Proof_spec.Script

type proof = step list
type script = {
  directives: string;
  name: string;
  spec: string;
  proof: proof;
}

let proof_str = IO.with_in "../../resources/seq_to_array/Verify_seq_to_array_old.v" IO.read_all

let get_tag = function
  | Vernacexpr.VernacLoad (_, _) -> "VernacLoad"
  |Vernacexpr.VernacReservedNotation (_, _)
    -> "VernacReservedNotation"
  |Vernacexpr.VernacOpenCloseScope (_, _) -> "VernacOpenCloseScope"
  |Vernacexpr.VernacDeclareScope _
    -> "VernacDeclareScope"
  |Vernacexpr.VernacDelimiters (_, _) -> "VernacDelimiters"
  |Vernacexpr.VernacBindScope (_, _)
    -> "VernacBindScope"
  |Vernacexpr.VernacNotation (_, _, _, _) -> "VernacNotation"
  |Vernacexpr.VernacNotationAddFormat
     (_, _, _) -> "VernacNotationAddFormat"
  |Vernacexpr.VernacDeclareCustomEntry _ -> "VernacDeclareCustomEntry"
  |Vernacexpr.VernacDefinition
     (_, _, _) -> "VernacDefinition"
  |Vernacexpr.VernacStartTheoremProof (_, _)
    -> "VernacStartTheoremProof"
  |Vernacexpr.VernacEndProof _ -> "VernacEndProof"
  |Vernacexpr.VernacExactProof _
    -> "VernacExactProof"
  |Vernacexpr.VernacAssumption (_, _, _) -> "VernacAssumption"
  |Vernacexpr.VernacInductive (_, _)
    -> "VernacInductive"
  |Vernacexpr.VernacFixpoint (_, _) -> "VernacFixpoint"
  |Vernacexpr.VernacCoFixpoint (_, _)
    -> "VernacCoFixpoint"
  |Vernacexpr.VernacScheme _ -> "VernacScheme"
  |Vernacexpr.VernacCombinedScheme (_, _)
    -> "VernacCombinedScheme"
  |Vernacexpr.VernacUniverse _ -> "VernacUniverse"
  |Vernacexpr.VernacConstraint _
    -> "VernacConstraint"
  |Vernacexpr.VernacBeginSection _ -> "VernacBeginSection"
  |Vernacexpr.VernacEndSegment _
    -> "VernacEndSegment"
  |Vernacexpr.VernacRequire (_, _, _) -> "VernacRequire"
  |Vernacexpr.VernacImport (_, _, _)
    -> "VernacImport"
  |Vernacexpr.VernacCanonical _ -> "VernacCanonical"
  |Vernacexpr.VernacCoercion (_, _, _)
    -> "VernacCoercion"
  |Vernacexpr.VernacIdentityCoercion (_, _, _)
    -> "VernacIdentityCoercion"
  |Vernacexpr.VernacNameSectionHypSet (_, _) -> "VernacNameSectionHypSet"
  |Vernacexpr.VernacInstance
     (_, _, _, _, _) -> "VernacInstance"
  |Vernacexpr.VernacDeclareInstance (_, _, _, _)
    -> "VernacDeclareInstance"
  |Vernacexpr.VernacContext _ -> "VernacContext"
  |Vernacexpr.VernacExistingInstance _
    -> "VernacExistingInstance"
  |Vernacexpr.VernacExistingClass _ -> "VernacExistingClass"
  |Vernacexpr.VernacDeclareModule
     (_, _, _, _) -> "VernacDeclareModule"
  |Vernacexpr.VernacDefineModule (_, _, _, _, _)
    -> "VernacDefineModule"
  |Vernacexpr.VernacDeclareModuleType (_, _, _, _) -> "VernacDeclareModuleType"
  |Vernacexpr.VernacInclude _
    -> "VernacInclude"
  |Vernacexpr.VernacAddLoadPath _ -> "VernacAddLoadPath"
  |Vernacexpr.VernacRemoveLoadPath _
    -> "VernacRemoveLoadPath"
  |Vernacexpr.VernacAddMLPath _ -> "VernacAddMLPath"
  |Vernacexpr.VernacDeclareMLModule _
    -> "VernacDeclareMLModule"
  |Vernacexpr.VernacChdir _ -> "VernacChdir"
  |Vernacexpr.VernacResetName _
    -> "VernacResetName"
  |Vernacexpr.VernacResetInitial -> "VernacResetInitial"
  |Vernacexpr.VernacBack _
    -> "VernacBack"
  |Vernacexpr.VernacCreateHintDb (_, _) -> "VernacCreateHintDb"
  |Vernacexpr.VernacRemoveHints (_, _)
    -> "VernacRemoveHints"
  |Vernacexpr.VernacHints (_, _) -> "VernacHints"
  |Vernacexpr.VernacSyntacticDefinition
     (_, _, _) -> "VernacSyntacticDefinition"
  |Vernacexpr.VernacArguments (_, _, _, _) -> "VernacArguments"
  |Vernacexpr.VernacReserve
     _ -> "VernacReserve"
  |Vernacexpr.VernacGeneralizable _ -> "VernacGeneralizable"
  |Vernacexpr.VernacSetOpacity _
    -> "VernacSetOpacity"
  |Vernacexpr.VernacSetStrategy _
    -> "VernacSetStrategy"
  |Vernacexpr.VernacAddOption (_, _) -> "VernacAddOption"
  |Vernacexpr.VernacRemoveOption (_, _)
    -> "VernacRemoveOption"
  |Vernacexpr.VernacMemOption (_, _) -> "VernacMemOption"
  |Vernacexpr.VernacPrintOption _
    -> "VernacPrintOption"
  |Vernacexpr.VernacCheckMayEval (_, _, _) -> "VernacCheckMayEval"
  |Vernacexpr.VernacGlobalCheck _
    -> "VernacGlobalCheck"
  |Vernacexpr.VernacDeclareReduction (_, _) -> "VernacDeclareReduction"
  |Vernacexpr.VernacPrint _
    -> "VernacPrint"
  |Vernacexpr.VernacSearch (_, _, _) -> "VernacSearch"
  |Vernacexpr.VernacLocate _
    -> "VernacLocate"
  |Vernacexpr.VernacRegister (_, _) -> "VernacRegister"
  |Vernacexpr.VernacPrimitive (_, _, _)
    -> "VernacPrimitive"
  |Vernacexpr.VernacComments _ -> "VernacComments"
  |Vernacexpr.VernacAbort _
    -> "VernacAbort"
  |Vernacexpr.VernacAbortAll -> "VernacAbortAll"
  |Vernacexpr.VernacRestart -> "VernacRestart"
  |Vernacexpr.VernacUndo _
    -> "VernacUndo"
  |Vernacexpr.VernacUndoTo _ -> "VernacUndoTo"
  |Vernacexpr.VernacFocus _
    -> "VernacFocus"
  |Vernacexpr.VernacUnfocus -> "VernacUnfocus"
  |Vernacexpr.VernacUnfocused
    -> "VernacUnfocused"
  |Vernacexpr.VernacBullet _ -> "VernacBullet"
  |Vernacexpr.VernacSubproof _
    -> "VernacSubproof"
  |Vernacexpr.VernacEndSubproof -> "VernacEndSubproof"
  |Vernacexpr.VernacShow _
    -> "VernacShow"
  |Vernacexpr.VernacCheckGuard -> "VernacCheckGuard"
  |Vernacexpr.VernacProof (_, _)
    -> "VernacProof"
  |Vernacexpr.VernacProofMode _ -> "VernacProofMode"
  |Vernacexpr.VernacExtend (extend_name, args) ->
    let f arg =
      let s = Serlib.Ser_genarg.sexp_of_raw_generic_argument arg in
      print_endline @@ Format.sprintf "%a" Sexplib.Sexp.pp_hum s;

      (* let s2 = match s with_in | Sexplib.Sexp.Atom _ -> assert false | Sexplib.Sexp.List xs -> List.nth xs 3 in *)
      (* let a2 = Serapi.Serapi_protocol.CoqGenArg (Serlib.Ser_genarg.raw_generic_argument_of_sexp (Sexplib.Sexp.Atom "xcf")) in *)

      (* let a = Serapi.Serapi_protocol.CoqGenArg (Serlib.Ser_genarg.raw_generic_argument_of_sexp s) in *)
      (* (\* match arg with *\) *)
      (* | Genarg.GenArg (Genarg.Rawwit (Genarg.ExtraArg _), _) -> *)
      (*   print_endline @@ Format.sprintf "%a" Pp.pp_with (Serapi.Serapi_protocol.gen_pp_obj Environ.empty_env Evd.empty a); *)
      (* | _ -> () *)

      let s2 =  Ppvernac.pr_vernac_expr (Vernacexpr.VernacExtend (extend_name, args)) in 
      print_endline @@ Format.sprintf "%a" Pp.pp_with s2;

    in

    (* f (List.nth args 2); *)

    "VernacExtend"
  |Vernacexpr.VernacSetOption (_, _, _) -> "VernacSetOption"



let asts =
  let module Ctx =
    Coq.Proof.Make(struct
      let verbose = false
      let libs = [
        Coq.Coqlib.make
          ~path:(Fpath.of_string "../../_build/default/resources/seq_to_array" |> Result.get_exn)
          "Proofs"
      ] 
    end) in
  Ctx.add proof_str;
  (* Ctx.exec(); *)

  let start = Ctx.size() - 1 in

  (* TODO: Candidate for function*)
  Iter.int_range_by ~step:(-1) start 0
  |> Iter.filter_map (fun at ->

   Ctx.query ~at Serapi.Serapi_protocol.Ast
  )
  |> Iter.flat_map_l Fun.id
  |> Iter.filter_map (function Serapi.Serapi_protocol.CoqAst v as ast ->
    (* print_endline @@ Format.sprintf "%7s\n%a\n------------------%!" (get_tag v.v.expr) Pp.pp_with (Serapi.Serapi_protocol.gen_pp_obj Environ.empty_env Evd.empty ast); *)
    Some v
                             | _ -> None
  )
  |> Iter.to_list

let statement_0 = List.hd asts

let ast_to_string ast =
  let pp = (Serapi.Serapi_protocol.gen_pp_obj Environ.empty_env Evd.empty (Serapi.Serapi_protocol.CoqAst ast)) in
  Format.sprintf "%a\n" Pp.pp_with pp

let handle_decs asts  =
  let is_dec (stmt: Vernacexpr.vernac_control_r CAst.t) =
    match stmt.v.expr  with
    | Vernacexpr.VernacSetOption (_, _, _) |  Vernacexpr.VernacRequire (_, _, _) -> true
    | _ -> false
  in
  let decs, rest = List.partition is_dec asts in
  let dec_str = List.fold_left (^) "" (List.map ast_to_string decs) in
  dec_str, rest

let handle_spec asts =
  ast_to_string @@ List.hd asts, List.tl asts

let vexpr_to_string vexpr =
   Format.sprintf "%a" Pp.pp_with (Ppvernac.pr_vernac_expr vexpr)

let tactics = ["xcf"; "xpullpure"; "xpurefun"; "xapp"; "xdestruct"; "rewrite"; "desstruct"; "xmatch_case"; "xvalemptyarr"; "xalloc"; "xletopaque"; "xvals"; "apply"; "intros"; "admitted"]

let get_tactic str vexpr  =
  try
    match (List.find (fun t -> String.prefix ~pre:t str) tactics) with
    | "xcf" -> `Xcf (vexpr_to_string vexpr)
    | "xpullpure" -> `Xpullpure (vexpr_to_string vexpr)
    | _ -> `Xcf (vexpr_to_string vexpr)
  with
  | Not_found -> assert false

let parse_tactic t vexpr  =
  let open Sexplib.Sexp in
  match[@warning "-8"] t with
  | List (
    _ :: _ :: _ ::
    List (List (_ :: ((List (_ :: (List ((List (_ :: _ :: (
      List (_ :: (Atom str :: _)) :: _))) :: _) :: _)) :: _))) :: _) :: _
  ) ->
    get_tactic str vexpr


let parse_proof (asts: Vernacexpr.vernac_expr list) =
  let program_id = ref 0 in
  let steps = ref [] in

  List.iter (fun vexpr ->
      match vexpr with
      | Vernacexpr.VernacExtend (ename, args) ->
        let tactic_arg = List.nth args 2 in (* args = [selector; flag; tactic; default] *)
        let t = Serlib.Ser_genarg.sexp_of_raw_generic_argument tactic_arg in
        let step  = parse_tactic t vexpr in
        print_endline @@ show_step step;
        steps := step :: !steps;
      | _ ->
        steps := !steps;

      program_id := !program_id + 1;
  ) asts;
  
  print_endline @@ show_steps !steps;
  ()

let () =
  let dec_str, rest = handle_decs asts in
  print_endline dec_str;

  let spec_str, rest' = handle_spec rest in
  print_endline spec_str;

  let mp (x: Vernacexpr.vernac_control_r CAst.t) = x.v.expr in
  let rest'' = List.map mp rest' in
  parse_proof rest'';
  (* let lemma, rest'  List.hd @@ rest, List.tl @@ rest in *)
  (* let spec, rest'' = parse_spec lemma in *)
  ()
