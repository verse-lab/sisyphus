open Containers
open Proof_spec.Script
module StringMap = Map.Make(String)


type proof = step list
type script = {
  prelude: string;
  import: string * string;
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
    print_endline @@ Format.sprintf "%7s\n%a\n------------------%!" (get_tag v.v.expr) Pp.pp_with (Serapi.Serapi_protocol.gen_pp_obj Environ.empty_env Evd.empty ast);
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

let tactics = ["xcf"; "xpullpure"; "xapp"; "xdestruct"; "rewrite"; "destruct"; "xmatch_case"; "xmatch"; "xvalemptyarr"; "xalloc"; "xletopaque"; "xvals"; "apply"; "intros"; "sep_split_tuple"; "admitted"; "xseq"]

let get_tactic str vexpr incr_pid : step  =
  let vexpr_str = vexpr_to_string vexpr in
  try
    match (List.find (fun t -> String.prefix ~pre:t str) tactics) with
    | "xcf" -> `Xcf vexpr_str
    | "xpullpure" -> `Xpullpure vexpr_str
    | "xapp" ->
      `Xapp (incr_pid (), "func", [], [])
    | "xdestruct" -> `Xdestruct vexpr_str
    | "rewrite" -> `Rewrite vexpr_str
    | "xmatch_case" | "xmatch" ->
      `Xmatchcase  vexpr_str
    | "xvalemptyarr" ->
      `Xvalemptyarr (incr_pid (), vexpr_str)
    | "xalloc" ->
      `Xalloc (incr_pid (), vexpr_str)
    | "xletopaque" ->
      `Xletopaque (incr_pid (), vexpr_str)
    |  "xvals" ->
      `Xvals (incr_pid (), vexpr_str)
    | "sep_split_tuple" ->
      `SepSplitTuple vexpr_str
    | "xseq" ->
      `Xseq vexpr_str
    | _ -> assert false
  with
  | Not_found -> assert false

let parse_tactic sexp vexp incr_pid : step option =
  let open Sexplib.Sexp in
  match sexp with
  | List (
    _ :: _ :: _ ::
    List (List (_ :: ((List (_ :: (List ((List (_ :: _ :: (
      List (_ :: (Atom str :: _)) :: _))) :: _) :: _)) :: _))) :: _) :: _
  ) ->
    let step = get_tactic str vexp incr_pid in
    Some step
  | _ -> None

let parse_apply_intros sexp vexp : step option =
  let open Sexplib.Sexp in
  match sexp with
  | List (
      _ :: _ :: _ ::
      List (List (_ :: ((List (_ :: (List (Atom x :: _)) :: _) :: _))) :: _) :: _
    )
    ->
    begin match x with
    | "TacApply" -> Some (`Apply (vexpr_to_string vexp))
    | "TacIntroPattern" -> Some (`Intros (vexpr_to_string vexp))
    | _ -> None
    end
  | _ -> None

(* partitions based on bullet; assumes single-level case / destruct only; assume that a bullet immediately follows case *)
let partition_cases asts =
  let rec part_cases_aux asts curr acc =
    match asts with
    | [] -> (List.rev curr) :: acc
    | (Vernacexpr.VernacBullet x) :: t ->
      part_cases_aux t [] (List.rev curr :: acc)
    | h :: t ->
      part_cases_aux t (h :: curr) acc
  in
  List.rev (part_cases_aux (List.tl asts) [] [])


let rec find sexp str =
  let open Sexplib.Sexp in
  match sexp with
  | Atom _ -> None
  | List xs ->
    if List.exists (function | Atom x when String.equal x str -> true | _ -> false) xs
    then Some (List xs)
    else List.find_map (fun x -> find x str) xs


let rec find_all sexp str =
  let open Sexplib.Sexp in
  match sexp with
  | Atom _ -> None
  | List xs ->
    let rest = (List.flatten (List.filter_map (fun x -> find_all x str) xs)) in
    if List.exists (function | Atom x when String.equal x str -> true | _ -> false) xs
    then Some (List xs :: rest)
    else Some rest

let get_id sexp str =
  let open Sexplib.Sexp in
  match find sexp str  with
    | Some x ->
     begin match find x "Id" with
      | Some (List (_ :: Atom str :: _)) -> str
      | _ -> assert false
     end
    | _ -> assert false

let get_all_ids sexp =
  let open Sexplib.Sexp in
  begin match find_all sexp "Id" with
    | Some xs ->
      List.map (function | List (_ :: Atom str :: _) -> str | _ -> assert false) xs
    | _ -> []
  end

let get_str_ids sexp str =
  let open Sexplib.Sexp in
  match find sexp str with
  | Some x -> get_all_ids x
  | None -> []


let get_branches sexp =
  let open Sexplib.Sexp in
  match find sexp "IntroOrPattern" with
  | Some x ->
   begin match x with
     | List (_ :: List xs :: _) ->
       List.map (fun x -> get_all_ids x) xs
    | _ -> assert false
    end
  | _ -> assert false


let rec parse_case sexp vexp asts incr_pid : step option * Vernacexpr.vernac_expr list =
  let open Sexplib.Sexp in
  match sexp with
  | List (
      _ :: _ :: _ ::
      List (List (_ :: ((List (_ :: (List (Atom x :: _)) :: _) :: _))) :: _) :: _
    )
    ->
    begin match x with
      | "TacInductionDestruct" ->
        let case = get_id sexp "ElimOnIdent" in
        let eqn = get_id sexp "IntroIdentifier" in
        let ids = get_branches sexp in

        let parts = partition_cases asts in
        let parts_steps = List.map (fun xs -> parse_proof xs incr_pid)  parts in
        let parts_steps_names = List.combine ids parts_steps in
        Some (`Case (incr_pid (), case, eqn, parts_steps_names)), []
     | _ -> None, asts
    end
  | _ -> None, asts

and parse_proof (asts: Vernacexpr.vernac_expr list) incr_pid  =
  let rec parse_proof_aux asts steps  =
    match asts with
    | [] -> steps
    | vexp :: asts' ->
     match vexp with
      | Vernacexpr.VernacExtend (_, args) ->
        let step_arg = List.nth args 2 in
        let sexp = Serlib.Ser_genarg.sexp_of_raw_generic_argument step_arg in
        print_endline @@ Format.sprintf "%a" Sexplib.Sexp.pp_hum sexp;

        print_endline @@ vexpr_to_string vexp;

        let t_step = parse_tactic sexp vexp incr_pid in
        (match t_step with
        | Some step ->
          (* print_endline @@ show_step step; *)
          parse_proof_aux asts' (step :: steps)
        | None ->
          let o_step  = parse_apply_intros sexp vexp in
          match o_step with
          | Some step ->
            (* print_endline @@ show_step step; *)
            parse_proof_aux asts' (step :: steps)
          | None ->
            let c_step, rest = parse_case sexp vexp asts' incr_pid in
            match c_step with
            | Some step ->
              (* print_endline @@ show_steps steps; *)
              parse_proof_aux rest (step :: steps)
            | None ->
              parse_proof_aux asts' steps
        )
      | _ -> parse_proof_aux asts' steps
  in

  let steps = List.rev @@ (parse_proof_aux asts [])  in
  steps


let () =
  let dec_str, rest = handle_decs asts in
  print_endline dec_str;

  let spec_str, rest' = handle_spec rest in
  print_endline spec_str;

  let rest'' = List.map (fun (x : Vernacexpr.vernac_control_r CAst.t) -> x.v.expr) rest' in

  let incr_pid  =
    let id = ref 0 in
    fun () -> let oldvl = !id in incr id; oldvl in

  let steps = parse_proof rest'' incr_pid in
  print_endline @@ show_steps steps;
  (* let lemma, rest'  List.hd @@ rest, List.tl @@ rest in *)
  (* let spec, rest'' = parse_spec lemma in *)
  let module M = Sexplib.Sexp in
  ()

let unwrap_list = function
    Sexplib.Sexp.List xs -> xs
  | _ -> assert false

let unwrap_atom = function
    Sexplib.Sexp.Atom str -> str
  | _ -> assert false

let unwrap_tagged =
  let open Sexplib.Sexp in
  function [@warning "-8"]
  | List (Atom t :: args) -> t, args

let unwrap_value_binding =
  let open Sexplib.Sexp in  
  function [@warning "-8"]
  | List [Atom t; arg] -> t, arg

let unwrap_binding sexp =
  sexp
  |> unwrap_list
  |> List.map unwrap_value_binding
  |> StringMap.of_list

let unwrap_value_with_loc sexp =
  let binding = unwrap_binding sexp in
  let v = StringMap.find "v" binding in
  let loc = StringMap.find "loc" binding in
  v, loc

let tactics' = ["xcf"; "xpullpure"; "xapp"; "xdestruct"; "rewrite"; "destruct"; "xmatch_case"; "xmatch"; "xvalemptyarr"; "xalloc"; "xletopaque"; "xvals"; "apply"; "intros"; "sep_split_tuple"; "admitted"; "xseq"]

let unwrap_genarg sexp =
  match [@warning "-8"] unwrap_tagged sexp with
  | ("GenArg", [_raw; List [Atom _; Atom _tag]; binding]) ->
    let v, loc = unwrap_value_with_loc binding in
    _tag, v

let unwrap_tactic_name sexp =
  let open Sexplib.Sexp in
  match [@warning "-8"] unwrap_tagged sexp with
  | "KerName", [_; List [_; Atom id]] ->
    (List.find (fun t -> String.prefix ~pre:t id) tactics')

let unwrap_tacalias sexp =
  let open Sexplib.Sexp in
  match [@warning "-8"] unwrap_tagged sexp with
  | "TacAlias", [args] ->
    let [@warning "-8"] [name; params] = unwrap_list args in
    let name = unwrap_tactic_name name in
    let args = unwrap_list params in
    name, args

let unwrap_tacgeneric_arg sexp =
  let open Sexplib.Sexp in
  match [@warning "-8"] unwrap_tagged sexp with
  | "TacGeneric", [_; arg] ->
    let  [@warning "-8"] ("constr", exp) = unwrap_genarg arg in
    exp

let unwrap_cref sexp =
  let open Sexplib.Sexp in
  match [@warning "-8"] unwrap_tagged sexp with
  | "CRef", [binding; _] ->
    let v, _ = unwrap_value_with_loc binding in
    let _, [_; List [Atom "Id"; Atom cref]] = unwrap_tagged v in
    cref

let or_exn name sexp f =
  try f () with
  | Match_failure (pos,st,ed) ->
    failwith @@ Format.sprintf "unexpected form for %s (at %s:%d:%d): %a"
                  name pos st ed Sexplib.Sexp.pp_hum sexp

let rec unwrap_ty sexp : Lang.Type.t =
  let open Sexplib.Sexp in
  match unwrap_tagged sexp with
  | "CRef", _ ->
    begin match unwrap_cref sexp with
    | "func" -> Func
    | "int" -> Int
    | "loc" -> Loc
    | "unit" -> Unit
    | var -> Var var
    end
  | "CApp", [fname; args] ->
    let fname = 
      let fname, _ = unwrap_value_with_loc fname in
      unwrap_cref fname in
    let args = 
      let args = unwrap_list args
                 |> List.map (function List [data; _] ->
                   unwrap_value_with_loc data
                   |> fst
                   |> unwrap_ty
                 ) in
      args in
    begin match fname, args with
    | "list", [ty] -> List ty
    | "array", [ty] -> Array ty
    | "ref", [ty] -> Ref ty
    | adt, args -> ADT (adt, args)
    end
  | "CNotation", _ ->
    failwith @@ Format.sprintf "todo: implement support for product sexps: %a" Sexplib.Sexp.pp_hum sexp
[@@warning "-8"]


let unwrap_ty sexp =
  let open Sexplib.Sexp in
  or_exn "lambda type" sexp @@ fun () -> unwrap_ty sexp

let unwrap_lambda_arg sexp =
  let open Sexplib.Sexp in
  or_exn "lambda arg" sexp @@ fun () ->
  match unwrap_tagged sexp with
  | "CLocalAssum", [name; _; ty] ->
    let "Name", [List [Atom "Id"; Atom name]] =
      let [name] = unwrap_list name in
      unwrap_value_with_loc name
      |> fst
      |> unwrap_tagged in
    let ty =
      let ty, _ = unwrap_value_with_loc ty in
      unwrap_ty ty in
    (name, ty)
[@@warning "-8"]


let unwrap_clambda sexp = 
  match[@warning "-8"] unwrap_tagged sexp with
  | "CLambdaN", [args; body] ->
    let args = unwrap_list args
               |> List.map unwrap_lambda_arg in

    let body, _ = unwrap_value_with_loc body in
    args, body
  | _ -> failwith "found unexpected structure for "

let unwrap_expr sexp  =
  let open Sexplib.Sexp in
  match unwrap_tagged sexp with
  | "CRef", _ -> `Expr (`Var (unwrap_cref sexp))
  | "CLambdaN", _ -> `Spec (unwrap_clambda sexp)
  | tag, _ -> failwith @@ "found unhandled expr tag " ^ tag

let unwrap_spec_arg sexp  =
  let open Sexplib.Sexp in
  match unwrap_tagged sexp with
  | "CRef", _ -> `Expr (`Var (unwrap_cref sexp))
  | "CLambdaN", _ -> `Spec (unwrap_clambda sexp)
  | tag, _ -> failwith @@ "found unhandled expr tag " ^ tag


let unwrap_tac_capp sexp =
  let open Sexplib.Sexp in
  match [@warning "-8"] unwrap_tagged sexp with
  | "CApp", [fname; args] ->
    let fname = unwrap_value_with_loc fname
               |> fst
               |> unwrap_cref
    in
    let args = unwrap_list args
               |> List.map
                 (function [@warning "-8"] List [binding; _] ->
                  unwrap_value_with_loc binding |> fst)
   in
   fname, args

