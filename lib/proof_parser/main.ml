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


(* start parsing*)

(* parser state *)
type state = {
  mutable pid: Lang.Expr.program_id;
  mutable asts: Vernacexpr.vernac_expr list;
}

let with_current_pid state f =
  let id = state.pid in
  state.pid <- state.pid + 1;
  f id

let with_current_ast state f =
  let ast = List.hd state.asts in
  state.asts <- List.tl state.asts;
  f ast

let clear_state state =
  state.pid <- 0;
  state.asts <- []

let (let+) x f = x f

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

(* [ [v ...] [loc ...]]   *)
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

let unwrap_genarg sexp =
  match [@warning "-8"] unwrap_tagged sexp with
  | ("GenArg", [_raw; List [Atom _; Atom _tag]; binding]) ->
    let v, loc = unwrap_value_with_loc binding in
    _tag, v

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
    (`Var name, ty)
[@@warning "-8"]


let unwrap_clambda sexp =
  match unwrap_tagged sexp with
  | "CLambdaN", [args; body] ->
    let args = unwrap_list args
               |> List.map unwrap_lambda_arg in

    let body, _ = unwrap_value_with_loc body in
    args, body
  | _ ->
    failwith @@ Format.sprintf "found invalid structure for clambda expression: %a" Sexplib.Sexp.pp_hum sexp

let unwrap_int_literal sexp : int =
  let open Sexplib.Sexp in
  match unwrap_tagged sexp with
  | "Number", [List [Atom "SPlus"; List [List [Atom "int"; Atom n]; _frac; _exp]]] -> int_of_string n
  | _ ->
    failwith @@ Format.sprintf "found invalid structure for literal: %a" Sexplib.Sexp.pp_hum sexp

let rec unwrap_expr sexp : Lang.Expr.t =
  let open Sexplib.Sexp in
  match unwrap_tagged sexp with
  | "CRef", _ -> `Var (unwrap_cref sexp)
  | "CPrim", [num] -> `Int (unwrap_int_literal num)
  | "CNotation", [_; List[Atom "InConstrEntry"; Atom "( _ , _ , .. , _ )"]; List (List [fst'] :: List [List rest] :: _)] ->
    let elts = fst' :: rest in
    let elts = List.map (fun v -> unwrap_value_with_loc v |> fst |> unwrap_expr) elts in
    `Tuple elts
  | "CApp", [fname; args] ->
    let fname = fname |> unwrap_value_with_loc |> fst |> unwrap_cref in
    let args = unwrap_list args
               |> List.map (function
                     List [data; _] ->
                     unwrap_value_with_loc data
                     |> fst
                     |> unwrap_expr
                   | sexp -> failwith @@ Format.sprintf "found unexpected lambda structure in CApp %a"
                       Sexplib.Sexp.pp_hum sexp
                 ) in
    let is_uppercase c = Char.equal c (Char.uppercase_ascii c) in
    begin if String.get fname 0 |> is_uppercase
      then `Constructor (fname, args)
      else `App (fname, args)
    end
  | "CNotation", [_; List[Atom "InConstrEntry"; Atom ("_ ++ _" | "_ + _" | "_ - _" as op)]; List (List [l; r] :: _)] ->
    let l = unwrap_value_with_loc l |> fst |> unwrap_expr in
    let r = unwrap_value_with_loc r |> fst |> unwrap_expr in
    begin match op with
      | "_ ++ _" -> `App ("++", [l;r])
      | "_ + _" -> `App ("+", [l;r])
      | "_ - _" -> `App ("-", [l;r])
      | _ -> failwith "invalid assumptions"
    end
  (* lambdas.... CLambdaN not supported *)
  | tag, _ -> failwith @@ Format.sprintf "found unhandled expr (tag: %s): %a" tag Sexplib.Sexp.pp_hum sexp

let unwrap_assertion sexp : Proof_spec.Heap.Assertion.t =
  let open Sexplib.Sexp in
  match unwrap_tagged sexp with
  | "CNotation", [_; List[Atom "InConstrEntry"; Atom "_ ~> _"]; List (List [vl; body] :: _)] ->
    let vl = unwrap_value_with_loc vl |> fst |> unwrap_cref in
    let body =
      let body, _ = unwrap_value_with_loc body in
      unwrap_expr body in
    Proof_spec.Heap.(Assertion.emp |> Assertion.add_heaplet (PointsTo (vl, body)))
  | "CNotation", [_; List[Atom "InConstrEntry"; Atom notation]; _] ->
    failwith @@ Format.sprintf "found unknown notation %s" notation
  | tag, _ -> failwith @@ Format.sprintf "found unhandled assertion tag %s: %a" tag Sexplib.Sexp.pp_hum sexp

let unwrap_spec_arg sexp : spec_arg =
  let open Sexplib.Sexp in
  match unwrap_tagged sexp with
  | "CRef", _ -> `Expr (`Var (unwrap_cref sexp))
  | "CLambdaN", _ ->
    let args, body = unwrap_clambda sexp in
    let body = unwrap_assertion body in
    `Spec (args, body)
  | tag, _ -> failwith @@ "found unhandled expr tag " ^ tag

let unwrap_tac_capp sexp =
  let open Sexplib.Sexp in
  match [@warning "-8"] unwrap_tagged sexp with
  | "CApp", [fname; args] ->
    let fname = unwrap_value_with_loc fname
                |> fst
                |> unwrap_cref
    in
    let args  =
      unwrap_list args
      |> List.map
        (function [@warning "-8"] List [binding; _] ->
           unwrap_value_with_loc binding
           |> fst
           |> unwrap_spec_arg
        )
    in
    fname, args

let unwrap_tactic_name sexp =
  let tactics = ["xcf"; "xpullpure"; "xapp"; "xdestruct"; "rewrite"; "destruct"; "xmatch_case"; "xmatch"; "xvalemptyarr"; "xalloc"; "xletopaque"; "xvals"; "apply"; "intros"; "sep_split_tuple"; "admitted"; "xseq"] in

  let open Sexplib.Sexp in
  match [@warning "-8"] unwrap_tagged sexp with
  | "KerName", [_; List [_; Atom id]] ->
    (List.find (fun t -> String.prefix ~pre:t id) tactics)

let unwrap_tacalias sexp =
  let open Sexplib.Sexp in
  match [@warning "-8"] unwrap_tagged sexp with
  | "TacAlias", [args] ->
    let [@warning "-8"] [name; params] = unwrap_list args in
    let name = unwrap_tactic_name name in
    let args = unwrap_list params in
    name, args

let unwrap_prim_tactic sexp =
  let open Sexplib.Sexp in
  match [@warning "-8"] unwrap_tagged sexp with
  | "TacApply", args -> "apply", args
  | "TacIntroPattern", args -> "intros", args
  | "TacInductionDestruct", args -> "case", args
  | _ -> failwith "unhandled primitive tactic"

let unwrap_tacatom sexp =
  let open Sexplib.Sexp in
  match [@warning "-8"] unwrap_tagged sexp with
  | "TacAtom", [tac] ->
    unwrap_prim_tactic tac

let unwrap_xapp sexp =
  let arg = unwrap_tacgeneric_arg sexp in 
  match [@warning "-8"] unwrap_tagged arg with
  | "CRef", _ -> unwrap_cref arg, []
  | "CApp", _  -> unwrap_tac_capp arg
  | _ -> failwith "unhandled xapp argument type"


let get_tactic name args state : step =
  let vexpr_str = vexpr_to_string (List.hd state.asts) in
  match name with
  | "xcf" ->
    `Xcf vexpr_str
  | "xpullpure" -> `Xpullpure vexpr_str
  | "xapp" ->
    let+ id = with_current_pid state in
    let fname, spec_args = unwrap_xapp (List.hd args) in
    `Xapp (id, fname, spec_args)
  | "xdestruct" -> `Xdestruct vexpr_str
  | "rewrite" -> `Rewrite vexpr_str
  | "xmatch_case" | "xmatch" ->
    `Xmatchcase  vexpr_str
  | "xvalemptyarr" ->
    let+ id = with_current_pid state in
    `Xvalemptyarr (id, vexpr_str)
  | "xalloc" ->
    let+ id = with_current_pid state in
    `Xalloc (id, vexpr_str)
  | "xletopaque" ->
    let+ id = with_current_pid state in
    `Xletopaque (id, vexpr_str)
  |  "xvals" ->
    let+ id = with_current_pid state in
    `Xvals (id, vexpr_str)
  | "sep_split_tuple" ->
    `SepSplitTuple vexpr_str
  | "xseq" ->
    `Xseq vexpr_str
  | _ -> assert false

let get_id sexp =
  match [@warning "-8"] unwrap_list sexp with
  | [Atom "Id"; Atom id] -> id 

let unwrap_elem_ident sexp =
  let open Sexplib.Sexp in
  match [@warning "-8"] unwrap_tagged sexp with
  | "ElimOnIdent", [binding] ->
    let v, _ = unwrap_value_with_loc binding in
    v |> get_id

let unwrap_destr_id sexp =
  let open Sexplib.Sexp in
  match [@warning "-8"] unwrap_list sexp with
  | [_ ; id] -> unwrap_elem_ident id

let unwrap_eqn sexp =
  let open Sexplib.Sexp in
  match [@warning "-8"] unwrap_list sexp with
  | [binding] ->
    let v, _ = unwrap_value_with_loc binding in
    match [@warning "-8"] unwrap_list v with
    | [_; eqn] -> get_id eqn

let unwrap_intro_naming sexp =
  let open Sexplib.Sexp in
  let [@warning "-8"] v, _ = unwrap_value_with_loc sexp in
  match [@warning "-8"] unwrap_list v with
  | [_;  id] -> match [@warning "-8"] unwrap_list id with
    | [_; id] -> get_id id

let unwrap_intro_namings_or_nil sexp =
  let open Sexplib.Sexp in
  match [@warning "-8"] unwrap_list sexp with
  | [] -> []
  | vars ->
    List.map unwrap_intro_naming vars

let unwrap_intro_or_pattern sexp =
  let open Sexplib.Sexp in
  match [@warning "-8"] unwrap_tagged sexp with
  | "IntroOrPattern", [vars] ->
    let vars = unwrap_list vars in
    List.map unwrap_intro_namings_or_nil vars

let unwrap_vars sexp =
  let open Sexplib.Sexp in
  match [@warning "-8"] unwrap_list sexp with
  | [vars] ->
    let [@warning "-8"] _, [vars] = unwrap_tagged vars in
    let v, _ = unwrap_value_with_loc vars in
    unwrap_intro_or_pattern v


let unwrap_eqn_vars sexp =
  let open Sexplib.Sexp in
  let [@warning "-8"] [eqn; vars] = unwrap_list sexp in
  let eqn = unwrap_eqn eqn in
  let vars = unwrap_vars vars in
  eqn, vars

let unwrap_case sexp =
  let open Sexplib.Sexp in 
  match [@warning "-8"] sexp with
  | [_; _; args] ->
    let [@warning "-8"] [args; _] = unwrap_list args in
    let [@warning "-8"] [args] = unwrap_list args in
    let [@warning "-8"] [destr; eqn_vars; _] = unwrap_list args in
    let destr_id = unwrap_destr_id destr in
    let eqn, vars = unwrap_eqn_vars eqn_vars in
    destr_id, eqn, vars

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

let rec handle_case name args state =
  let+ id = with_current_pid state in
  let destr_id, eqn, vars = unwrap_case args in

  let parts = partition_cases (List.tl state.asts) in
  let parts_steps = List.map (fun part -> parse_proof { pid = state.pid; asts = part }) parts in
  let parts_steps_names = List.combine vars parts_steps in

  `Case (id, destr_id, eqn, parts_steps_names)

and get_prim_tactic name args state =
  let vexpr_str = vexpr_to_string (List.hd state.asts) in
  match name with
  | "apply" ->
    let+ _ = with_current_ast state in
    `Apply vexpr_str
  | "intros" ->
    let+ _ = with_current_ast state in
    `Intros vexpr_str
  | "case" ->
    let step = handle_case name args state in
    clear_state state;
    step

  | _ -> failwith "unhandled prim tactic"

and unwrap_tactic sexp state =
  let open Sexplib.Sexp in
  match [@warning "-8"] unwrap_tagged sexp with
  | "TacAlias", _ ->
    let name, args = unwrap_tacalias sexp in
    let step = get_tactic name args state in
    let+ _ = with_current_ast state in
    Some step
  | "TacAtom", _ ->
    let name, args = unwrap_tacatom sexp in
    let step = get_prim_tactic name args state in
    Some step
  | "TacThen", tac_bindings ->
    let texp = List.hd tac_bindings |> unwrap_value_with_loc |> fst in
    unwrap_tactic texp state
  | "TacArg", _ ->
    (* admit / admitted*)
    None

and parse_step sexp vexp state  =
  let sexp = sexp |> unwrap_genarg |> snd in
  unwrap_tactic sexp state

and parse_proof state =
  let rec parse_proof_aux steps lvl =
    match (state.asts) with
    | [] -> steps
    | vexp :: _ ->
      match vexp with
      | Vernacexpr.VernacExtend (_, args) when lvl = 0 ->
        let step_arg = List.nth args 2 in
        let sexp = Serlib.Ser_genarg.sexp_of_raw_generic_argument step_arg in

        let step = parse_step sexp vexp state in
        (match step with
         | Some step ->
           parse_proof_aux (step :: steps) lvl
         | None ->
           parse_proof_aux steps lvl
        )
      | Vernacexpr.VernacSubproof _  ->
        let+ _ = with_current_ast state in
        parse_proof_aux steps (lvl + 1)
      | Vernacexpr.VernacEndSubproof ->
        let+ _ = with_current_ast state in
        parse_proof_aux steps (lvl - 1)
      | _ ->
        let+ _ = with_current_ast state in
        parse_proof_aux steps lvl
  in

  let steps = List.rev @@ (parse_proof_aux [] 0)  in
  steps

let () =
  let dec_str, rest = handle_decs asts in
  print_endline dec_str;

  let spec_str, rest' = handle_spec rest in
  print_endline spec_str;

  let rest'' = List.map (fun (x : Vernacexpr.vernac_control_r CAst.t) -> x.v.expr) rest' in

  let state = { pid = 0; asts = rest'' } in

  let steps = parse_proof state in
  print_endline @@ show_steps steps;
  ()
