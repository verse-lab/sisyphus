open Containers

module Log = (val Logs.src_log (Logs.Src.create ~doc:"Parses proof scripts" "prf-parser.core"))

let to_vernac = let open Serapi.Serapi_protocol in function [@warning "-8"]
    | CoqAst {v = {control; attrs; expr}; _} -> Some expr
    | _ -> None

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

let handle_decs asts  =
  let open Serapi.Serapi_protocol in

  let is_dec obj  =
    match (to_vernac obj) with
    | Some (Vernacexpr.VernacSetOption (_, _, _)) | Some (Vernacexpr.VernacRequire (_, _, _)) -> true
    | _ -> false
  in

  let decs, rest = List.partition is_dec asts in
  let decs = List.map Print_utils.string_of_coq_obj decs in

  let last_idx = List.length decs - 1 in
  let prelude, import = List.take last_idx decs, List.nth decs last_idx in
  let import = Str.bounded_split (Str.regexp "Import ") import 2 in
  let import = List.hd import ^ "Import", List.nth import 1 in

  let prelude_str = List.fold_left (^) "" prelude in
  prelude_str, import, rest

let handle_spec asts =
  match asts with
  | spec :: rest -> Print_utils.string_of_coq_obj spec, rest
  | _ ->
    Format.ksprintf ~f:failwith "Failed to parse proof script. Script terminated prematurely; maybe some library failed to load?"

let get_tactic name args state : Proof_spec.Script.step =
  let vexpr_str = Print_utils.string_of_vexp (List.hd state.asts) in
  match name with
  | "xcf" ->
    `Xcf vexpr_str
  | "xpullpure" -> `Xpullpure vexpr_str
  | "xapp" when List.compare_length_with args 1 = 0 ->
    let+ id = with_current_pid state in
    let fname, spec_args = Parser_utils.unwrap_xapp (List.hd args) in
    `Xapp (id, fname, spec_args)
  | "xapp" when List.is_empty args ->
    let+ id = with_current_pid state in
    `XappOpaque (id, vexpr_str)
  | "xsimpl" ->
    `Xsimpl vexpr_str
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
  | "xref" ->
    let+ id = with_current_pid state in
    `Xref (id, vexpr_str)
  | "xunit" ->
    let+ id = with_current_pid state in
    `Xunit (id, vexpr_str)
  |  "xvals" ->
    let+ id = with_current_pid state in
    `Xvals (id, vexpr_str)
  | "sep_split_tuple" ->
    `SepSplitTuple vexpr_str
  | "xseq" ->
    `Xseq vexpr_str
  | name ->
    Format.ksprintf ~f:failwith
      "Failed to parse proof script. Unsupported tactic %s; args [%a]"
      name (List.pp Sexplib.Sexp.pp) args


(* partitions based on bullet; assumes single-level case / destruct
   only; assume that a bullet immediately follows case *)
let partition_cases asts =
  let rec part_cases_aux asts curr acc lvl =
    match asts with
    | [] -> (List.rev curr) :: acc
    | (Vernacexpr.VernacBullet x) :: t when lvl = 0 ->
      part_cases_aux t [] (List.rev curr :: acc) lvl
    | h :: t ->
      let lvl = match h with
        | Vernacexpr.VernacSubproof _ -> lvl + 1
        | Vernacexpr.VernacEndSubproof -> lvl - 1
        | _ -> lvl
      in
      part_cases_aux t (h :: curr) acc lvl
  in
  List.rev (part_cases_aux (List.tl asts) [] [] 0)

let rec handle_case name args state =
  let destr_id, eqn, vars = Parser_utils.unwrap_case args in

  let parts = partition_cases (List.tl state.asts) in
  let parts_steps = List.map (fun part -> parse_proof { pid = state.pid; asts = part }) parts in
  let parts_steps_names = List.combine vars parts_steps in

  `Case (state.pid, destr_id, eqn, parts_steps_names)

and get_prim_tactic name args state =
  let vexpr_str = Print_utils.string_of_vexp (List.hd state.asts) in
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
  match [@warning "-8"] Parser_utils.unwrap_tagged sexp with
  | "TacAlias", _ ->
    let name, args = Parser_utils.unwrap_tacalias sexp in
    let step = get_tactic name args state in
    let+ _ = with_current_ast state in
    Some step
  | "TacAtom", _ ->
    let name, args = Parser_utils.unwrap_tacatom sexp in
    let step = get_prim_tactic name args state in
    Some step
  | "TacThen", tac_bindings ->
    let texp = List.hd tac_bindings |> Parser_utils.unwrap_value_with_loc |> fst in
    unwrap_tactic texp state
  | "TacArg", _ ->
    (* admit / admitted*)
    None

and parse_step sexp vexp state  =
  let sexp = sexp |> Parser_utils.unwrap_genarg |> snd in
  unwrap_tactic sexp state

and parse_proof state =
  Log.debug (fun f -> f "Parsing proof now");
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

let handle_script rest =
  let rest = List.filter_map to_vernac rest in
  let state = { pid = 0; asts = rest } in
  parse_proof state

let retrieve_ast (module Ctx: Coq.Proof.PROOF) proof_str =
  Ctx.reset ();
  Ctx.add proof_str;
  let start = Ctx.size() - 1 in

  let query start  =
    Iter.int_range_by ~step:(-1) start 0
    |> Iter.filter_map (fun at -> Ctx.query ~at Serapi.Serapi_protocol.Ast)
    |> Iter.flat_map_l Fun.id in

  query start |> Iter.to_list

let parse ctx proof_str : Proof_spec.Script.script =
  let asts = retrieve_ast ctx proof_str in
  let prelude, import, rest = handle_decs asts in
  let spec_str, rest = handle_spec rest in
  let steps = handle_script rest in

  {
    prelude;
    import;
    spec = spec_str;
    proof = steps;
  }
