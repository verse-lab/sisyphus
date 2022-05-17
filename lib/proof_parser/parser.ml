open Containers

open Proof_spec.Script
open Coq_exec
open Print_utils
open Parser_utils

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
  let decs = List.map string_of_coq_obj decs in 

  let last_idx = List.length decs - 1 in
  let prelude, import = List.take last_idx decs, List.nth decs last_idx in
  let import = Str.bounded_split (Str.regexp "Import ") import 2 in 
  let import = List.hd import ^ "Import", List.nth import 1 in 

  let prelude_str = List.fold_left (^) "" prelude in
  prelude_str, import, rest

let handle_spec asts =
  string_of_coq_obj @@ List.hd asts, List.tl asts

let get_tactic name args state : step =
  let vexpr_str = string_of_vexp (List.hd state.asts) in
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
  let destr_id, eqn, vars = unwrap_case args in

  let parts = partition_cases (List.tl state.asts) in
  let parts_steps = List.map (fun part -> parse_proof { pid = state.pid; asts = part }) parts in
  let parts_steps_names = List.combine vars parts_steps in

  `Case (state.pid, destr_id, eqn, parts_steps_names)

and get_prim_tactic name args state =
  let vexpr_str = string_of_vexp (List.hd state.asts) in
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

let handle_script rest =
  let rest = List.filter_map Coq_exec.to_vernac rest in
  let state = { pid = 0; asts = rest } in
  parse_proof state

let parse proof_str dir : script =
  let asts = send_to_coq dir proof_str false in

  let prelude, import, rest = handle_decs asts in
  let spec_str, rest = handle_spec rest in
  let steps = handle_script rest in

  {
    prelude;
    import;
    spec = spec_str;
    proof = steps;
  }
