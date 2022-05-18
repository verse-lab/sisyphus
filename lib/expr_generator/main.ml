open Containers

type pat =
  [ `App of string * pat list
  | `Constructor of string * pat list
  | `Int of int
  | `Tuple of pat list
  | `Var of string
  | `PatVar of string * Lang.Type.t
  ]
[@@deriving eq, ord]

type expr = [
  | `Int of int
  | `Func of string
]

let show_expr = function
  | `Int i -> string_of_int i
  | `Func fname -> fname

(* assumption: no strings used*)
let rec collect_expr : Lang.Expr.t -> expr list = function
  | `Int _ as e -> [e]
  | `App (fname, exps)  ->
    [`Func fname] @ List.flat_map collect_expr exps
  | `Constructor (_, es) ->
    List.flat_map collect_expr es
  | _ ->
    []

let collect = let open Proof_spec.Heap in function
    | `Expr e -> collect_expr e
    | `Spec (_, asn) ->
      let collect_heaplet = function
        | Heaplet.PointsTo (_, e) ->  collect_expr e in
       List.flat_map collect_heaplet (Assertion.sigma asn)
    | `Hole -> failwith "holes not supported"

let collect_in =
  function
  | `Xapp (_, _, args) ->
    List.iter (fun x -> print_endline @@ Proof_spec.Script.show_spec_arg x) args;
    let ls = List.flat_map collect args in
    print_endline @@ string_of_int @@ List.length ls;
    ls
  | _ ->
    []

let collect_constants from_id to_id (steps: Proof_spec.Script.step list)  =
  let rec cc_aux steps =
    match steps with
    | [] -> []
    | h :: t ->
      let curr = match h with
        | `Xapp (id, _, _) | `Case (id, _, _, _) | `Xvalemptyarr (id, _)  | `Xalloc (id, _) | `Xletopaque (id, _)  | `Xvals (id, _) -> id
        | _ -> -1 (* assume: from_id >= 0 *)
      in

      print_endline @@ string_of_int curr;

      if curr >= from_id && curr <= to_id
      then
        (collect_in h) @ cc_aux t
      else cc_aux t
  in
  cc_aux steps


let () =
  let proof_str = IO.with_in "../../resources/seq_to_array/Verify_seq_to_array_old.v" IO.read_all in
  let dir = "../../_build/default/resources/seq_to_array" in
  let module Ctx =
    Coq.Proof.Make(struct
      let verbose = false
      let libs = [
        Coq.Coqlib.make
          ~path:(Fpath.of_string dir |> Result.get_exn)
          "Proofs"
      ]
    end) in

  let parsed_script = Proof_parser.Parser.parse (module Ctx) proof_str in
  Proof_spec.Script.pp_parsed_script parsed_script;

  let steps = parsed_script.proof in
  let case = List.nth steps 5 in

  let steps = match [@warning "-8"] case with
    | `Case (_, _, _, (_ :: (_, steps) :: _)) -> steps
  in

  let xapp = List.nth steps 4 in
  print_endline @@ Proof_spec.Script.show_step xapp;

  let cc  = collect_constants 0 10 [xapp] in
  List.iter (fun x -> print_endline @@ show_expr x) cc;
  ()





