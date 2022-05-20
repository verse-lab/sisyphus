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

module Constants = struct
  (* assumption: no strings use *)
  type t = [
  | `Int of int
  | `Func of string
] [@@deriving eq, show, ord]
end

module ConstantSet = Set.Make (Constants)


let rec collect_expr: Lang.Expr.t -> Constants.t list = function
  | `Int i  -> [`Int i]
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

let rec collect_in =
  function
  | `Xapp (_, _, args) -> List.flat_map collect args
  | `Case (_, _, _, cases) ->
    List.flatten @@ List.flat_map (fun (_, steps) -> List.map collect_in steps) cases
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

      let is_case = function
        | `Case (_, _, _, _) -> true
        | _ -> false
      in

      if (curr >= from_id && curr <= to_id) || is_case h
      then
        (collect_in h) @ cc_aux t
      else cc_aux t
  in
  cc_aux steps |> ConstantSet.of_list |> ConstantSet.to_list


let steps =
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
  parsed_script.proof


type func = (Lang.Type.t list) * Lang.Type.t [@@deriving show]
module StringMap = Map.Make (String)
type func_map = func StringMap.t

let () =
  let cc  = collect_constants 4 4 steps in
  List.iter (fun x -> print_endline @@ Constants.show x) cc;

  let env = StringMap.empty in

  let open Lang.Type in
  let t_app  = [List (Var "A"); List Unit], List Unit in
  let t_make  = [Int; Unit], List Unit in
  let t_length = [List Unit], Int in
  let t_sub = [Int; Int], Int in
  let t_drop = [Int; List Unit], List Unit in 
  let map =
    env
    |> StringMap.add "++" t_app
    |> StringMap.add "make" t_make
    |> StringMap.add "length" t_length
    |> StringMap.add "-" t_sub
    |> StringMap.add "drop" t_drop
  in

  StringMap.iter (fun k v -> print_endline @@ k ^ " " ^ show_func v) map;

  let pats = Expr_generator.Patgen.pat_gen map steps in
  List.iter (fun ty_p -> print_endline @@ Expr_generator.Patgen.show_tag_pat ty_p ) pats;

  ()
