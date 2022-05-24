open Containers

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

