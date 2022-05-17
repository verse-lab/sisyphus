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

(* assumption: no strings used*)
let collect_expr = function
  | `App (_, _) | `Int _ as e  -> Some e
  | _ -> None

let collect = let open Proof_spec.Heap in function
  | `Expr e ->
    [collect_expr e]
  | `Spec (_, asn) ->
    let collect_heaplet = function
      | PointsTo (_, e) -> collect_expr e in 
   List.filter_map Fun.id (fold (fun acc x -> collect_heaplet x :: acc ) [] asn.sigma)
  | `Hole -> failwith "holes not supported"

let collect_in = function
  | `Xapp (_, _, args) ->
    List.flat_map collect args
  | _ -> []

let collect_constants from_id to_id steps =
  let rec cc_aux steps =
    match steps with
    | [] -> []
    | h :: t ->
      let curr = match h with
      | `Xapp (id, _, _, _) :: _
      | `Case (id, _, _, _) :: _
      | `Xvalemptyarr (id, _, _) :: _
      | `Xalloc (id, _, _) :: _
      | `Xletaopaque (id, _, _) :: _
      | `Xvals (id, _, _) :: _ -> id
      | _ -> -1 in

      if curr >= from_id && curr <= to_id
      then (collect_in h) @ cc_aux t
      else cc_aux t
  in
  cc_aux steps


