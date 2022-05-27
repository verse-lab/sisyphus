open Containers
module PS = Proof_spec

module Constants = struct
  (* assumption: no strings use *)
  type t = [
    | `Int of int
    | `Func of string
  ] [@@deriving eq, show, ord]
end

module ConstantSet = Set.Make (Constants)

let rec collect_expr cs = function
  | `Int i  -> ConstantSet.add (`Int i) cs
  | `App (fname, args)  ->
    List.fold_left collect_expr
      (ConstantSet.add (`Func fname) cs)
      args
  | `Constructor (_, args) ->
    List.fold_left collect_expr cs args
  | _ -> cs

let collect_spec_arg cs =
  let open Proof_spec.Heap in
  function
  | `Expr e -> collect_expr cs e
  | `Spec (_, asn) ->
    let collect_heaplet cs = function
      | Heaplet.PointsTo (_, e) ->  collect_expr cs e in
    List.fold_left collect_heaplet cs (Assertion.sigma asn)
  | `Hole -> failwith "holes not supported"


let collect_constants from_id to_id (steps: Proof_spec.Script.step list) =
  let collect_step cs : PS.Script.step -> _ = function
    | `Xapp (_, _, spec_args) ->
      List.fold_left collect_spec_arg cs spec_args
    | `SepSplitTuple _ | `Xmatchcase _ |`Intros _ |`Xpurefun _ |`Xvals _
    | `Xvalemptyarr _ |`Case _ |`Xletopaque _ |`Xdestruct _ |`Xalloc _
    |`Apply _ |`Xseq _ |`Rewrite _ |`Xcf _ |`Xpullpure _ -> cs
  in

  PS.Script.fold_proof_script ~start:from_id ~stop:to_id
    collect_step ConstantSet.empty steps
           |> ConstantSet.to_list
