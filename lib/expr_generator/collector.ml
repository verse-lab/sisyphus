open Containers
module PS = Proof_spec
module PatternSet = Set.Make (struct
    type t = Lang.Type.t * Types.pat [@@deriving eq, ord, show]
  end)

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
      | Heaplet.PointsTo (_, _, e) ->  collect_expr cs e in
    List.fold_left collect_heaplet cs (Assertion.sigma asn)
    |> Fun.flip (List.fold_left collect_expr) (Assertion.phi asn)

  | `Hole -> failwith "holes not supported"

let collect_constants ?from_id ?to_id (steps: Proof_spec.Script.step list) =
  let collect_step cs : PS.Script.step -> _ = function
    | `Xapp (_, _, spec_args) ->
      List.fold_left collect_spec_arg cs spec_args
    | `Xif _ | `Xinhab _
    | `SepSplitTuple _ | `Xmatchcase _ |`Intros _ |`Xpurefun _ |`Xvals _
    | `Xvalemptyarr _ |`Case _ |`Xletopaque _ |`Xdestruct _ |`Xalloc _
    | `Xref _ | `Xunit _ | `Xsimpl _ | `XappOpaque _
    |`Apply _ |`Xseq _ |`Rewrite _ |`Xcf _ |`Xpullpure _ -> cs in
  PS.Script.fold_proof_script ?start:from_id ?stop:to_id
    collect_step ConstantSet.empty steps
  |> ConstantSet.to_list


(** [get_consts_and_funcs ~from_id ~to_id ~env script] when given a
    proof script [script], retrieves constants and functions used
    between proof points [from_id] and [to_id]. *)
let collect_consts_and_funcs ?from_id ?to_id ~(env: Types.env) steps =
  let open Lang.Type in
  (* collect constants used in script *)
  let consts_in_script = collect_constants ?from_id ?to_id steps in
  (* collect a typemap of constants (ints + variables) *)
  let consts =
    List.to_iter consts_in_script
    |> Iter.filter_map (function `Int i -> Some (`Int i) | _ -> None)
    |> Iter.fold (Fun.flip Types.update_binding Int) Types.TypeMap.empty  in
  (* collect a typemap of functions by return type *)
  let funcs =
    let add_to_map map = function
      | `Func fname ->
        (env fname)
        |> List.fold_left (fun map (args, ret_ty) ->
          Types.update_binding map ret_ty (fname, args)) map
      | _ -> map in
    List.fold_left add_to_map Types.TypeMap.empty consts_in_script in
  consts, funcs


let gen_lvl_zero_pat (env: Types.env) fname  =
  List.fold_left (fun acc (input_types, ret_type) ->
    let pat_vars =
      List.mapi (fun i ty ->
        `PatVar (Format.sprintf "arg_%d" i, ty)
      ) input_types in
    let pat = `App (fname, pat_vars) in
    ((ret_type, pat), pat_vars) :: acc
  ) [] (env fname)


let collect_at_expr_no_recur (env: Types.env) expr pat_var =
  match expr with
  | `App (fname, args) ->
    let zero_pat =
      gen_lvl_zero_pat env fname
      |> List.map Fun.(snd % fst) in
    zero_pat @ [pat_var]
  | _ -> [pat_var]

let rec collect_at_apply env ps fname args =
  List.fold_left (fun ps (input_types, ret_type) ->
    let pat_vars =
      List.mapi (fun i ty ->
        `PatVar (Format.sprintf "arg_%d" i, ty)
      ) input_types in
    let tag_pats =
      List.combine args pat_vars
      |> List.map (Fun.uncurry (collect_at_expr_no_recur env))
      |> List.cartesian_product
      |> List.map (fun (arg_pats) -> ret_type, `App (fname, arg_pats)) in
    (* recurse on args*)
    let ps = PatternSet.add_list ps tag_pats in
    List.fold_left (collect_at_expr env) ps args
  ) ps (env fname)

and collect_at_expr env ps = function
  | `App (fname, args) ->
    collect_at_apply env ps fname args
  | `Constructor (_, es) ->
    List.fold_left (collect_at_expr env) ps es
  | _ -> ps

let collect_at_spec_arg env ps = function
  | `Expr _ -> ps
  | `Spec (_, asn) ->
    let collect_at_heaplet ps (PointsTo (_, _, e) : Proof_spec.Heap.Heaplet.t) =
      collect_at_expr env ps e in

    let old_invariant_size_pure =
      Proof_spec.Heap.Assertion.phi asn
      |> List.map Lang.Expr.size
      |> List.reduce (+)
      |> Option.value ~default:0 in
    let old_invariant_size_heap =
      Proof_spec.Heap.Assertion.sigma asn
      |> List.map (fun (PointsTo (_, _, e): Proof_spec.Heap.Heaplet.t) -> Lang.Expr.size e)
      |> List.reduce (+)
      |> Option.value ~default:0 in
    Configuration.stats_set_count "old-invariant-size-pure" old_invariant_size_pure;
    Configuration.stats_set_count "old-invariant-size-heap" old_invariant_size_heap;
    Configuration.stats_set_count "old-invariant-size" (old_invariant_size_pure + old_invariant_size_heap);
    let old_invariant_depth_pure =
      Proof_spec.Heap.Assertion.phi asn
      |> List.map Lang.Expr.depth
      |> List.reduce (+)
      |> Option.value ~default:0 in
    let old_invariant_depth_heap =
      Proof_spec.Heap.Assertion.sigma asn
      |> List.map (fun (PointsTo (_, _, e): Proof_spec.Heap.Heaplet.t) -> Lang.Expr.depth e)
      |> List.reduce (+)
      |> Option.value ~default:0 in

    Configuration.stats_set_count "old-invariant-depth-pure" old_invariant_depth_pure;
    Configuration.stats_set_count "old-invariant-depth-heap" old_invariant_depth_heap;
    Configuration.stats_set_count "old-invariant-depth" (Int.max old_invariant_depth_pure old_invariant_depth_heap);

    List.fold_left collect_at_heaplet ps (Proof_spec.Heap.Assertion.sigma asn)
  | `Hole -> failwith "holes not supported"

let collect_pats ?from_id ?to_id ~env steps =
  let collect_pats_at_step env ps = function
    | `Xapp (_, _, args) ->
      List.fold_left (collect_at_spec_arg env) ps args
    | _ -> ps in
  steps
  |> Proof_spec.Script.fold_proof_script ?start:from_id ?stop:to_id
       (collect_pats_at_step env) PatternSet.empty 
  |> PatternSet.to_list
  |> List.fold_left (fun env (ty,vl) ->
    Types.update_binding env ty vl
  ) (Types.TypeMap.empty)
