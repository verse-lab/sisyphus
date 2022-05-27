open Containers
module PS = Proof_spec

module PatternSet = Set.Make (struct
    type t = Expgen.tag_pat [@@deriving eq, ord, show]
  end)

let construct_pat_vars fname input_types =
  let construct_pat_var fname idx ty =
    `PatVar (Format.sprintf "%s %s" "arg" (string_of_int idx), ty)
  in
  List.mapi (fun i ty -> construct_pat_var fname i ty) input_types

let gen_lvl_zero_pat env fname  =
  let input_types, ret_type = env fname in
  let pat_vars = construct_pat_vars fname input_types in
  let pat = `App (fname, pat_vars) in
  (ret_type, pat), pat_vars

let gen_at_expr_no_recur types pat_var = function
  | `App (fname, args) ->
    let (_, pat), _ = gen_lvl_zero_pat types fname in
    [pat; pat_var]
  | _ -> [pat_var]

let rec gen_at_apply env ps fname args =
  let input_types, ret_type = env fname in
  let pat_vars = construct_pat_vars fname input_types in

  let arg_pat_vars = List.combine args pat_vars in
  let tag_pats : (Expgen.tag_pat list) =
    List.map (fun (arg, pat_var) -> gen_at_expr_no_recur env pat_var arg) arg_pat_vars
    |> List.cartesian_product
    |> List.map (fun (arg_pats) -> ret_type, `App (fname, arg_pats))
  in

  (* recurse on args*)
  let ps = PatternSet.add_list ps tag_pats in
  List.fold_left (gen_at_expr env) ps args

and gen_at_expr env ps = function
  | `App (fname, args) ->
    gen_at_apply env ps fname args
  | `Constructor (_, es) ->
    List.fold_left (gen_at_expr env) ps es
  | _ -> ps


let gen_at_spec_arg env ps = let open Proof_spec.Heap in function
    | `Expr e -> ps
    | `Spec (_, asn) ->
      let gen_at_heaplet ps = function
        | Heaplet.PointsTo (_, e) -> gen_at_expr env ps e in
      List.fold_left gen_at_heaplet ps (Assertion.sigma asn)
    | `Hole -> failwith "holes not supported"

(* generate patterns from ALL possible steps, regardless of program ID *)
let gen_pats steps ~from_id ~to_id ~env : Expgen.tag_pat list =
  let gen_pats_at_step env ps = function
    | `Xapp (_, _, args) ->
      List.fold_left (gen_at_spec_arg env) ps args
    | _ -> ps
  in

  PS.Script.fold_proof_script ~start:from_id ~stop:to_id
    (gen_pats_at_step env) PatternSet.empty steps
  |> PatternSet.to_list 


let get_pat_type_map (env: string -> Expgen.func_type) (pats: Expgen.tag_pat list) =
  let add_type type_map = function
    | (ty, pat) -> Expgen.TypeMap.update ty (function Some ls -> Some (pat :: ls) | None -> Some [pat]) type_map
  in
  List.fold_left add_type (Expgen.TypeMap.empty) pats
