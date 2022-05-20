open Containers

(*
 [`App "++" [`PatVar "ls" foo; `PatVar "var2" foo]]
 [`App "++" [`PatVar "ls" foo; `App "make" foo]]


 [`App "-" [.., ...] ]

   ++ (make pp) (make pp)
   ++ p p 1
   ++ (make pp) p 2
   ++ p (make pp) 2
   ++ (make pp) (make pp) 2 

   ++ p p -> list
   ++ p [make p p] -> list

   make p p -> list
   make [- p p] p -> list

   - p p -> int
   - [length p] p -> int
   - p [length p] -> int
   - [length p] [length p] -> int (COMBINATORIAL)
 *)

type pat =
  [ `App of string * pat list
  | `Constructor of string * pat list
  | `Int of int
  | `Tuple of pat list
  | `Var of string
  | `PatVar of string * Lang.Type.t
  ]
[@@deriving eq, ord, show]

type tag_pat = Lang.Type.t * pat
[@@deriving show]

module StringMap = Map.Make (String)


let gen_product ls =
  let (let+) x f = List.(>>=) x f in
  let rec loop = function
    | h :: t ->
      let+ h_elt = h in
      let+ t_elt = loop t in
      List.return (h_elt :: t_elt)
    | _ -> List.return [] in
  loop ls

let construct_pat_vars fname input_types =
  let construct_pat_var fname idx ty =
    `PatVar (Format.sprintf "%s %s" "arg" (string_of_int idx), ty)
  in
  List.mapi (fun i ty -> construct_pat_var fname i ty) input_types


let gen_lvl_zero_pat types fname  =
  let input_types, ret_type = StringMap.find fname types in
  let pat_vars = construct_pat_vars fname input_types in
  let pat = `App (fname, pat_vars) in
  (ret_type, pat), pat_vars

let gen_at_expr_no_recur types (pat_var: pat ) = function
  | `App (fname, args) ->
    let (_, pat), _ = gen_lvl_zero_pat types fname in
    [pat; pat_var]
  | _ -> [pat_var]

let rec gen_at_apply types fname args =
  let input_types, ret_type = StringMap.find fname types in
  let pat_vars = construct_pat_vars fname input_types in 

  let arg_pat_vars = List.combine args pat_vars in
  let tag_pats =
    List.map (fun (arg, pat_var) -> gen_at_expr_no_recur types pat_var arg) arg_pat_vars
    |> gen_product
    |> List.map (fun (arg_pats) -> ret_type, `App (fname, arg_pats))
  in

  (* recurse on args*)
  tag_pats @ List.flat_map (fun x -> gen_at_expr types x) args

and gen_at_expr types  = function
  | `App (fname, args) ->
    gen_at_apply types fname args
  | `Constructor (_, es) ->
    List.flat_map (fun x -> gen_at_expr types x) es
  | _ -> []


let gen_at_spec_arg types = let open Proof_spec.Heap in function
    | `Expr e -> []
    | `Spec (_, asn) ->
      let gen_at_heaplet = function
        | Heaplet.PointsTo (_, e) -> gen_at_expr types e in
      List.flat_map gen_at_heaplet (Assertion.sigma asn)
    | `Hole -> failwith "holes not supported"

let rec gen_at_step types step = match step with 
  | `Xapp (_, _, args) -> List.flat_map (fun x -> gen_at_spec_arg types x) args
  | `Case (_, _, _, cases) ->
    List.flatten @@ List.flat_map (fun (_, steps) -> List.map (fun x -> gen_at_step types x) steps) cases
  | _ -> []

(* generate patterns from ALL possible steps, regardless of program ID *)
let pat_gen types steps  =
  let rec pat_gen_aux types steps  =
    match steps with
    | [] -> []
    | h :: t ->
      gen_at_step types h @ pat_gen_aux types t
  in
  pat_gen_aux types steps

