[@@@warning "-23"]
open Containers
module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

type t = {

  encoding_functions: (string * string) StringMap.t;
  (** [encoding_functions] represents a mapping from ADT type names to
     their encoding [of_list, to_list] functions. Currently we use
     lists as the common intermediate representation, but in theory a
     generic structured value encoding could be used. *)
  
  nested_proof_depth: int;
  (** [nested_proof_depth] indicates the depth of the current nested
     subproof - used to work out what symbol to use for subproof
     bullets. *)

  lambda: (Lang.Id.t * [ `Lambda of Lang.Expr.typed_param list * Lang.Expr.t Lang.Program.stmt ]) StringMap.t;
  (** [lambda] is a mapping of proof vars encoding lambdas to their
     corresponding definitions and observation points. *)

  bindings: string StringMap.t;
  (** [bindings] are a mapping of proof vars (i.e [idx]) to their
     corresponding program variables.

      This information is obtained purely mechanically during
     execution of the program and is required to handle renaming that
     might occur when creating fresh variables.  *)

  logical_mappings: string StringMap.t;
  (** [logical_mappings] are a mapping of logical mappings of concrete
     values (i.e [s]) to their corresponding logical variables [l]. *)  

  args: (string * Lang.Type.t) list;
  (** [args] are a full list of formal parameters to the function
     being evaluated *)

  ret_ty: Lang.Type.t;
  (** [ret_ty] is the type of the return of the function. *)

  gamma: Lang.Type.t StringMap.t;
  (** [gamma] is the typing environment for the OCaml program (i.e
     doesn't include proof terms) *)

  poly_vars: string list;
  (** [poly_vars] is a list of polymorphic variables.  *)

  logical_functions: string list;
  (** [logical_functions] is a list of any logical functions found in
     the specifications of functions used in the current program.  *)
}

let pp_lambda fmt (id, `Lambda (args, program)) =
  Format.fprintf fmt
    "%a :-> fun %a -> %a" Lang.Id.pp id
    (List.pp ~pp_sep:Format.pp_print_space Lang.Expr.pp_typed_param)
    args
    Lang.(Program.pp_stmt Expr.print_simple)
    program

let pp fmt (t: t) =
  Format.fprintf fmt
    "{\n Proof_env.t = %a;\n bindings = %a\n }"
    (StringMap.pp String.pp pp_lambda)
    t.lambda
    (StringMap.pp String.pp String.pp)
    t.bindings

let rec is_pure_ty : Lang.Type.t -> bool = function
  | Lang.Type.Int
  | Lang.Type.Unit
  | Lang.Type.Bool
  | Lang.Type.Var _ -> true
  | Lang.Type.ADT ("option", [ty], _)
  | Lang.Type.List ty -> is_pure_ty ty
  | Lang.Type.Product elts ->
    List.for_all is_pure_ty elts
  | Lang.Type.Func _
  | Lang.Type.Loc
  | Lang.Type.Array _
  | Lang.Type.Ref _
  | Lang.Type.ADT (_, _, _)
  | Lang.Type.Val -> false


let initial_env ?(enc_funs=[]) ?(logical_mappings=[]) ?(logical_functions=[]) ~ret_ty (args: (string * Lang.Type.t) list) =

  let encoding_functions = StringMap.of_list enc_funs in
  let logical_mappings = StringMap.of_list logical_mappings in

  (* bindings map proof vars to their corresponding program vars  *)
  let bindings =
    List.to_iter args
    |> Iter.map (fun (v, _ty) -> (v,v))
    |> StringMap.of_iter in
  let gamma = StringMap.of_list args in
  let poly_vars =
    List.fold_left
      (fun vars (_, ty) ->
         Lang.Type.poly_vars vars ty)
      StringSet.empty args
    |> StringSet.to_list
    |> List.map (fun s -> String.uppercase_ascii (String.drop 1 s)) in
  {
    encoding_functions;
    nested_proof_depth=0;
    lambda=StringMap.empty;
    bindings;
    logical_mappings;
    args; ret_ty;
    gamma;
    poly_vars;
    logical_functions;
  }

let with_nested_subproof env = {env with nested_proof_depth = env.nested_proof_depth + 1}
let bullet env = match env.nested_proof_depth with 0 -> "-" | 1 -> "+" | 2 -> "*" | n -> String.concat "" (List.init n (fun _ -> "+"))

let has_definition env v = StringMap.mem v env.lambda

let is_pure_lambda env v =
  StringMap.find_opt v env.lambda
  |> Option.exists (fun (_, body) -> Program_utils.is_pure body)

let add_binding env ~var ~ty =
  {env with gamma=StringMap.add var ty env.gamma}

let add_proof_binding env ~proof_var ~program_var =
  {env with bindings=StringMap.add proof_var program_var env.bindings}

let add_lambda_def (t: Proof_context.t) env name body =
  {env with lambda=StringMap.add name (t.current_program_id, body) env.lambda}

let find_pure_lambda_def env name =
  StringMap.find_opt name env.lambda
  |> Option.flat_map (Option.if_ (fun (_, body) -> Program_utils.is_pure body))

let env_to_defmap env =
  StringMap.map snd env.lambda

let normalize_observation env ((pure, heap): (Dynamic.Concrete.context * Dynamic.Concrete.heap_context)) =
  let rev_map = StringMap.to_list env.logical_mappings |> List.map Pair.swap |> StringMap.of_list in
  let pure = List.map (Pair.map_fst (fun v -> StringMap.find_opt v env.logical_mappings |> Option.get_or ~default:v)) pure in
  let mapped =
    List.filter_map (function
      | (v, `Array vls) when StringMap.mem v rev_map ->
        Some (StringMap.find v rev_map, `List vls)
      | (v, `PointsTo (`Opaque (_, vls))) when StringMap.mem v rev_map ->
        Some (StringMap.find v rev_map, `List vls)
      | (v, `PointsTo vl) when StringMap.mem v rev_map ->
        Some (StringMap.find v rev_map, vl)
      | _ -> None
    ) heap in
  
  (pure @ mapped,heap)

let find_to_list_function_for env (adt_name: string) =
  match StringMap.find adt_name env.encoding_functions with
  | (_, to_list) -> to_list
  | exception Not_found ->
    Format.ksprintf ~f:failwith "failed to find conversion functions for ADT %s (known mappings: %a)" adt_name
      (StringMap.pp String.pp (Pair.pp String.pp String.pp)) env.encoding_functions
