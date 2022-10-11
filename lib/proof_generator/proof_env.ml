[@@@warning "-23"]
open Containers
module StringMap = Map.Make(String)

type t = {
  lambda: (Lang.Id.t * [ `Lambda of Lang.Expr.typed_param list * Lang.Expr.t Lang.Program.stmt ]) StringMap.t;
  (** mapping of proof vars encoding lambdas to their corresponding definitions and observation points. *)
  bindings: string StringMap.t;
  (** mapping of proof vars (i.e [idx]) to their corresponding program variables.  *)
  logical_mappings: string StringMap.t;
  (** mapping of logical mappings of concrete values (i.e [s]) to their corresponding logical variables [l].  *)  
  args: (string * Lang.Type.t) list;
  (** full list of formal parameters to the function being evaluated *)
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
  | Lang.Type.List ty -> is_pure_ty ty
  | Lang.Type.Product elts ->
    List.for_all is_pure_ty elts
  | Lang.Type.Func _
  | Lang.Type.Loc
  | Lang.Type.Array _
  | Lang.Type.Ref _
  | Lang.Type.ADT (_, _, _)
  | Lang.Type.Val -> false

let initial_env ?(logical_mappings=[]) (args: (string * Lang.Type.t) list) =

  let logical_mappings = StringMap.of_list logical_mappings in
  let bindings =
    List.to_iter args
    |> Iter.filter_map (fun (v, ty) ->
      if is_pure_ty ty
      then Some (v,v)
      else StringMap.find_opt v logical_mappings
           |> Option.map (fun bv -> (bv, v))
    )
    |> StringMap.of_iter in
  {
    lambda=StringMap.empty;
    bindings;
    logical_mappings;
    args;
  }

let has_definition env v = StringMap.mem v env.lambda

let is_pure_lambda env v =
  StringMap.find_opt v env.lambda
  |> Option.exists (fun (_, body) -> Program_utils.is_pure body)

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
  let pure = List.map (Pair.map_fst (fun v -> StringMap.find_opt v env.logical_mappings |> Option.get_or ~default:v)) pure in
  (pure,heap)

    
