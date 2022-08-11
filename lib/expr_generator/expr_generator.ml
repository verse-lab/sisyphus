open Containers

module Types = Types

type env = string -> ((Lang.Type.t list) * Lang.Type.t) option

module StringMap = Map.Make(String)

let (let+) x f = x f

let rec gen_product_l (f : 'a -> 'b Gen.t) (ls: 'a Gen.t) : 'b list Gen.t =
  match ls () with
  | None -> Gen.of_list [ [] ]
  | Some hd ->
    let hd_elts = (f hd) in
    let tl_elts  = gen_product_l f ls in
    Gen.product hd_elts tl_elts
    |> Gen.map (fun (hd, tl) -> hd :: tl)

let mapM f ls kont =
  let rec loop acc f ls kont =
    match ls with
    | [] -> kont (List.rev acc)
    | h :: t ->
      let+ h = f h in
      loop (h :: acc) f t kont in
  loop [] f ls kont

type 'a type_map = 'a Types.TypeMap.t
let pp_type_map f fmt vl =
  Types.TypeMap.pp
    ~pp_start:Format.(fun fmt () -> pp_open_hovbox fmt 1; pp_print_string fmt "{")
    ~pp_stop:Format.(fun fmt () -> pp_print_string fmt "}"; pp_open_hovbox fmt 1)
    Lang.Type.pp f fmt vl

type expr = Lang.Expr.t
let pp_expr fmt vl = Lang.Expr.pp fmt vl

type ctx = {
  consts: expr list type_map;
  pats: Types.pat list type_map;
  funcs: (string * Lang.Type.t list) list type_map;
} [@@deriving show]

let ctx_pats ctx = ctx.pats
let ctx_consts_with_ty ctx ~ty =
  Types.TypeMap.find_opt ty ctx.consts
  |> Option.value  ~default:[]
let ctx_funcs_with_ty ctx ~ty =
  Types.TypeMap.find_opt ty ctx.funcs
  |> Option.value  ~default:[]
let ctx_pats_with_ty ctx ~ty =
  Types.TypeMap.find_opt ty ctx.pats
  |> Option.value  ~default:[]


let make_raw_ctx :
  consts: (Lang.Type.t * Lang.Expr.t list) list ->
  pats: (Lang.Type.t * Types.pat list) list ->
  funcs: (Lang.Type.t * (string * Lang.Type.t list) list) list ->
  ctx = fun ~consts ~pats ~funcs ->
  {
    consts = Types.TypeMap.of_list consts;
    pats = Types.TypeMap.of_list pats;
    funcs = Types.TypeMap.of_list funcs;
  }


let build_context ?(vars=[]) ?(ints=[0;1;2;3]) ?(funcs=[]) ~from_id ~to_id ~env proof_script =
  (* collect consts, functions and patterns from old proof script. *)
  let consts, old_funcs = Collector.collect_consts_and_funcs ~from_id ~to_id ~env proof_script in
  let pats = Collector.collect_pats ~from_id ~to_id ~env proof_script in
  (*  update consts with variables *)
  let consts =
    List.fold_left (fun acc (var, ty) ->
        Types.update_binding acc ty (`Var var)
      ) consts vars in
  let consts =
    List.fold_left (fun acc i ->
        Types.update_binding acc Int (`Int i)
      ) consts ints in
  let funcs =
    let normalize_name f = String.split_on_char '.' f |> List.last_opt |> Option.value ~default:f in
    List.fold_left (fun acc f ->
        match env f with
        | None -> acc
        | Some (args, ret_ty) -> Types.update_binding acc ret_ty (normalize_name f, args)
      ) old_funcs funcs in
  let funcs = Types.TypeMap.map (fun fns -> StringMap.of_list fns |> StringMap.to_list) funcs in

  {consts; pats; funcs}

(* [get_fuels ctx fname fuel args]: determines fuel for arguments of function fname.
* rationale for fuel distribution is as follows:
   - no fuel decrement for first arguments of functions where atleast one argument cannot be generated using a function (but might be a supplied constant)
   - else, decrement fuel by one
*)
let get_fuels ctx fuel fname arg_tys =
  let open Lang.Type in

  (* empty arg types do not have a function that generates values of that type *)
  let has_empty_arg = List.exists (fun arg ->
      Types.TypeMap.find_opt arg ctx.funcs
      |> Option.value ~default:[]
      |> List.is_empty
    ) arg_tys
  in

  let get_fuel i arg =
    match arg with
    | _ when i = 0 && has_empty_arg -> arg, fuel
    | _ -> arg, fuel
  in

  List.mapi get_fuel arg_tys

let rec generate_expression ?(fuel=3) (ctx: ctx) (env: Types.env)  (ty: Lang.Type.t) =
  match fuel with
  | fuel when fuel > 0 ->
    let consts = ctx_consts_with_ty ctx ~ty in
    let funcs = ctx_funcs_with_ty ctx ~ty in
    let consts =
      if fuel = 1
      then
        let consts_funcs =
          (Gen.of_list funcs)
          |> Gen.filter_map (function
            | (fname, [arg]) -> Some (fname, arg)
            | (_, _)  -> None
          ) 
          |> Gen.flat_map (fun (fname, ty) ->
            ctx_consts_with_ty ctx ~ty
            |> Gen.of_list
            |> Gen.map (fun arg -> `App (fname, [arg]))
          ) in
        Gen.append (Gen.of_list consts) consts_funcs
      else Gen.of_list consts in
    let funcs =
      (Gen.of_list funcs)
      |> Gen.flat_map (fun (fname, args) ->
        let arg_with_fuels = get_fuels ctx fuel fname args in
        (Gen.of_list arg_with_fuels)
        |> gen_product_l (fun (arg, fuel) ->
          generate_expression ctx env ~fuel:fuel arg
        ) 
        |> Gen.map (fun args -> `App (fname, args))
      ) in
    Gen.append funcs consts
  | _ -> Gen.of_list []


let rec instantiate_pat ?(fuel=3)  ctx env (pat: Types.pat) : Lang.Expr.t Gen.t  =
  match pat with
  | `App (fname, args) ->
    Gen.of_list args
    |> gen_product_l (instantiate_pat ctx env  ~fuel:(fuel)) 
    |> Gen.map (fun args -> `App (fname, args))
  | `Constructor (name, args) ->
    Gen.of_list args
    |> gen_product_l (instantiate_pat ctx env ~fuel:(fuel)) 
    |>  Gen.map (fun args -> `Constructor (name, args))
  | `Int i as e -> Gen.of_list [e]
  | `Tuple ls ->
    (Gen.of_list ls)
    |> gen_product_l (instantiate_pat ctx env ~fuel:(fuel))
    |> Gen.filter_map (function [] -> None | xs -> Some (`Tuple xs))
  | `Var v as e -> Gen.of_list [e]
  | `PatVar (str, ty) ->
    generate_expression ctx env ~fuel:(fuel) ty

(* generates a list of candidate expressions of a desired type;
 * if initial = true then only use patterns as a template to generate candidate expressions *)
let generate_expression ?(initial=true) ?fuel ctx env ty =
  if initial then
    ctx_pats_with_ty ctx ~ty
    |> Gen.of_list
    |> Gen.flat_map (instantiate_pat ctx env ?fuel) 
  else
    generate_expression ?fuel ctx env ty
