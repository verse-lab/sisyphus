open Containers

type env = string -> ((Lang.Type.t list) * Lang.Type.t) option

module StringMap = Map.Make(String)

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

let get_fuels ctx fname fuel args =
  let open Lang.Type in
  let has_no_func arg =
    match Types.TypeMap.find_opt arg ctx.funcs with
    | Some (_ :: _) -> false
    | _ -> true in

  let get_fuel i arg =
    let curr_fuel =
      if i = 0 && List.exists has_no_func args
      then fuel
      else fuel - 1 in
    match arg with
    | List (Var "A") ->  arg, curr_fuel - 1
    | _ -> arg, curr_fuel in

  List.mapi get_fuel args

let rec generate_expression ?(initial=false) ?(fuel=10) (ctx: ctx) (env: Types.env)  (ty: Lang.Type.t): Lang.Expr.t list =
  match fuel with
  | fuel when initial ->
    let pats = List.rev @@ (Types.TypeMap.find_opt ty ctx.pats |> Option.value ~default:[]) in
    let pats = List.flat_map (instantiate_pat ctx env ~fuel:(fuel)) pats in
    pats
  | fuel when fuel > 0 ->
    let consts = Types.TypeMap.find_opt ty ctx.consts |> Option.value  ~default:[] in
    let funcs = Types.TypeMap.find_opt ty ctx.funcs |> Option.value ~default:[] in
    let funcs =  List.flat_map (fun (fname, args) ->
      let arg_with_fuels = get_fuels ctx fname fuel args in
      List.map_product_l (fun (arg, fuel) ->
        generate_expression ctx env ~fuel:fuel arg
      ) arg_with_fuels
      |> List.map (fun args -> `App (fname, args))
    ) funcs in
    funcs @ consts
  | _ -> []

and instantiate_pat ?(max_fuel=10) ?(fuel=10)  ctx env pat : Lang.Expr.t list  =
  match pat with
  | `App (fname, args) ->
    List.map_product_l (instantiate_pat ctx env ~max_fuel ~fuel:(fuel)) args
    |> List.map (fun args -> `App (fname, args))
  | `Constructor (name, args) ->
    List.map_product_l (instantiate_pat ctx env ~max_fuel ~fuel:(fuel - 1)) args
    |>  List.map (fun args -> `Constructor (name, args))
  | `Int i as e -> [e]
  | `Tuple ls ->
    let ls = List.map (instantiate_pat ctx env ~max_fuel ~fuel:(fuel - 1)) ls in
    if List.exists (fun xs -> List.length xs = 0) ls
    then []
    else List.map (fun x -> `Tuple x) ls
  | `Var v as e -> [e]
  | `PatVar (str, ty) ->
    generate_expression ctx env ~fuel:(fuel - 1) ty


let generate_expression ?(initial=true) ?fuel ctx env ty = generate_expression ~initial ?fuel ctx env ty
