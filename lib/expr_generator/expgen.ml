open Containers

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

module TypeMap = Map.Make (struct
    type t = Lang.Type.t [@@deriving eq, ord]
  end )

type func_type = (Lang.Type.t list) * Lang.Type.t [@@deriving show]
type env_type =
  | FuncType of func_type
  | VarType of Lang.Type.t

type env = string -> func_type

type ctx = {
  consts: Lang.Expr.t list TypeMap.t;
  pats: pat list TypeMap.t;
  funcs: (string * Lang.Type.t list) list TypeMap.t;
}

let (let+) x f = List.(>>=) x f

let get_fuels ctx fname fuel args =
  let open Lang.Type in
  let has_no_func arg =
    match TypeMap.find_opt arg ctx.funcs with
    | Some (_ :: _) -> false
    | _ ->
      print_endline @@ fname ^ " " ^ "Found";
      true
  in

  let has_missing_func = List.exists has_no_func args in

  let get_fuel i arg =
    let curr_fuel =
    if i = 0 && has_missing_func
    then fuel
    else fuel - 1
    in

    match arg with
    | List (Var "A") ->  arg, curr_fuel - 1
    | _ -> arg, curr_fuel
  in

  List.mapi get_fuel args

let rec gen_exp (ctx: ctx) (env: env) ~max_fuel ~fuel (ty: Lang.Type.t): Lang.Expr.t list =
  if fuel > 0
  then
    begin
      if fuel = max_fuel
      then
        let pats = List.rev @@ (TypeMap.find_opt ty ctx.pats |> Option.value ~default:[]) in
        let pats = List.flat_map (instantiate_pat ctx env ~max_fuel ~fuel:(fuel)) pats in
        pats
      else
        begin
          let consts = TypeMap.find_opt ty ctx.consts |> Option.value  ~default:[] in

          let funcs = TypeMap.find_opt ty ctx.funcs |> Option.value ~default:[] in
          let funcs =  List.flat_map (fun (fname, args) ->
              let arg_with_fuels = get_fuels ctx fname fuel args in
              let+ args = List_utils.mapM (fun (arg, fuel) -> gen_exp ctx env ~max_fuel ~fuel:fuel arg) arg_with_fuels in
              List.return (`App (fname, args))
            ) funcs in
          funcs @ consts
        end
    end
  else
    []

and instantiate_pat ctx env ~max_fuel ~fuel pat : Lang.Expr.t list  =
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
    gen_exp ctx env ~max_fuel ~fuel:(fuel - 1) ty
  |  _ -> []
