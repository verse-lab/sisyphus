open Containers

module Log = (val Logs.src_log (Logs.Src.create ~doc:"An Expression Generator" "expr-gen"))

module Types = Types

type env = string -> ((Lang.Type.t list) * Lang.Type.t) list

module StringMap = Map.Make(String)
module StringSet = Set.Make (String)

let filter_blacklisted blacklisted_vars ls =
  List.filter (function
    | `Var v when (StringSet.mem v blacklisted_vars) -> false
    | _ -> true) ls

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

let (let+) x f = x f
let (|>>) x f kont = x (fun x -> f x kont)

let mapM f ls kont =
  let rec loop acc f ls kont =
    match ls with
    | [] -> kont (List.rev acc)
    | h :: t ->
      let+ h = f h in
      loop (h :: acc) f t kont in
  loop [] f ls kont

let rec fold_leftM f accu l kont =
  match l with
    [] -> kont accu
  | a::l ->
    let+ accu = f accu a in
    fold_leftM f accu l kont

let mapM_product_l f l kont =
  (* [left]: elements picked so far
     [right]: sets to pick elements from
     [acc]: accumulator for the result, to pass to continuation
     [k]: continuation *)
  let rec prod_rec left right k acc kont = match right with
    | [] -> kont (k acc (List.rev left))
    | l1 :: tail ->
      let+ l1 = f l1 in
      fold_leftM
        (fun acc x -> prod_rec (x::left) tail k acc)
        acc l1 kont
  in
  prod_rec [] l (fun acc l' -> (l' :: acc)) [] kont

let flat_mapM f l kont =
  let rec aux f l kont = match l with
    | [] -> kont []
    | x::l' ->
      let+ y = f x in
      let kont' tail = match y with
        | [] -> kont tail
        | [x] -> kont (x :: tail)
        | [x;y] -> kont (x::y::tail)
        | l -> kont (List.append l tail)
      in
      aux f l' kont'
  in
  aux f l kont


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
      List.fold_left (fun acc (args, ret_ty) ->
        Types.update_binding acc ret_ty (normalize_name f, args)
      ) acc (env f)
    ) old_funcs funcs in
  let funcs =
    let module StringTypeSet =
      Set.Make (struct
        type t = string * Lang.Type.t list
        [@@deriving ord]
      end) in
    Types.TypeMap.map (fun fns ->
      StringTypeSet.of_list fns
      |> StringTypeSet.to_list
    ) funcs in
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
    | _ -> arg, fuel - 1
  in

  List.mapi get_fuel arg_tys

let rec generate_expression ?(fuel=3) ~blacklisted_vars (ctx: ctx) (env: Types.env)  (ty: Lang.Type.t) k =
  match fuel with
  | fuel when fuel > 0 ->
    let consts = Types.TypeMap.find_opt ty ctx.consts |> Option.value  ~default:[]
                 |> filter_blacklisted blacklisted_vars in
    let consts = match ty with
      | Lang.Type.List _ -> `Constructor ("[]", []) :: consts
      | Lang.Type.Unit -> `Constructor ("()", []) :: consts
      | Lang.Type.Bool -> `Constructor ("true", []) :: `Constructor ("false", []) :: consts
      | _ -> consts in
    let funcs = Types.TypeMap.find_opt ty ctx.funcs |> Option.value ~default:[] in
    let consts_funcs =
      if fuel = 1 then
        List.filter_map (function
          | (fname, [arg]) -> Some (fname, arg)
          | (_, _)  -> None
        ) funcs
        |> List.flat_map (fun (fname, arg) ->
          Types.TypeMap.find_opt arg ctx.consts |> Option.value  ~default:[]
          |> filter_blacklisted blacklisted_vars
          |> List.map (fun arg -> `App (fname, [arg]))
        )
      else [] in
    let consts = consts @ consts_funcs in
    let+ funcs =  flat_mapM (fun (fname, args) kont ->
      let arg_with_fuels = get_fuels ctx fuel fname args in
      let+ funcs =
        mapM_product_l (fun (arg, fuel) ->
          generate_expression ~blacklisted_vars ctx env ~fuel:fuel arg
        ) arg_with_fuels in
      let+ funcs = mapM (fun args kont -> kont (`App (fname, args))) funcs in
      kont funcs
    ) funcs in
    k (funcs @ consts)
  | _ -> k []


let rec instantiate_pat ?(fuel=3) ~blacklisted_vars ctx (env: env) pat kont  =
  match pat with
  | `App (fname, args) ->
    let+ args = mapM_product_l (instantiate_pat ~blacklisted_vars ctx env  ~fuel:(fuel)) args in
    kont (List.map (fun args -> `App (fname, args)) args)
  | `Constructor (name, args) ->
    let+ args = mapM_product_l (instantiate_pat ~blacklisted_vars ctx env ~fuel:(fuel)) args in
    kont (List.map (fun args -> `Constructor (name, args)) args)
  | `Int i as e -> kont [e]
  | `Tuple ls ->
    let+ ls = mapM (instantiate_pat ~blacklisted_vars ctx env ~fuel:(fuel)) ls in
    if List.exists (fun xs -> List.length xs = 0) ls
    then kont []
    else kont (List.map (fun x -> `Tuple x) ls)
  | `Var v as e ->
    if not (StringSet.mem v blacklisted_vars)
    then kont [e]
    else kont []
  | `PatVar (str, ty) ->
    generate_expression  ~blacklisted_vars ctx env ~fuel:(fuel) ty kont

(* generates a list of candidate expressions of a desired type;
 * if initial = true then only use patterns as a template to generate candidate expressions *)
let generate_expression ?(blacklisted_vars=[]) ?(initial=true) ?fuel ctx (env: env) ty =
  let blacklisted_vars = StringSet.of_list blacklisted_vars in
  let pats = List.rev @@ (Types.TypeMap.find_opt ty ctx.pats |> Option.value ~default:[]) in
  if initial && List.length pats > 0 then
    let pats = flat_mapM (instantiate_pat ~blacklisted_vars ctx env ?fuel) pats Fun.id in
    pats
  else
    generate_expression ?fuel  ~blacklisted_vars ctx env ty Fun.id 
