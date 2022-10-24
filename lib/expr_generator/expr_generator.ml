open Containers

module Log = (val Logs.src_log (Logs.Src.create ~doc:"An Expression Generator" "expr-gen"))

module Types = Types

type env = string -> ((Lang.Type.t list) * Lang.Type.t) list

module StringMap = Map.Make(String)
module StringSet = Set.Make (String)

let filter_blacklisted blacklisted_vars ls =
  Seq.filter (function
    | `Var v when (StringSet.mem v blacklisted_vars) -> false
    | _ -> true) ls

type 'a type_map = 'a Types.TypeMap.t
let pp_type_map f fmt vl =
  Types.TypeMap.pp
    ~pp_start:Format.(fun fmt () -> pp_open_hovbox fmt 1; pp_print_string fmt "[")
    ~pp_sep:Format.(fun fmt () -> pp_print_string fmt "; ")
    ~pp_arrow:Format.(fun fmt () -> pp_print_string fmt ", ")
    ~pp_stop:Format.(fun fmt () -> pp_print_string fmt "]"; pp_open_hovbox fmt 1)
    Lang.Type.pp_raw f fmt vl

type expr = Lang.Expr.t
let pp_expr fmt vl = Lang.Expr.pp_raw fmt vl

type ty = Lang.Type.t
let pp_ty fmt vl = Lang.Type.pp_raw fmt vl

type ctx = {
  consts: expr list type_map;
  pats: Types.pat list type_map;
  funcs: (string * ty list) list type_map;
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

let build_context ?(constants=[]) ?(vars=[]) ?(ints=[0;1;2;3]) ?(funcs=[]) ~from_id ~to_id ~env proof_script =
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
  let consts =
    List.fold_left (fun consts (expr, ty) ->
      Types.update_binding consts ty expr
    ) consts constants in
  let consts =
    Types.TypeMap.map (fun elts ->
      let module S = Set.Make (struct
                       type t = Lang.Expr.t
                       [@@deriving ord]
                     end) in
      S.of_list elts |> S.to_list) consts in
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

(* [get_fuels ctx fname fuel args]: determines fuel for arguments of
   function fname.

 * rationale for fuel distribution is as follows:

   - no fuel decrement for first arguments of functions where atleast
     one argument cannot be generated using a function (but might be a
     supplied constant)

   - else, decrement fuel by one *)
let get_fuels ctx fuel fname arg_tys =
  let open Lang.Type in

  (* empty arg types do not have a function that generates values of that type *)
  let has_empty_arg = List.exists (fun arg ->
    Types.TypeMap.find_opt arg ctx.funcs
    |> Option.value ~default:[]
    |> List.is_empty
  ) arg_tys
  in

  let is_func = function
    | Func _ -> true
    | _ -> false
  in

  (* if any argument doesnt need more fuel, then distribute more fuel to first non-function argument *)
  let priority_arg =
    List.find_mapi (fun i arg ->
      if has_empty_arg && not (is_func arg)
      then Some i
      else None
    ) arg_tys
    |> Option.get_or ~default:(-1)
  in

  let get_fuel i arg =
    match arg with
    | _ when i = priority_arg -> arg, fuel
    | _ -> arg, fuel - 1
  in

  List.mapi get_fuel arg_tys

let rec generate_expression ?(fuel=3) ~blacklisted_vars (ctx: ctx)  (ty: Lang.Type.t) () =
  (* Format.printf "Fuel = %s, Ty = %a@." (string_of_int fuel) Lang.Type.pp ty; *)
  match fuel with
  | fuel when fuel > 0 ->
    let consts = Types.TypeMap.find_opt ty ctx.consts
                 |> Option.value  ~default:[]
                 |> List.to_seq
                 |> filter_blacklisted blacklisted_vars in
    let consts = match ty with
      | Lang.Type.List _ -> Seq.cons (`Constructor ("[]", [])) consts
      | Lang.Type.Unit -> Seq.cons (`Constructor ("()", [])) consts
      | Lang.Type.ADT ("option", _, _) -> Seq.cons (`Constructor ("None", [])) consts
      | _ -> consts in
    let funcs = Types.TypeMap.find_opt ty ctx.funcs
                |> Option.value ~default:[]
                |> List.to_seq in
    let consts_funcs =
      if fuel = 1 then
        Seq.filter_map (function
          | (fname, [arg]) -> Some (fname, arg)
          | (_, _)  -> None
        ) funcs
        |> Seq.flat_map (fun (fname, arg) ->
          Types.TypeMap.find_opt arg ctx.consts
          |> Option.value  ~default:[]
          |> List.to_seq
          |> filter_blacklisted blacklisted_vars
          |> Seq.map (fun arg -> `App (fname, [arg]))
        )
      else Seq.nil in

    let consts = Seq.append consts consts_funcs in
    let funcs =  Seq.flat_map (fun (fname, args) ->
      let arg_with_fuels = get_fuels ctx fuel fname args |> List.to_seq in
      let funcs =
        Utils.seq_map_product_l (fun (arg, fuel) ->
          generate_expression ~blacklisted_vars ctx ~fuel:fuel arg
        ) arg_with_fuels in
      let funcs = Seq.map (fun args -> `App (fname, args)) funcs in
      funcs
    ) funcs in

    (* add negation of bools for free *)
    let res =
      let res = Seq.append funcs consts in
      let is_bool = function Lang.Type.Bool -> true | _ -> false in
      let negs =
        if is_bool ty then
          Seq.map (fun e -> `App ("not", [e])) res
        else Seq.nil in
      Seq.append res negs in
    res ()
  | _ -> Seq.Nil


let rec instantiate_pat ?(fuel=3) ~blacklisted_vars ctx pat () =
  match pat with
  | `App (fname, args) ->
    let args = Utils.seq_map_product_l (instantiate_pat ~blacklisted_vars ctx  ~fuel:(fuel)) (Seq.of_list args) in
    Seq.map (fun args -> `App (fname, args)) args ()
  | `Constructor (name, args) ->
    let args = Utils.seq_map_product_l (instantiate_pat ~blacklisted_vars ctx ~fuel:(fuel)) (Seq.of_list args) in
    Seq.map (fun args -> `Constructor (name, args)) args ()
  | `Int i as e -> Seq.singleton e ()
  | `Tuple ls ->
    let ls = Seq.map (instantiate_pat ~blacklisted_vars ctx ~fuel:(fuel)) (Seq.of_list ls) in
    let ls = Seq.map (Seq.to_list) ls in
    Seq.filter_map (function
      | [] -> None
      | ls -> Some (`Tuple ls)
    ) ls ()
  | `Var v as e ->
    if not (StringSet.mem v blacklisted_vars)
    then Seq.singleton e ()
    else Seq.Nil
  | `PatVar (str, ty) ->
    generate_expression  ~blacklisted_vars ctx ~fuel:(fuel) ty ()

(* generates a list of candidate expressions of a desired type;
 * if initial = true then only use patterns as a template to generate candidate expressions *)
let generate_expression ?(blacklisted_vars=[]) ?(initial=true) ?fuel ctx ty =
  let blacklisted_vars = StringSet.of_list blacklisted_vars in
  let pats = List.rev @@ (Types.TypeMap.find_opt ty ctx.pats |> Option.value ~default:[]) in
  if initial && List.length pats > 0 then
    let pats = Seq.flat_map (instantiate_pat ~blacklisted_vars ctx ?fuel) (Seq.of_list pats) in
    pats
  else
    generate_expression ?fuel ~blacklisted_vars ctx ty
