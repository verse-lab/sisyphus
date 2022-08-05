open Containers
module IntSet = Set.Make(Int)
module IntMap = Map.Make(Int)
module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

type def_map = [ `Lambda of Lang.Expr.typed_param list * Lang.Expr.t Lang.Program.stmt ] StringMap.t
type ty = Lang.Type.t
let rec pp_ty fmt : Lang.Type.t -> unit = function
  | Lang.Type.Unit -> Format.pp_print_string fmt "Lang.Type.Unit"
  | Lang.Type.Var v -> Format.fprintf fmt "Lang.Type.Var \"%s\"" v
  | Lang.Type.Int -> Format.pp_print_string fmt "Lang.Type.Int"
  | Lang.Type.Func -> Format.pp_print_string fmt "Lang.Type.Func"
  | Lang.Type.Loc -> Format.pp_print_string fmt "Lang.Type.Loc"
  | Lang.Type.List t -> Format.fprintf fmt "Lang.Type.List (%a)" pp_ty t
  | Lang.Type.Array t -> Format.fprintf fmt "Lang.Type.Array (%a)" pp_ty t
  | Lang.Type.Ref t -> Format.fprintf fmt "Lang.Type.Ref (%a)" pp_ty t
  | Lang.Type.Product elts ->
    Format.fprintf fmt "Lang.Type.Product ([%a])"
      (List.pp ~pp_sep:(fun fmt () -> Format.fprintf fmt "; ") pp_ty) elts
  | Lang.Type.ADT (name, args, Some (constr, _)) ->
    Format.fprintf fmt "Lang.Type.ADT (\"%s\", [%a], Some \"%s\")" name
      (List.pp ~pp_sep:(fun fmt () -> Format.fprintf fmt "; ") pp_ty) args
      constr
  | Lang.Type.ADT (name, args, None) ->
    Format.fprintf fmt "Lang.Type.ADT (\"%s\", [%a], None)" name
      (List.pp ~pp_sep:(fun fmt () -> Format.fprintf fmt "; ") pp_ty) args
  | Lang.Type.Val -> Format.pp_print_string fmt "Lang.Type.Val"

type fn = Lang.Type.fn
let pp_fn fmt (Lang.Type.Forall (qf, tys)) =
  Format.fprintf fmt "Lang.Type.Forall ([%a], [%a])"
    (List.pp ~pp_sep:(fun fmt () -> Format.fprintf fmt "; ") String.pp) qf
    (List.pp ~pp_sep:(fun fmt () -> Format.fprintf fmt "; ") pp_ty) tys


type expr = [
    `Var of string
  | `Int of int
  | `Tuple of expr list
  | `App of string * expr list
  | `Constructor of string * expr list
  | `Lambda of [`Var of (string * ty) | `Tuple of (string * ty) list ] list * expr
] [@@deriving show]
type holy_expr = expr -> expr
type 'a map = 'a StringMap.t

let pp_holy_expr fmt v =
  pp_expr fmt (v (`Var "??"))

let pp_map f fmt vl =
  StringMap.pp
    ~pp_start:(fun fmt () -> Format.fprintf fmt "{")
    ~pp_stop:(fun fmt () -> Format.fprintf fmt "}")
    ~pp_arrow:(fun fmt () -> Format.fprintf fmt " -> ")
    ~pp_sep:(fun fmt () -> Format.fprintf fmt ",@ ")
    Format.pp_print_string
    f fmt vl


type property = string list * (string * ty) list *
                [`Assert of expr | `Eq of (ty * expr * expr)] list *
                [`Assert of expr | `Eq of (ty * expr * expr)]
[@@deriving show]

let property_functions s (_, _, assertions, prop) =
  match prop with
  | `Eq (_, l, r) ->
    List.fold_left (fun s -> function
      | `Assert b -> Lang.Expr.functions s b
      | `Eq (_, l, r) -> Lang.Expr.functions (Lang.Expr.functions s l) r
    ) s assertions
    |> Fun.flip Lang.Expr.functions l
    |> Fun.flip Lang.Expr.functions r  
  |`Assert b ->
    List.fold_left (fun s -> function
      | `Assert b -> Lang.Expr.functions s b
      | `Eq (_, l, r) -> Lang.Expr.functions (Lang.Expr.functions s l) r
    ) s assertions
    |> Fun.flip Lang.Expr.functions b

let property_only_uses_functions_in s prop =
  StringSet.subset (property_functions StringSet.empty prop) s

type initial_vc = {
  expr_values: expr array; (* values for variables *)
  param_values: expr list;  (* initial values for invariant parameters *)
} [@@deriving show]

type vc = {
  qf: (string * ty) list;

  param_values: expr list;
  assumptions: [`Eq of (ty * expr * expr) | `Assert of expr ] list;

  post_param_values: expr list;
  expr_values: holy_expr array;
} [@@deriving show]

type verification_condition = {
  poly_vars: string list;
  functions: (string * fn) list;
  properties: (string * property) list;
  env: (string * ty) list;
  assumptions: (ty * expr * expr) list; (* assumptions *)
  invariant: string * ty list;
  initial: initial_vc;
  conditions: vc list;
} [@@deriving show]


(** [normalize vc] returns a copy of vc where discrepancies between
   LibList and LibListZ functions have been ignored.  *)
let normalize (data: verification_condition) =
  let update s =
    if String.prefix ~pre:"TLC.LibListZ." s
    then Some ("TLC.LibList." ^ String.drop (String.length "TLC.LibListZ.") s)
    else None in
  let update_expr e = Lang.Expr.subst_functions update e in
  let update_assertion = function
      `Eq (ty, l, r) ->
      `Eq (ty, update_expr l, update_expr r)
    | `Assert prop -> `Assert (update_expr prop) in

  (* update functions *)
  let functions =
    let update_binding fns (name, sg) =
      let name = Option.value ~default:name @@ update name in
      let fns' = StringSet.add name fns in
      (fns', Option.return_if Equal.(not @@ physical fns fns') (name, sg)) in
    data.functions
    |> List.fold_map update_binding StringSet.empty
    |> snd
    |> List.filter_map Fun.id in

  (* update properties *)
  let properties =
    List.map (fun (pname, (qfs, params, assums, concl)) ->
      let assums = List.map update_assertion assums in
      (pname, (qfs, params, assums, update_assertion concl))) data.properties in

  (* update assumptions *)
  let assumptions =
    List.map (fun (ty, l, r) -> (ty, update_expr l, update_expr r)) data.assumptions in

  (* update initial verification condition *)
  let initial : initial_vc =  {
    expr_values=Array.map update_expr data.initial.expr_values;
    param_values=List.map update_expr data.initial.param_values;
  } in

  (* update post conditions *)
  let conditions = List.map (fun (vc: vc) ->
    {vc
     with param_values=List.map update_expr vc.param_values;
          assumptions=List.map update_assertion vc.assumptions;
          post_param_values=List.map update_expr vc.post_param_values;
          expr_values=Array.map (fun f -> fun e -> update_expr (f e)) vc.expr_values;
    }
  ) data.conditions in
  {data with
   functions;
   properties;
   assumptions;
   initial;
   conditions=conditions;
  }
