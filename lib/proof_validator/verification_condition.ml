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
  | Lang.Type.ADT (name, args, Some constr) ->
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

(* let pp_expr = Lang.Expr.pp
 * let pp_ty = Lang.Type.pp *)

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
