open Containers
module IntSet = Set.Make(Int)
module IntMap = Map.Make(Int)
module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

type def_map = [ `Lambda of Lang.Expr.typed_param list * Lang.Expr.t Lang.Program.stmt ] StringMap.t
type expr = Lang.Expr.t
type holy_expr = expr -> expr
type ty = Lang.Type.t
type 'a map = 'a StringMap.t

let pp_expr = Lang.Expr.pp
let pp_ty = Lang.Type.pp

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
  env: (string * ty) list;
  assumptions: (ty * expr * expr) list; (* assumptions *)
  initial: initial_vc;
  conditions: vc list;
} [@@deriving show]
