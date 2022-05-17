open Containers
module StringMap = Map.Make(String)

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
    
type 'a condition = {
  quantified_over: (string * ty) list; (* list of variables being quantified over *)
  assumptions: (expr * expr) list;     (* list of assumed equalities *)
  goal: 'a;                             (* expression to be proved *)
} [@@deriving show]

type initial_vc = {
  assumptions: (expr * expr) list; (* assumptions *)
  expr_values: expr array; (* values for variables *)
  param_values: expr map;  (* initial values for invariant parameters *)
} [@@deriving show]

type vc = {
  qf: (string * ty) list;

  param_values: expr map;
  assumptions: (expr * expr) list;

  post_param_values: expr map;
  expr_values: holy_expr array;
} [@@deriving show]

type verification_condition = {
  initial: initial_vc;
  conditions: vc list;
} [@@deriving show]
