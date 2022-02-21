type pattern =
  | Var of string
  | Tuple of pattern list
  | Constructor of string * pattern list
  | Wildcard

(* straight line code *)
and slc = [
  | `Let of pattern * Expr.expr
  | `ArrayAssign of string * Expr.expr * Expr.expr
  | `Expr of Expr.expr
]

type t = [
  | `Fold of pattern * pattern * pattern * slc list * Expr.expr * Expr.expr
  | `Iteri of string * string * slc * Expr.expr
  | `ListFold of pattern * pattern * pattern * slc list * Expr.expr * Expr.expr
  | `Match of Expr.expr * (pattern * t list) list
  | slc
]

