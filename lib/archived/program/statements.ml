type pattern =
  | Var of string
  | Tuple of pattern list
  | Constructor of string * pattern list
  | Wildcard

(* straight line code *)
and slc = [
  | `ArrayAssign of string * Expr.expr * Expr.expr
  | `Expr of Expr.expr
] [@@deriving eq, show]

type t = [
  | `LetPure of string * Expr.expr
  | `AllocArray of string * Expr.expr * string
  | `Length of string * Expr.expr
  | `Fold of pattern * pattern * string * slc list * Expr.expr * Expr.expr
  | `Iteri of string * string * slc list * Expr.expr
  | `ListFold of pattern * pattern * string * slc list * Expr.expr * Expr.expr
  | `MatchPure of string * (pattern * t list) list
  | `MatchDeferred of string * (pattern * t list) list
  | `Comment of string
  | `EmpArray
  | slc
]
[@@deriving eq, show]

type func = string * pattern list * t list
[@@deriving eq, show]
