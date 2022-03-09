
type t =
  | Var of string
  | Int
  | Func
  | Loc
  | List of t
  | ADT of string * t list
  | Product of t list
