
type t =
  | Unit
  | Var of string
  | Int
  | Func
  | Loc
  | List of t
  | Array of t
  | Ref of t
  | ADT of string * t list
  | Product of t list
[@@deriving eq, ord]

module PP = PPrint

let rec print =
  let open PP in
  function
  | Unit -> string "unit"
  | Var v -> string v
  | Int -> string "int"
  | Func -> string "func"
  | Loc -> string "loc"
  | Ref t -> group (print t ^/^ string "ref")
  | Array t -> group (print t ^/^ string "array")
  | List t -> group (print t ^/^ string "list")
  | ADT (name, args) -> group (group (parens (separate_map comma print args)) ^/^ string name)
  | Product elts -> group (parens @@ (separate_map (string " * ")  print elts))

let pp fmt vl = PP.ToFormatter.pretty 0.9 80 fmt (print vl)
let show = Containers.Format.to_string pp
             
