
type t =
  | Unit
  | Var of string
  | Int
  | Func
  | Loc
  | List of t
  | Array of t
  | Ref of t
  | Product of t list
  | ADT of string * t list * string option
[@@deriving eq, ord]

type fn =
  | Forall of string list * t list
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
  | Ref t -> align @@  group (print t ^^ blank 1 ^^ string "ref")
  | Array t -> align @@  group (print t ^^ blank 1 ^^ string "array")
  | List t -> group (print t ^^ blank 1 ^^ string "list")
  | ADT (name, args, _) -> group (group (parens (separate_map comma print args)) ^/^ string name)
  | Product elts -> group (parens @@ (separate_map (string " * ")  print elts))

let print_fn (Forall (qf,tys)) =
  let open PP in
  (match qf with
   | [] -> Fun.id
   | _ -> fun v -> group @@ string "forall " ^^ separate_map (break 1) string qf ^^ string "," ^/^ v) @@
  group @@ separate_map (blank 1 ^^ string "->" ^^ break 1) print tys

let pp fmt vl = PP.ToFormatter.compact fmt (print vl)
let show vl =
  let buf = Buffer.create 10 in
  PP.ToBuffer.compact buf (print vl);
  Buffer.contents buf

let pp_fn fmt vl = PP.ToFormatter.compact fmt (print_fn vl)
let show_fn vl =
  let buf = Buffer.create 10 in
  PP.ToBuffer.compact buf (print_fn vl);
  Buffer.contents buf
