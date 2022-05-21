open Containers
module StringMap = Map.Make(String)

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
  | Val
[@@deriving eq, ord]

type fn =
  | Forall of string list * t list
[@@deriving eq, ord]

module PP = PPrint

let rec print =
  let open PP in
  function
  | Val -> string "val"
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

let rec subst map = function
  | (Var name) as ty ->  StringMap.find_opt name map |> Option.value ~default:ty
  | Ref t -> Ref (subst map t)
  | Array t -> Array (subst map t)
  | List t -> List (subst map t)
  | Product elts -> Product (List.map (subst map) elts)
  | ADT (name, args, cons) -> ADT (name, List.map (subst map) args, cons)
  | ty -> ty
