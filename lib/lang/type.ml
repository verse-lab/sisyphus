open Containers
module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

type t =
  | Unit
  (** [Unit] represents [(): unit] type.  *)
  | Var of string
  (** [Var v] represents a polymorphic variable [v]. Note: depending
      on whether we retrieved this type from OCaml or Coq, the
      representation of the type variable itself may differ in subtle
      ways. For example, OCaml type variable strings [v] include the
      prefixing apostrophe and are always lower case. Coq polymorphic
      variables have no prefix and are upper case. *)
  | Int
  (** [Int] represents the int [1: int] type. *)
  | Bool
  (** [Bool] represents the bool [true: bool] type.  *)
  | Func of (t list * t) option (* optionally include the internal parameters *)
  (** [Func f] represents a function type - if we know the actual type
      of the function, then we include it in [f], otherwise [f] is
      empty. This accounts for the case in which [Func] is used to
      represent the [func] type from CFML which doesn't track the
      argument and return types of the function.  *)
  | Loc
  (** [Loc] represents CFML's [Loc] type  *)
  | List of t
  (** [List ty] represents a List type over elements of type [ty].  *)
  | Array of t
  (** [Array ty] represents an Array type over elements of type [ty].
  *)
  | Ref of t
  (** [Ref ty] represents a Ref type over elements of type [ty].  *)
  | Product of t list
  (** [Product tys] represents a product of [tys] types.  *)
  | ADT of string * t list * (string * string) option
  (** [ADT (name, tys, converters)] represents an arbitrary ADT named
      [name] instantiated with types [tys], and optionally providing
      converters [conv]. *)
  | Val
  (** [Val] represents CFML's opaque Val type.  *)
[@@deriving show, eq, ord]

let pp_raw = pp
let show_raw = show

type fn =
  | Forall of string list * t list
[@@deriving show, eq, ord]

let pp_raw_fn = pp_fn
let show_raw_fn = show_fn


module PP = PPrint

let rec print =
  let open PP in
  function
  | Val -> string "val"
  | Unit -> string "unit"
  | Var v -> string v
  | Int -> string "int"
  | Bool -> string "bool"
  | Func None -> string "func"
  | Func (Some (args,res)) ->
    group (string "func" ^^ group (parens (separate_map (blank 1 ^^ string "->" ^^ break 1) print args ^/^ string "->" ^/^ print res)))
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

let rec exists p ty =
  match ty with
  | Loc | Val
  | Unit | Var _ |Int |Bool  -> p ty
  | List ity
  | Array ity
  | Ref ity -> p ty || p ity
  | Product tys -> p ty || List.exists (exists p) tys
  | Func None -> p ty
  | Func (Some (args, res)) -> p ty || List.exists (exists p) args || exists p res
  | ADT (_, tys, _) -> p ty || List.exists (exists p) tys

let rec poly_vars vars = function
  | Var v -> StringSet.add v vars
  | Unit | Int | Bool | Loc | Val -> vars
  | List ty | Array ty | Ref ty ->  poly_vars vars ty
  | Func (Some (args, res)) ->
    let vars = poly_vars vars res in
    List.fold_left
      (fun vars ty ->
         poly_vars vars ty)
      vars args
  | Func None -> vars

  | ADT (_, tys, _)
  | Product tys ->
    List.fold_left
      (fun vars ty ->
         poly_vars vars ty) vars tys

let rec map_poly_var f = function
  | Var name -> Var (f name)
  | Unit | Int | Bool | Loc | Val as ty -> ty
  | List ty -> List (map_poly_var f ty)
  | Array ty -> Array (map_poly_var f ty)
  | Ref ty -> Ref (map_poly_var f ty)
  | Func (Some (args, res)) ->
    let res = map_poly_var f res in
    let args = List.map (map_poly_var f) args in
    Func (Some (args, res))
  | Func None -> Func None
  | ADT (name, tys, conv) ->
    let tys = List.map (map_poly_var f) tys in
    ADT (name, tys, conv)
  | Product tys ->
    let tys = List.map (map_poly_var f) tys in
    Product tys

let rec fold (f: 'a -> _ -> 'a) (acc: 'a) : t -> 'a = fun ty ->
  let acc = f acc ty in
  match ty with 
  | Unit
  | Var _
  | Int
  | Bool
  | Loc
  | Val
  | Func None -> acc
  | Func Some (args, ret) ->
    List.fold_left (fold f) acc
      (ret :: args)
  | Ref ty
  | Array ty
  | List ty -> fold f acc ty
  | Product tys
  | ADT (_, tys, _) ->
    List.fold_left (fold f) acc
      tys

(** [to_coq_form ty] converts a type [ty] into a form that will be
    accepted by Coq (i.e updates any polymorphic variables) to have the
    correct representation.  *)
let to_coq_form ty =
  map_poly_var (fun s ->
    if String.prefix ~pre:"'" s
    then String.uppercase_ascii (String.drop 1 s)
    else s
  ) ty

(** [to_ocaml_form ty] converts a type [ty] into a form that will be
    accepted by OCaml (i.e updates any polymorphic variables) to have the
    correct representation.  *)
let to_ocaml_form ty =
  map_poly_var (fun s ->
    if String.prefix ~pre:"'" s
    then s
    else "'" ^ (String.lowercase_ascii s)
  ) ty
