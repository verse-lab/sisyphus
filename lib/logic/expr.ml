open Containers
module PP = PPrint
module StringMap = Map.Make (String)
module StringSet = Set.Make (String)

type 'a simple_shape = [>
  | `Var of string
  | `Int of int
  | `Tuple of 'a simple_shape list
  | `App of string * 'a simple_shape list
  | `Constructor of string * 'a simple_shape list
] as 'a
[@@deriving show, eq]

type param = [`Var of string | `Tuple of string list]
  [@@deriving show, eq, ord]

type 'a lambda_shape = [`Lambda of param list * 'a]
[@@deriving show, eq, ord]

type 'a shape = [> 'a lambda_shape ] as 'a constraint 'a = 'a simple_shape
[@@deriving show, eq]

type simple_t = [
    `Var of string
  | `Int of int
  | `Tuple of simple_t list
  | `App of string * simple_t list
  | `Constructor of string * simple_t list
] 
[@@deriving eq, ord]
type t = [
    `Var of string
  | `Int of int
  | `Tuple of t list
  | `App of string * t list
  | `Constructor of string * t list
  | `Lambda of param list * t
] [@@deriving eq, ord]

let print_param : param -> PP.document =
  let open PP in
  function
  | `Var v -> group (string v)
  | `Tuple args ->
    group (parens (flow_map (char ',' ^^ break 1) string args))

let print_simple_nonfix : 'a .
  (needs_parens:bool -> 'a simple_shape -> PP.document) ->
  (needs_parens:bool -> 'a simple_shape -> PP.document) ->
  needs_parens:bool -> 'a simple_shape -> PP.document =
  fun print_simple default ~needs_parens exp ->
  let open PP in
  match exp with
  | `Var v -> string v
  | `Int i -> string (Int.to_string i)
  | `Constructor (cons, []) -> string cons 
  | `Constructor ("::", [h;t]) ->
    let body () = group ((print_simple ~needs_parens:true h) ^/^ string "::" ^/^ (print_simple ~needs_parens:false t)) in
    if needs_parens then parens (body ()) else body ()
  | `Constructor (cons, t) ->
    let body () = group (string cons ^/^ parens (flow_map (string "," ^^ break 1) (print_simple ~needs_parens:false) t)) in
    if needs_parens then parens (body ()) else body ()
  | `Tuple t ->
    group (parens (separate_map (string "," ^^ space) (print_simple ~needs_parens:false) t))
  | `App (("(+)" | "(-)") as op,[l;r]) ->
    let body () = group ((print_simple ~needs_parens:false l) ^/^ string (String.sub op 1 1) ^/^ (print_simple ~needs_parens:true r)) in
    if needs_parens then parens (body ()) else body ()
  | `App (f,args) ->
    let body () = group (string f ^/^ (flow_map (break 1) (print_simple ~needs_parens:true) args)) in
    if needs_parens then parens (body ()) else body ()
  | e -> default ~needs_parens e

let rec print_simple ~needs_parens exp = print_simple_nonfix ~needs_parens print_simple (fun ~needs_parens:_ _ -> PP.string "(??)") exp
let print_simple' = print_simple
let print_simple exp = print_simple ~needs_parens:false exp
let pp_simple fmt vl = PP.ToFormatter.pretty 0.9 80 fmt (print_simple vl)
let show_simple vl = Format.to_string pp_simple vl


let subst_simple_nonfix : 'a .
  ((string -> 'a simple_shape option) -> 'a simple_shape -> 'a simple_shape) -> ((string -> 'a simple_shape option) -> 'a simple_shape -> 'a simple_shape) ->
  (string -> 'a simple_shape option) -> 'a simple_shape -> 'a simple_shape =
  fun subst_simple default map exp ->
  match exp with
  | `Var v ->  map v |> Option.value ~default:(`Var v)
  | `Int i -> `Int i
  | `Constructor (cons, t) -> `Constructor (cons, List.map (subst_simple map) t)
  | `Tuple t -> `Tuple (List.map (subst_simple map) t)
  | `App (f,args) ->
    let f = match map f with None -> f | Some (`Var v) -> v [@@warning "-8"] in
    `App (f, List.map (subst_simple map) args)
  | e -> default map e
let rec subst_simple map exp = subst_simple_nonfix subst_simple (fun _ exp -> exp) map exp

let subst_simple_var_nonfix : 'a .
  ((string -> string option) -> 'a simple_shape -> 'a simple_shape) ->
  ((string -> string option) -> 'a simple_shape -> 'a simple_shape) ->
  (string -> string option) ->
  'a simple_shape -> 'a simple_shape =
  fun subst_simple_var default map  exp -> match exp with
  | `Var v ->  map v
               |> Option.map (fun v -> `Var v)
               |> Option.value ~default:(`Var v)
  | `Int i -> `Int i
  | `Constructor (cons, t) -> `Constructor (cons, List.map (subst_simple_var map) t)
  | `Tuple t -> `Tuple (List.map (subst_simple_var map) t)
  | `App (f,args) ->
    let f = match map f with None -> f | Some v -> v in
    `App (f, List.map (subst_simple_var map) args)
  | e -> default map e
let rec subst_simple_var map exp = subst_simple_var_nonfix subst_simple_var (fun _ exp -> exp) map exp

let simple_vars_nonfix : 'a .
  (?with_funs:bool -> StringSet.t -> 'a simple_shape -> StringSet.t) ->
  (?with_funs:bool -> StringSet.t -> 'a simple_shape -> StringSet.t) ->
  ?with_funs:bool -> StringSet.t -> 'a simple_shape -> StringSet.t =
  fun vars default ?(with_funs=false) map -> function
  | `Var v -> StringSet.add v map
  | `Int _ -> map
  | `Constructor (_, t)
  | `Tuple t -> List.fold_left (vars ~with_funs) map t
  | `App (f, args) ->
    let map = if with_funs then StringSet.add f map else map in
    List.fold_left (vars ~with_funs) map args
  | e -> default ~with_funs map e
let rec simple_vars ?with_funs map exp =
  simple_vars_nonfix simple_vars (fun ?with_funs:_ map _ -> map) ?with_funs map exp

let remove_binding fn v =
  (fun v' -> if String.equal v v' then None else fn v)

let rec print ~needs_parens exp =
  print_simple_nonfix print_simple' ~needs_parens PP.(fun ~needs_parens:_ -> function
    | `Lambda (params, body) -> group @@
      parens (string "fun" ^/^ flow_map space print_param params ^/^ string "->" ^/^
      nest 2 (print ~needs_parens:false body) )
    | _ -> PP.string "(??)"
  ) exp
let print exp = print ~needs_parens:false exp
let pp fmt vl = PP.ToFormatter.pretty 0.9 80 fmt (print vl)
let show vl = Format.to_string pp vl

let rec subst :
  'a . (string -> 'a shape option) -> 'a shape -> 'a shape =
  fun map exp ->
  subst_simple_nonfix subst (fun map -> function
    | `Lambda (params, body) ->
      let map = List.fold_left (fun fn ->
        function
        | `Var v -> remove_binding fn v
        | `Tuple elts -> List.fold_left remove_binding fn elts
      ) map params in
      `Lambda (params, subst map body)
    | e -> e
  ) map exp

let rec subst_var :
  'a . (string -> string option) -> 'a shape -> 'a shape =
  fun map exp ->
  subst_simple_var_nonfix subst_var (fun map -> function
    | `Lambda (params, body) ->
      let map = List.fold_left (fun fn ->
        function
        | `Var v -> remove_binding fn v
        | `Tuple elts -> List.fold_left remove_binding fn elts
      ) map params in
      `Lambda (params, subst_var map body)
    | e -> e
  ) map exp

let rec vars :
  'a . ?with_funs:bool -> StringSet.t -> 'a shape -> StringSet.t =
  fun ?(with_funs=false) map exp ->
  simple_vars_nonfix vars (fun ?with_funs map -> function
    | `Lambda (params, body) ->
      let map = List.fold_left (fun map ->
        function
        | `Var v -> StringSet.remove v map
        | `Tuple elts -> List.fold_left (Fun.flip StringSet.remove) map elts
      ) map params in
      vars ?with_funs map body
    | _ -> map
  ) ~with_funs map exp

let rec upcast : simple_t -> t = function
  | `Var v -> `Var v
  | `Int i -> `Int i
  | `Tuple t -> `Tuple (List.map upcast t)
  | `App (f, args) -> `App (f, List.map upcast args)
  | `Constructor (f, args) -> `Constructor (f, List.map upcast args)

let rec downcast : t -> simple_t = function
  | `Var v -> `Var v
  | `Int i -> `Int i
  | `Tuple t -> `Tuple (List.map downcast t)
  | `App (f, args) -> `App (f, List.map downcast args)
  | `Constructor (f, args) -> `Constructor (f, List.map downcast args)
  | `Lambda _ -> failwith "invalid arg"
