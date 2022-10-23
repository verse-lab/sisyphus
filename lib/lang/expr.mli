open Containers
module StringMap : module type of Map.Make(String)
module StringSet : module type of Set.Make(String)

type program_id = int

type 'a simple_shape = 'a constraint 'a =
    [> `App of string * 'a simple_shape list
    | `Constructor of string * 'a simple_shape list
    | `Int of int
    | `Tuple of 'a simple_shape list
    | `Var of string ]
[@@deriving show, eq]

val pp_raw_simple_shape: (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a simple_shape -> unit
val show_raw_simple_shape: (Format.formatter -> 'a -> unit) -> 'a simple_shape -> string

type param = [ `Tuple of string list | `Var of string ]
[@@deriving show, eq, ord]

val pp_raw_param: Format.formatter -> param -> unit
val show_raw_param: param -> string

type typed_param = [`Var of (string * Type.t) | `Tuple of (string * Type.t) list]
[@@deriving show, eq, ord]

val pp_raw_typed_param:  Format.formatter -> typed_param -> unit
val show_raw_typed_param: typed_param -> string

type 'a lambda_shape = [`Lambda of typed_param list * 'a]
[@@deriving show, eq, ord]

val pp_raw_lambda_shape: (Format.formatter -> 'a -> unit) -> Format.formatter ->  'a lambda_shape -> unit
val show_raw_lambda_shape: (Format.formatter -> 'a -> unit) -> 'a lambda_shape -> string

type 'a shape = 'a constraint 'a =
    [> `App of string * 'a shape list
    | `Constructor of string * 'a shape list
    | `Int of int
    | `Lambda of typed_param list * 'a shape
    | `Tuple of 'a shape list
    | `Var of string ]
[@@deriving show, eq]

val pp_raw_shape: (Format.formatter -> 'a -> unit) -> Format.formatter ->  'a shape -> unit
val show_raw_shape: (Format.formatter -> 'a -> unit) -> 'a shape -> string

type simple_t =
  [ `App of string * simple_t list
  | `Constructor of string * simple_t list
  | `Int of int
  | `Tuple of simple_t list
  | `Var of string ]
[@@deriving eq, ord]

val pp_raw_simple_t: Format.formatter -> simple_t -> unit
val show_raw_simple_t:  simple_t -> string

type t =
  [ `App of string * t list
  | `Constructor of string * t list
  | `Int of int
  | `Lambda of typed_param list * t
  | `Tuple of t list
  | `Var of string ]
[@@deriving eq, ord]

val pp_raw:  Format.formatter -> t -> unit
val show_raw: t -> string

val print_param : param -> PPrint.document
val print_typed_param : typed_param -> PPrint.document

val print_simple : 'a simple_shape -> PPrint.document
val pp_simple : Format.formatter -> 'a simple_shape -> unit
val show_simple :  'a simple_shape -> string

val subst_simple : (string -> 'a simple_shape option) -> 'a simple_shape -> 'a simple_shape
val subst_simple_var : (string -> string option) -> 'a simple_shape -> 'a simple_shape
val simple_vars : ?with_funs:bool -> StringSet.t -> 'a simple_shape -> StringSet.t

val print : 'a shape -> PPrint.document
val pp : Format.formatter -> 'a shape -> unit
val show :  'a shape -> string


val subst : (string -> 'a shape option) -> 'a shape -> 'a shape
val subst_var : (string -> string option) -> 'a shape -> 'a shape
val vars : ?with_funs:bool -> StringSet.t -> 'a shape -> StringSet.t

val upcast : simple_t -> t
val downcast : t -> simple_t
val functions: StringSet.t -> t -> StringSet.t
val subst_functions: (string -> string option) -> t -> t

val fold: ('a -> t -> 'a) -> 'a -> t -> 'a
