type value = [
  | `Int of int
  | `Bool of bool
  | `Value of string
  | `List of value list
  | `Tuple of value list
  | `Constructor of string * value list
  | `Opaque of string * value list
]  [@@deriving show]
(** Represents an encoding of OCaml runtime values from a concrete execution trace. *)

type heaplet = [
    `PointsTo of value
  | `Array of value list
]  [@@deriving show]
(** Represents a particular value on the heap observed during a concrete execution.  *)

type context = (string * value) list
(** A [context] is a list of program variables and their observed runtime values.  *)

type heap_context = (string * heaplet) list
(** A [heap_context] is a list of program variables and their corresponding values on the heap. *)

type t
(** Represents an abstract encoding of a collection of observations of
   concrete values of program variables during an execution. *)

val build: Parsetree.expression list -> Sisyphus_tracing.trace -> t
(** [build args trace] extracts a collection of observations of concrete
   values from an execution trace and the args that were used to create it. *)

val lookup : t -> int -> (context * heap_context) list
(** [lookup t point] retrieves the list of observed concrete values at
   a particular program point during an execution. *)

val args: t -> Parsetree.expression list
(** [args t] retrieves the list of arguments used to construct this
   given trace. *)
