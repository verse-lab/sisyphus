type t =
  | SetFlag of string
  | ImportFrom of string * string list
  | Comment of string
[@@deriving show, eq]





