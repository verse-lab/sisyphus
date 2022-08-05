open Containers

module TypeMap = Map.Make (Lang.Type)

type pat =
  [ `App of string * pat list
  | `Constructor of string * pat list
  | `Int of int
  | `Tuple of pat list
  | `Var of string
  | `PatVar of string * Lang.Type.t
  ]
[@@deriving eq, ord, show]

type env = (string -> ((Lang.Type.t list) * Lang.Type.t) option)

let update_binding env ty vl =
  TypeMap.update ty
    Fun.(Option.some % Option.map_or ~default:[vl] (List.cons vl))
    env
