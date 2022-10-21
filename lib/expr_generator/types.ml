open Containers

module TypeMap = Map.Make (Lang.Type)

type ty = Lang.Type.t
let pp_ty = Lang.Type.pp_raw
let equal_ty = Lang.Type.equal
let compare_ty = Lang.Type.compare

type pat = [
    `App of string * pat list
  | `Constructor of string * pat list
  | `Int of int
  | `Tuple of pat list
  | `Var of string
  | `PatVar of string * ty ]
[@@deriving eq, ord, show]

type env = string -> ((Lang.Type.t list) * Lang.Type.t) list

let update_binding env ty vl =
  TypeMap.update ty
    (function
      | None -> Some [vl]
      | Some ls -> Some (vl :: ls)
    )
    env
