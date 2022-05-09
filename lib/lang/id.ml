open Containers
type t = int

let init = 0

let incr i = i + 1

let pp fmt vl = Format.fprintf fmt "ID(%d)" vl
let show vl = Format.to_string pp vl
