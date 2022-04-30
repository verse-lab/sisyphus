
module type S = sig

  type t

  val create: unit -> t

  val update: t -> int -> t

  val to_string: t -> string

end


type t =
  | Epic
  | Bepic

let to_string = function
  | Epic -> "epic"
  | Bepic -> "bepic"

let trace : t ref = ref Epic
