type t = private int

val init : t

val incr : t -> t

val pp : Format.formatter -> t -> unit

val show : t -> string
