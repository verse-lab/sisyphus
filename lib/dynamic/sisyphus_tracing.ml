module Wrap: sig
  type t
  val wrap: 'a -> t
  val unwrap: t -> 'a
end = struct
  type t = Mk : 'a -> t

  let wrap v = Mk v

  let unwrap (Mk v) = Obj.magic v

end

module Symbol : sig
  type t

  val pp: Format.formatter -> t -> unit
  val show: t -> string

  val equal : t -> t -> bool

  val fresh : unit -> t

  val of_raw: int -> t
end = struct
  type t = Symbol of int


  let pp fmt (Symbol v) =  Format.fprintf fmt "symbol_%d" v

  let show v = Format.asprintf "%a" pp v

  let equal (Symbol l) (Symbol r) = l = r

  let fresh =
    let id = ref 0 in
    fun () -> incr id; Symbol !id

  let of_raw v = Symbol v

end

type value = [
  | `Int of int
  | `Bool of bool
  | `Value of Symbol.t
  | `List of value list
  | `Tuple of value list
  | `Constructor of string * value list
]

type heaplet = [
    `PointsTo of value
  | `Array of value list
]

type context = (string * value) list
type heap_context = (string * heaplet) list

type state = {
  position: int;
  env: context;
  heap: heap_context;
}

type trace = state list

include (struct

  let state = ref None

  let observe ~at ~env ~heap =
    match !state with
    | None -> failwith "attempted to observe in an invalid context"
    | Some trace ->
      state := Some ({position=at; env; heap} :: trace)

  let trace f =
    match !state with
    | Some _ -> failwith "nested traces not supported"
    | None ->
      state := Some [];
      f ();
      let trace = Option.get !state in
      state := None;
      trace

end : sig
           val observe: at:int -> env:context -> heap:heap_context -> unit
           val trace : (unit -> unit) -> trace
         end)
