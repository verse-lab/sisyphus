open Utils

type sanitized_state = {
  id : int;
  env : Runtime.value stringmap;
  heap : Runtime.heaplet stringmap;
}
[@@deriving show, eq]

type scorer = sanitized_state -> sanitized_state -> float option

type t
(** Represents a matching between two program points. *)

val build :
  ?scorers:(sanitized_state -> sanitized_state -> float option) list ->
  Sisyphus_tracing.state list -> Sisyphus_tracing.state list -> t
(** [build ?scorers l r] given two traces [l] and [r] constructs a
   matching between program points. *)

val top_k : int -> [< `Left | `Right ] -> t -> (int * float) list intmap
(** [top_k k orientation t] given a matcher [t], calculates a mapping
   of program points of [orientation] to the top [k] similar program
   points in the other program. *)
