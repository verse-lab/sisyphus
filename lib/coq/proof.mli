module type CONFIG = sig
  (** This module type encodes the parameters needed to instantiate the Coq proof assistant. *)

  val libs : Coqlib.t list
  (** [libs] is the list of coq libraries used by the proof script *)

  val verbose : bool
  (** [verbose] is whether the proof assistant should print out debugging information. *)

end

module type PROOF = sig
  (** This module represents an instantiation of the Coq proof
     assistant. *)

  val size : unit -> int
  (** [size ()] returns the size of a proof *)

  val reset : unit -> unit
  (** [reset ()] resets the proof to a fresh state *)

  val add : string -> unit
  (** [add txt] extends the proof script with [txt]

      Note: this does not evaluate the extended proof script, you must
     call [exec] *)

  val cancel : count:int -> unit
  (** [cancel ~count] undoes the last [count] statements of the proof script. *)

  val cancel_last : unit -> unit
  (** [cancel_last ()] undoes the last statement of the proof script. *)

  val parse : ?at:int -> string -> Vernacexpr.vernac_control option
  (** [parse txt] parses [txt] in the context of the current proof script. *)

  val query : ?at:int ->
    Serapi.Serapi_protocol.query_cmd ->
    Serapi.Serapi_protocol.coq_object list option
  (** [query ?at cmd] executes a query [cmd] on the proof script
     state. If provided, evaluated at [at] commands prev *)

  val exec : unit -> unit
  (** [exec ()] executes the proof script.  *)

  val debug_current_goal: unit -> string
  (** [debug_current_goal ()] returns a string representing the current proof script state. *)

end

module Make(C: CONFIG) : PROOF

val make: ?verbose:bool -> Coqlib.t list -> (module PROOF)
