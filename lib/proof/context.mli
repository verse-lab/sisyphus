module type CONFIG = sig

  val libs : Coqlib.t list

  val verbose : bool

end

module Make : functor (C : CONFIG) -> sig

  type state

  val initial_state : state

  val fresh_doc : unit -> unit

  val add : ?state:state -> string -> state list

  val cancel: state list -> state list

  val parse : ?state:state -> string -> Vernacexpr.vernac_control option

  val query : state -> Serapi.Serapi_protocol.query_cmd -> Serapi.Serapi_protocol.coq_object list option

  val exec : state -> unit

end
