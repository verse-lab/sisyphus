val sisyphus_runs_on: path:string -> coq_name:string -> common_path: string -> common_coq_name:string -> unit -> unit

val run : string -> unit

module Make : functor (S : sig val name : string end) -> sig
    val add_test : string -> (unit -> unit) -> unit
    val add_slow_test : string -> (unit -> unit) -> unit
    val run : unit -> unit
end
