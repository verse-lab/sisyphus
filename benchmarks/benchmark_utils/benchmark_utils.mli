val sisyphus_runs_on: path:string -> coq_name:string -> common_path: string -> common_coq_name:string -> unit -> unit

val run : string -> unit

(* [h] is a collection of named tests with (path, coq_name, common_path, common_coq_lib_name)
TODO: refactor tuple to struct instead
*)
val h : (string, (string * string * string * string)) Hashtbl.t

module Make : functor (S : sig val name : string end) -> sig
    val add_test : string -> (unit -> unit) -> unit
    val add_slow_test : string -> (unit -> unit) -> unit
    val run : unit -> unit
end
