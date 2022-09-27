val run: string -> unit

val program : Lang.Expr.t Lang.Program.t Alcotest.testable

module Make : functor (S : sig val name : string end) -> sig
    val add_test : string -> (unit -> unit) -> unit
    val add_slow_test : string -> (unit -> unit) -> unit
    val run : unit -> unit
end
