
val dispatch_goals_with_solver_tactic : unit -> bool
(** [dispatch_goals_with_solver_tactic] specifies whether the runtime
    system should check generated candidates using Sispyhus' solver
    tactic. Defaults to true.  *)

val max_goal_dispatch_attempts : unit -> int
(** [max_goal_dispatch_attempts ()] indicates the maximum number of
    attempts to dispatch subgoals from an invariant that Sisyphus will
    make. Defaults to 3. *)

val solver_tactic : unit -> string
(** [solver_tactic ()] returns the tactic that Sisyphus will attempt
    to use to dispatch generated subgoals. *)

val print_proof_extraction: unit -> bool
(** [print_proof_extraction ()] returns a boolean indicating whether
    Sisyphus should dump detailed information about reifying proof
    terms.

    Warning: Significantly increases run time. *)

val dump_generated_invariants: unit -> bool
(** [dump_generated_invariants ()] returns a boolean indicating whether
    Sisyphus should dump out all the invariants that it finds.

    Warning: Dumped invariant lists can be very large (~gbs in size). *)

val admit_all_sub_goals: unit -> bool
(** [admit_all_sub_goals ()] returns a boolean indicating whether
    Sisyphus should admit all sub-goals that it runs into. *)


val initialize :
  ?filter_logs:string ->
  ?print_proof_extraction:bool ->
  ?dump_generated_invariants:bool ->
  ?log_level:Logs.level ->
  ?log_dir:Fpath.t ->
  ?dump_dir:Fpath.t ->
  ?dispatch_goals_with_tactic:bool ->
  ?solver_tactic:string ->
  ?max_dispatch_attempts:int ->
  ?admit_all_sub_goals:bool ->
  ?stats_out_file:Fpath.t ->
  unit -> unit
(** [initialise args...] initialises the Sisyphus configuration
    parameters that are used by the rest of the runtime.


    - [filter_logs] is a PCRE regex that is used internally to filter
      logging output.  Only logging sources that match the regular
      expression will be printed.

    - [print_proof_extraction] determines whether sisyphus should
      print detailed traces of its proof reduction and extraction
      mechanism.

    - [dump_generated_invariants] determines whether sisyphus should
      dump any intermediate invariants it finds.

    - [log_level] specifies the logging level at which Sisyphus should
      be run

    - [log_dir] if specified informs Sisyphus to pipe all logging
      output to the specified log dir.

    - [dump_dir] if specified informs Sisyphus to turn on dumping of
      debugging information to the specified directory.

    - [dispatch_goals_with_tactic] indicates whether Sisyphus should
      dispatch generated subgoals using its solver tactic. Defaults to
      true.

    - [solver_tactic] is the tactic that sisyphus uses internally to
      dispatch subgoals. Defaults to [sis_generic_solver].

    - [max_dispatch_attempts] indicates the maximum number of attempts
      Sisyphus should make to find a invariant that the solver can
      dispatch before giving up and using admits. Defaults to 3.

    - [admit_all_sub_goals ()] indicates whether Sisyphus should admit
      all sub-goals that it runs into.

    - [stats_out_file] if specified informs Sisyphus to turn on writing of
      key statistics to the specified file.

*)

val dump_output: string -> ((('a, Format.formatter, unit, unit) format4 -> 'a) -> unit) -> unit
(** [dump_output name f] can be used to dump large amounts of raw
    debugging information to the specified dump directory under the
    filename [name]. This is useful for storing large output such as
    proof terms. *)

val dump_stats: unit -> unit
(** [dump_stats ()] can be used to write stats to the
    [stats_out_file] file. This is useful for collating data used
    to evaluate benchmarks, such as the number of invariants generated.
*)

val stats_incr_count: string -> unit
(** [stats_incr_count name] given an arbitrary statistic [name] increments its
    count *)

val stats_set_count: string -> int -> unit
(** [stats_set_count name c] given an arbitrary statistic [name] sets
    its counter value to [c] *)


val stats_start_timer: string -> unit
(** [stats_start_counter name] records the starting time for a counter [name],
    and throws and throws an exception if a previous counter is still running. *)

val stats_stop_timer: string -> unit
(** [stats_stop_counter name] stops the running counter for [name], and adds to
    the cumulative time spent on [name]. It throws an exception if there is no
    running counter. *)

val stats_time : string -> (unit -> 'a) -> 'a
(** [stats_time name f] times the result of [f] under the counter [name], and
    returns the result. *)
