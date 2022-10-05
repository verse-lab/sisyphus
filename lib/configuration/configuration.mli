
val validate_with_z3 : unit -> bool
(** [validate_with_z3] specifies whether the runtime system should
   check generated candidates using Z3. Defaults to true.  *)

val z3_default_timeout : unit -> int
(** [z3_default_timeout ()] is the timeout used by Z3 for simple goals. *)

val z3_challenging_timeout : unit -> int
(** [z3_challenging_timeout ()] is the timeout used by Z3 for complex
    logical goals *)

val max_z3_calls : unit -> int option
(** [max_z3_calls ()] if is [Some v] then [v] indicates the maximum
   number of calls to z3 that Sisyphus will make. If this is specified
   along with setting [validate_with_z3] to false, then after
   exceeding the max number of calls Sisyphus will just assume that its
   current invariant is valid.  *)


val initialize :
  ?default_timeout:int ->
  ?challenging_timeout:int ->
  ?max_calls:int ->
  ?filter_logs:string ->
  ?should_validate_with_z3:bool ->
  ?log_level:Logs.level ->
  ?log_dir:Fpath.t ->
  ?dump_dir:Fpath.t -> unit -> unit
(** [initialise args...] initialises the Sisyphus configuration
    parameters that are used by the rest of the runtime.

    - [default_timeout] is the timeout used by Z3 for simple goals

    - [challenging_timeout] is the timeout used by Z3 for complex
      logical goals

    - [filter_logs] is a PCRE regex that is used internally to filter
      logging output.  Only logging sources that match the regular
      expression will be printed.


    - [should_validate_with_z3] specifies whether the runtime system
      should check generated candidates using Z3. Defaults to true.


    - [log_level] specifies the logging level at which Sisyphus should
      be run

    - [log_dir] if specified informs Sisyphus to pipe all logging
      output to the specified log dir.


    - [dump_dir] if specified informs Sisyphus to turn on dumping of
      debugging information to the specified directory.  *)


val dump_output: string -> ((('a, Format.formatter, unit, unit) format4 -> 'a) -> unit) -> unit
(** [dump_output name f] can be used to dump large amounts of raw
    debugging information to the specified dump directory under the
    filename [name]. This is useful for storing large output such as
    proof terms. *)
