
(** [get_consts_and_funcs ~from_id ~to_id ~env script] when given a
   proof script [script], retrieves a mapping of constants and
   functions used between proof points [from_id] and [to_id] indexed
   by their types and return types respectively. *)
val collect_consts_and_funcs: from_id:int -> to_id:int -> env:Types.env -> Proof_spec.Script.step list ->
  [> `Int of int ] list Types.TypeMap.t * (Containers.String.t * Lang.Type.t list) list Types.TypeMap.t


(** [collect_pats ~from_id ~to_id ~env script] when given a proof
   script [steps] collects patterns from expressions used in [script]
   between proof point [from_id] and [to_id]. *)
val collect_pats: from_id:int -> to_id:int -> env:Types.env -> Proof_spec.Script.step list -> Types.pat list Types.TypeMap.t
