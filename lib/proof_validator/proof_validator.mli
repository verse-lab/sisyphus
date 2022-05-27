module VerificationCondition = Verification_condition

type pure_candidate = Lang.Expr.t list -> Lang.Expr.t
(** A pure candidate expression represents a pure boolean expression
   parameterised over a varying number of expressions.  *)

type heap_candidate = Lang.Expr.t list -> Lang.Expr.t array
(** A heap candidate expression represents a list of candidate
   expressions to fill in holes in a heap parameterised over a varying
   number of expressions. *)

type candidate = pure_candidate * heap_candidate
(** A verification candidate is a pair of a pure and heap candidate  *)

type validator = candidate -> [ `InvalidPure | `InvalidSpatial | `Valid ]
(** A validator takes a verification candidate and returns a
   verification outcome - either the candidate is valid w.r.t the
   verification condition, or either the pure or spatial parts are
   invalid. *)

(** [build_validator vc] given a verification condition builds a
   validator function that can be used to validate candidate
   expressions.  *)
val build_validator : VerificationCondition.verification_condition -> validator
