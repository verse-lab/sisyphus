open Containers
open Lang

module StringMap : module type of Map.Make(String)
module StringSet  : module type of Set.Make(String)

module Heaplet : sig
  type t = PointsTo of string * Type.t option * Expr.t [@@deriving show, eq, ord]

  val print: t -> PPrint.document

  val subst : (string -> Expr.t option) -> t -> t

  val subst_var : (string -> string option) -> t -> t

  val vars : ?with_funs:bool -> StringSet.t -> t -> StringSet.t

end

module ExprSet : module type of Set.Make(Expr)
module HeapSet : module type of Set.Make(Heaplet)

module Heap : sig
  type t[@@deriving eq, ord, show]

  val empty : t
  val is_empty : t -> bool

  val add_heaplet : Heaplet.t -> t -> t

  val add_heaplets : Heaplet.t list -> t -> t

  val add_heaplets_iter : Heaplet.t Iter.t -> t -> t

  val filter : (Heaplet.t -> bool) -> t -> t

  val get : string -> t -> Expr.t
  val get_with_ty : string -> t -> Type.t option * Expr.t
  val get_opt : string -> t -> Expr.t option

  val remove : string -> t -> t
  val remove_heaplet : Heaplet.t -> t -> t



  val to_list : t -> Heaplet.t list
  val of_list : Heaplet.t list -> t

  val iter : t -> Heaplet.t Iter.t
  val of_iter : Heaplet.t Iter.t -> t

  val fold : ('a -> Heaplet.t -> 'a) -> 'a -> t -> 'a

  val subst : (string -> Expr.t option) -> t -> t
  val subst_var : (string -> string option) -> t -> t

  val vars : ?with_funs:bool -> StringSet.t -> t -> StringSet.t

  val union : t -> t -> t
  val diff : t -> t -> t

  val mem : Heaplet.t -> t -> bool
  val mem_var : string -> t -> bool

end

module Assertion : sig
  type t [@@deriving eq, ord, show]

  val print: t -> PPrint.document

  val emp: t

  val of_list: Expr.t list * Heaplet.t list -> t
  val phi: t -> Expr.t list
  val sigma: t -> Heaplet.t list

  val filter_phi : (Expr.t -> bool) -> t -> t
  val filter_sigma : (Heaplet.t -> bool) -> t -> t

  val mem_expr : Expr.t -> t -> bool
  val mem_heaplet : Heaplet.t -> t -> bool
  val add_expr : Expr.t -> t -> t
  val remove_expr : Expr.t -> t -> t
  val add_heaplet : Heaplet.t -> t -> t
  val remove_heaplet : Heaplet.t -> t -> t
  val with_exprs : Expr.t list -> t -> t
  val with_exprs_iter : Expr.t Iter.t -> t -> t
  val with_heaplets : Heaplet.t list -> t -> t
  val with_heaplets_iter : Heaplet.t Iter.t -> t -> t
  val empty : t
  val union : t -> t -> t
  val diff : t -> t -> t
  val vars : ?with_funs:bool -> t -> StringSet.t -> StringSet.t
  val subst : (string -> Expr.t option) -> t -> t
  val subst_var : (string -> string option) -> t -> t
  val map_heap : (Heap.t -> Heap.t) -> t -> t
end
