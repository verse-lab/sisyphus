
type ty = Type of string list
        | Prod of ty list
 [@@deriving show, eq]

type param =
  | Ident of string
  | Implicit of string * ty
  | Explicit of string * ty
 [@@deriving show, eq]

type function_application = (string * pure_expression list)
 [@@deriving show, eq]  

and pure_expression =
  | Var of string
  | Int of int
  | Eq of pure_expression * pure_expression
  | Add of pure_expression * pure_expression
  | Sub of pure_expression * pure_expression
  | Append of pure_expression * pure_expression
  | Cons of pure_expression * pure_expression
  | Tuple of pure_expression list
  | Predicate of string * pure_expression list
  | Lambda of param list * coq_expression
  | DestructurePair of string * string  * string * pure_expression


and spatial_expression =
  | PointsTo of string * pure_expression


and assertion =
  | Pure of pure_expression
  | Spatial of spatial_expression


and sep_spec = assertion list

and coq_expression = HeapSpec of sep_spec | FunctionalSpec of pure_expression
[@@deriving show, eq]  

type opaque_proof_script = string
[@@deriving show, eq]

type let_spec = param * param list * function_application * pure_expression
[@@deriving show, eq]

type proof_step =
  | Xcf
  | Xpull of opaque_proof_script list
  | Xapp of pure_expression option * opaque_proof_script list * opaque_proof_script list
  | Xvals of opaque_proof_script list
  | Xmatch of opaque_proof_script list * opaque_proof_script list
  | Xlet of let_spec option * opaque_proof_script list * opaque_proof_script list
  | Xseq
  | CaseEq of (string * string list list) * opaque_proof_script list * proof_step list list
  | Intros of string list
  | Xsimpl
[@@deriving show, eq] 

type proof = proof_step list
[@@deriving show, eq] 

type t = {
  directives: Command.t list;
  name: string;
  formal_params: param list;
  spec: function_application;
  pre: sep_spec;
  post: param * sep_spec;
  proof: proof;
} [@@deriving show, eq]


