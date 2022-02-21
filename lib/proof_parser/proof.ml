
type ty = string list
 [@@deriving show, eq]

type param =
  | Ident of string
  | Implicit of string * ty
  | Explicit of string * ty
 [@@deriving show, eq]

type function_application = (string * string list)
 [@@deriving show, eq]  

type pure_expression =
  | Var of string
  | Int of int
  | Add of pure_expression * pure_expression
  | Sub of pure_expression * pure_expression
  | Append of pure_expression * pure_expression
  | Predicate of string * pure_expression list
  | Lambda of param list * coq_expression


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

type proof_step =
  | Xcf
  | Xpull of opaque_proof_script list
  | Xapp of pure_expression option * opaque_proof_script list * opaque_proof_script list
  | Xvals of opaque_proof_script list
  | Xmatch
  | Xlet
  | Xseq
  | CaseEq of (string * string list list) * opaque_proof_script list * proof_step list list
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


