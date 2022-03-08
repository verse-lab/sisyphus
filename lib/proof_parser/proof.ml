
type ty = Type of string list
        | Prod of ty list
 [@@deriving show, eq]

type param =
  | Implicit of string * ty
  | Explicit of string * ty
  | TupleParam of string list * ty
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

and spatial_expression =
  | PointsTo of string * pure_expression

and assertion =
  | Emp
  | Pure of pure_expression
  | Spatial of spatial_expression

and sep_spec = assertion list

and coq_expression = HeapSpec of sep_spec | FunctionalSpec of pure_expression
[@@deriving show, eq]  

type opaque_proof_script = string
[@@deriving show, eq]

type let_spec = param * param list * function_application * pure_expression
[@@deriving show, eq]

type spec_arg =
  | Lambda of param list * coq_expression
  | Pure of pure_expression
  | Hole
[@@deriving show, eq]   

type spec_app = SpecApp of string * spec_arg list
[@@deriving show, eq] 

type spec = Spec of param list * function_application * sep_spec * param * sep_spec
[@@deriving show, eq] 

type proof_step =
  | Xcf
  | Xpullpure of string list
  | Xpurefun of string * string * (string * ty) * spec
  | Xapp of spec_app * string list * string list
  | Xdestruct of string list
  | Rewrite of string * string
  | SepSplitTuple of string list
  | Xmatchcase of int * string list
  | Xvalemptyarr
  | Xalloc of string * string * string
  | Xletopaque of string * string
  | Intros of string list
  | Xvals of string list
  | Case of string * string * string list list * proof_step list list
[@@deriving show, eq] 

type proof = proof_step list
[@@deriving show, eq] 



type t = {
  directives: Command.t list;
  name: string;
  spec: spec;
  proof: proof;
} [@@deriving show, eq]


