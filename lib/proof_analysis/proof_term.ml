
type expr = Lang.Expr.t
type ty = Lang.Type.t
let pp_expr = Lang.Expr.pp_raw
let pp_ty = Lang.Type.pp_raw

type sym_heap =
  [
    (* `Heaplet of Proof_spec.Heap.Heaplet.t *)
    | `Invariant of expr
  ] list [@@deriving show]

type truncated_string = string
let pp_truncated_string fmt vl =
  Format.fprintf fmt "\"%s...\"" (String.escaped String.(sub vl 0 10))
let show_truncated_string = Format.asprintf "%a" pp_truncated_string

type proof_value = [
  | `Expr of expr
  | `Ty of ty
  | `Eq of ty * expr * expr
  | `Proof of truncated_string
] [@@deriving show]

type spec_arg = [
  | `Expr of expr
  | `ProofTerm of truncated_string
] [@@deriving show]
type spec_app = string * spec_arg list
[@@deriving show] 

type prop_type = {
  params: (string * proof_value) list;
  spec: string * expr list;
  pre: sym_heap;
  post: string * ty * sym_heap
} [@@deriving show]   

type t =
  | HimplHandR of sym_heap * t * t
  | HimplTrans of sym_heap * sym_heap * t * t
  | Lambda of string * proof_value * t
  | XLetVal of {
      pre: sym_heap;
      binding_ty: ty;
      let_binding: (string * ty);
      eq_binding: (string * (string * expr));
      value: expr;
      proof: t
    }
  | XLetTrmCont of {
      pre: sym_heap;
      binding_ty: ty;
      value_code: expr;
      proof: t
    }
  | XLetFun of {
      pre: sym_heap;
      proof: t
    }
  | XMatch of {value: (expr * expr) list; pre: sym_heap; proof: t}
  | XApp of {
      application: string * expr list;
      pre: sym_heap;
      fun_pre: sym_heap;
      proof_fun: t;
      proof: t
    }
  | XVal of { pre: sym_heap; value_ty: ty; value: expr }
  | XDone of sym_heap
  | VarApp of spec_app
  | AuxVarApp of string * spec_arg list * t
  | CharacteristicFormulae of {
      args: proof_value list;
      pre: sym_heap;
      proof: t
    }
  | AccRect of {
      prop_type: (string * ty) * prop_type;
      proof: acc_rect_proof;
      vl: expr;
      args: spec_arg list;
    }
  | Refl
and acc_rect_proof = {
  x: string; ty_x: ty;
  h_acc: string; ty_h_acc: string;
  ih_x: string; ty_ih_x: prop_type;
  proof: t
} [@@deriving show]

let tag = function
  | HimplHandR _ -> "HimplHandR"
  | HimplTrans _ -> "HimplTrans"
  | Lambda _ -> "Lambda"
  | XLetVal _ -> "XLetVal"
  | XLetTrmCont _ -> "XLetTrmCont"
  | XLetFun _ -> "XLetFun"
  | XMatch _ -> "XMatch"
  | XApp _ -> "XApp"
  | XVal _ -> "XVal"
  | XDone _ -> "XDone"
  | VarApp _ -> "VarApp"
  | AuxVarApp _ -> "AuxVarApp"
  | CharacteristicFormulae _ -> "CharacteristicFormulae"
  | AccRect _ -> "AccRect"
  | Refl -> "Refl"
