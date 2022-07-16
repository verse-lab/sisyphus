
type sym_heap =
  [
    (* `Heaplet of Proof_spec.Heap.Heaplet.t *)
  | `Invariant of Lang.Expr.t
  ] list [@@deriving show]

type proof_value = [
  | `Expr of Lang.Expr.t
  | `Ty of Lang.Type.t
  | `Proof of string
] [@@deriving show]

type spec_arg = [
  | `Expr of Lang.Expr.t
  | `ProofTerm
] [@@deriving show]
type spec_app = string * spec_arg list
[@@deriving show] 

type prop_type = {
  params: (string * proof_value) list;
  spec: string * Lang.Expr.t list;
  pre: sym_heap;
  post: string * Lang.Type.t * sym_heap
} [@@deriving show]   

type t =
  | HimplHandR of sym_heap * t * t
  | HimplTrans of sym_heap * sym_heap * t * t
  | Lambda of string * proof_value * t
  | XLetVal of {
      pre: sym_heap;
      binding_ty: Lang.Type.t;
      let_binding: (string * Lang.Type.t);
      eq_binding: (string * (string * Lang.Expr.t));
      value: Lang.Expr.t;
      proof: t
    }
  | XLetTrmCont of {
      pre: sym_heap;
      binding_ty: Lang.Type.t;
      value_code: Lang.Expr.t;
      proof: t
    }
  | XMatch of {pre: sym_heap; proof: t}
  | XApp of { pre: sym_heap; fun_pre: sym_heap; proof_fun: t; proof: t }
  | XVal of { pre: sym_heap; value_ty: Lang.Type.t; value: Lang.Expr.t }
  | XDone of sym_heap
  | VarApp of spec_app
  | CharacteristicFormulae of {
      args: proof_value list;
      pre: sym_heap;
      proof: t
    }
  | AccRect of {
      prop_type: (string * Lang.Type.t) * prop_type;
      proof: acc_rect_proof;
      vl: Lang.Expr.t;
      args: spec_app list;
    }
  | Refl
and acc_rect_proof = {
  x: string; ty_x: Lang.Type.t;
  h_acc: string; ty_h_acc: string;
  ih_x: string; ty_ih_x: prop_type;
  proof: t
} [@@deriving show]
