type t =
  | HimplHandR of string * t * t
  | HimplTrans of string * string * t * t
  | Lambda of string * string * t
  | XLetVal of {
      pre: string;
      binding_ty: string;
      let_binding: (string * string);
      eq_binding: (string * string);
      value: string;
      proof: t
    }
  | XLetTrmCont of {
      pre: string;
      binding_ty: string;
      value_code: string;
      proof: t
    }
  | XMatch of {pre: string; proof: t}
  | XApp of { pre: string; fun_pre: string; proof_fun: t; proof: t }
  | XVal of { pre: string; value_ty: string; value: string }
  | XDone of string
  | VarApp of string
  | CharacteristicFormulae of {
      args: string list;
      pre: string;
      proof: t
    }
  | AccRect of {
      prop_type: string;
      proof: acc_rect_proof;
      vl: string;
      args: string list;
    }
  | Refl
and acc_rect_proof = {
  x: string; ty_x: string;
  h_acc: string; ty_h_acc: string;
  ih_x: string; ty_ih_x: string;
  proof: t
} [@@deriving show]
