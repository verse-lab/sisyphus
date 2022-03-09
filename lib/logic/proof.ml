module Heap' = Heap 
open Containers
module Heap = Heap'

module StringMap = Containers.Map.Make(String)

type 'a ctx = {
  types: string list;
  variables: Type.t StringMap.t;
  relations: (string * Expr.t list) StringMap.t;
  equalities: (Expr.t * Expr.t) StringMap.t;
  specifications: (string * 'a Program.lambda) StringMap.t;

  pre: Heap.Assertion.t;
  res_param: string * Type.t;
  post: Heap.Assertion.t;

  state: [`Init of 'a Program.t | `Step of 'a Program.stmt ]
}


type spec = {
  types: string list;                                         (* ∀ A..., *)
  params: (string * Type.t) list;                                (*  (v1: t1)...(vn: tn),  *)
  invariants: (string * Expr.t list) list;                    (* I: int .... -> hprop, *)
  pure_preconditions: Expr.t list;                            (* l = t ++ v :: r  *)
  impure_preconditions: spec list;                            (* (∀ acc, ... { t acc } f acc v {x => I ... } )  *)
  pre: Heap.Assertion.t;                                      (* {P} *)
  res_param: string * Type.t;                                    (* { x => ... } *)
  post: Heap.Assertion.t;                                     (* {Q} *)
  application: string * string list;                          (* f a b c *)
}

type spec_arg = [
    `Expr of Expr.t
  | `Spec of (string * Type.t) list * Heap.Assertion.t
  | `Hole
]



type step = [
  | `Xpullpure of string list
  (**
    Γ ∪ {x1: P1 ᠁ xn: Pn} {P; H} C {res ↠ Q}
     ------------------------ XPullPure (x1,...,xn)
    Γ, {P1,᠁ Pn, P;H} C {res ↠ Q}
  *)
  | `Xpurefun of string * string * [`Lambda of Expr.param list * Expr.simple_t]
  (**
     lam = fun args -> body, pure_expr(body)
     Γ ∪ {f : func, Hf: f = lam}, {P} e {res ↠ Q}
     ------------------------ XPureFun (f,Hf, lam)
     Γ, {P} let f = fun args -> body in e  {res ↠ Q}
  *)
  | `Xapp of spec * spec_arg list * string list
  (**
     spec = ∀ v1..vn, {Pf} f args res => {res ↠ res = vl, Qf1...Qfm; Hf}
     {P} ⊫ {Pf}[ai/vi]  vl' = vl[ai/vi]
     Γ ∪ {∀ i,  ei: Qfi[ai/vi]} {P} let f = vl' in e {res ↠ Q}
     ------------------------ XApp (spec, a1...an, e,e1..em)
     Γ, {P} let f = f args in e  {res ↠ Q}
  *)
  | `Xdestruct of string list
  (**
     pure_expr(e_s)
     Γ ∪ {∀ i, vi: τi} ∪ {H: (v1,..,vn) = e_s}, {P} e {res ↠ Q}    
     ------------------------ XDestruct (v1,..,vn,H)
     Γ, {P} let (v1,..,vn) = e_s in e  {res ↠ Q}    
  *)
  | `Rewrite of string * string
  (**
     pure_expr(e_s)
     Γ ∪ {Hfrom: e1 = e2, Hin: e3[e2/e1]}, {P} e {res ↠ Q}    
     ------------------------ Rewrite (Hfrom,Hin)
     Γ ∪ {Hfrom: e1 = e2, Hin: e3}, {P} e {res ↠ Q}    
  *)
  | `SepSplitTuple of string * string list
  (**
     pure_expr(e_s)
     Γ ∪ {∀ i, Hi: eli = eri}, {P} e {res ↠ Q}    
     ------------------------ SepSplitTuple (Heq,H1,..,Hn)
     Γ ∪ {Heq: (el1,...eln) = (er1,...ern)}, {P} e {res ↠ Q}    
  *)
  | `Case of string * string * (string list * step list) list
  (**
     τ = C1 a11..a1m | ... | Cn an1 ... anm

     ∀ i,
     Γ ∪ {ail : τ1,..., aim : τm, H: l = Ci ail..aim}, {P} e {res ↠ Q}    
     ------------------------ Case(l,H)
     Γ ∪ {l : τ}, {P} e {res ↠ Q}    
  *)
  | `Xmatchcase of int * string list
  (**
     τ = C1 a11..a1m | ... | Cn an1 ... anm
     Γ, {P} ⊫ e = Ci x1 ... xn
     Γ ∪ {∀ i, xi : τi}, {P} ei  {res ↠ Q}    
     ------------------------ XMatchCase(i,x1,...,xn)
     Γ, {P} match e with C1 a1...am -> e1 | ... | Cn an1 ... anm -> en  {res ↠ Q}    
  *)
  | `Xvalemptyarr
  (**
     Γ, {P} ⊫ Q * res → Array []
     ------------------------ XValEmptyArr
     Γ, {P} [| |] {res ↠ Q * res → Array ls}
  *)
  | `Xalloc of string * string * string
  (**
     Γ ∪ {vl: τ, arr: loc, data: list τ, Hdata: data = repeat sz vl},
       {P * arr  → Array data} e {res ↠ Q}
     ------------------------ XAlloc(arr,data,Hdata)
     Γ ∪ {vl: τ}, {P} let arr = Array.make sz vl in e {res ↠ Q}
  *)
  | `Xletopaque of string * string
  (**
     simple_expr(ev)
     Γ ∪ {v: τ, Hv: v = ev}, {P} e {res ↠ Q}
     ------------------------ XLetOpaque(v,Hv)
     Γ, {P} let v = ev in e {res ↠ Q}


     Γ ∪ {v: τ, Hv: code_of(v, ev)}, {P} e {res ↠ Q}
     ------------------------ XLetOpaque(v,Hv)
     Γ, {P} let v = ev in e {res ↠ Q}
  *)
  | `Xvals
  (**
     Γ ∪ {P} ⊫ {Q[v/res]}
     ------------------------ XLetOpaque(v,Hv)
     Γ, {P} v {res ↠ Q}
  *)
]
