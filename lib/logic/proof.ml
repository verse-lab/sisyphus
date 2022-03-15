module Heap' = Heap 
open Containers
module Heap = Heap'
module PP = PPrint

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


let print_param (var, ty) =
  let open PP in
  parens ( string var ^^ string ":"  ^^ space ^^ Type.print ty)
  
let rec print_spec spec =
  let open PP in
  let print_type = (fun ty -> (parens @@ (string ty ^^ string ":" ^^ space ^^ string "Type"))) in
  let print_invariant (arg, exp) =
    parens (string arg ^^ string ":" ^/^ flow_map (string " ->" ^^ break 1)  Expr.print exp ^^ string " -> hprop") in
  let print_pure_preconditions exprs =
    flow_map (string " ->" ^^ break 1) (fun exp -> parens @@ Expr.print exp) exprs in
  group (
    group (fancystring "∀" 1 ^/^ group (flow_map space print_type spec.types)) ^^ string "," ^/^
    group (flow_map (break 1) print_param spec.params)  ^^ string "," ^^
    (if List.is_empty spec.invariants then empty else
       group (flow_map (string "," ^^ break 1) print_invariant spec.invariants) ^^ string ",") ^^
    (if List.is_empty spec.pure_preconditions then empty else
       print_pure_preconditions spec.pure_preconditions ^^ string " -> ") ^^
    (if List.is_empty spec.impure_preconditions then empty else
      separate_map (break 1) (fun sp -> parens @@ print_spec sp) spec.impure_preconditions ^^ string " -> ") ^/^
    (braces @@ group (Heap.Assertion.print spec.pre)) ^/^
    (braces @@ group (print_param spec.res_param ^/^ group (string "=>" ^/^ group (Heap.Assertion.print spec.post))))
  ) 
let pp_spec fmt vl = PP.ToFormatter.pretty 0.999999999999 80 fmt (print_spec vl)
let show_spec = Format.to_string pp_spec

type spec_arg = [
    `Expr of Expr.t
  | `Spec of (Expr.param * Type.t) list * Heap.Assertion.t
  | `Hole
] [@@deriving show]

let print_spec_param (param, ty) =
  let open PP in
  parens (group (Expr.print_param param ^^ string ": " ^^ Type.print ty))

let print_spec_arg = let open PP in function
  | `Expr e -> Expr.print e
  | `Hole -> string "(??)"
  | `Spec (params, spec) ->
    group (group (fancystring "∀" 1 ^/^ group (flow_map space print_spec_param params)) ^^ string "," ^/^
           Heap.Assertion.print spec)

type simple = Expr.simple_t
let pp_simple = Expr.pp_simple

type step = [
  | `Xcf
  | `Xpullpure of string list
  (**
    Γ ∪ {x1: P1 ᠁ xn: Pn} {P; H} C {res ↠ Q}
     ------------------------ XPullPure (x1,...,xn)
    Γ, {P1,᠁ Pn, P;H} C {res ↠ Q}
  *)
  | `Xpurefun of string * string * [`Lambda of Expr.typed_param list * simple]
  (**
     lam = fun args -> body, pure_expr(body)
     Γ ∪ {f : func, Hf: f = lam}, {P} e {res ↠ Q}
     ------------------------ XPureFun (f,Hf, lam)
     Γ, {P} let f = fun args -> body in e  {res ↠ Q}
  *)
  | `Xapp of string * spec_arg list * string list
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

let print_step print_steps : step -> PP.document = let open PP in function
  | `SepSplitTuple (h, vars) ->
    (string "SepSplittuple" ^/^ string h ^^ group (break 1 ^^ separate_map space string vars) ^^ string ".")
  | `Xvals -> string "Xvals."
  | `Xvalemptyarr -> string "Xvalemptyarr."
  | `Xcf -> string "xcf."
  | `Xdestruct vars ->
    (string "Xdestruct" ^^ group (break 1 ^^ separate_map space string vars) ^^ string ".")
  | `Xalloc (arr,data,h_data) ->
    (string "Xalloc" ^^ group (space ^^ string arr ^/^ string data ^/^ string h_data) ^^ string ".")      
  | `Xletopaque (f,h_f) ->
    (string "Xletopaque" ^^ group (space ^^ string f ^/^ string h_f) ^^ string ".")      
  | `Rewrite (lemma, h) ->
    (string "rewrite" ^^ group (space ^^ string lemma ^/^ string "in" ^/^ string h) ^^ string ".")      
  | `Xpullpure vars ->
    (group (string "Xpullpure" ^^ align (group (space ^^ separate_map space string vars)) ^^ string "."))
  | `Xmatchcase (i, vars)  ->
    (string ("Xmatch_case_" ^ Int.to_string i) ^/^ group (break 1 ^^ separate_map space string vars) ^^ string ".")        
  | `Xapp (fn, args, intrs) ->
    group (string "Xapp" ^/^ parens (
       string fn ^/^ group (break 1 ^^ separate_map space print_spec_arg args)
     ) ^^ string ".") ^/^
    (if List.is_empty intrs then empty else
       group (string "intros" ^/^ group (break 1 ^^ separate_map space string intrs) ^^ string "."))
  | `Xpurefun (f, h_f, `Lambda (params, expr)) ->
    group (string "Xpurefun" ^/^ string f ^/^ string h_f ^/^
           Expr.print (`Lambda (params, (expr :> Expr.t))) ^^ string ".")
  | `Case (l, h_l, cases) ->
    group (string "case" ^/^ string l ^/^ string "as" ^/^ braces (
       flow_map (string " |" ^^ break 1) (fun (vars, _) -> separate_map space string vars) cases
     ) ^/^ string "eqn:" ^^ string h_l ^^ string ".") ^^
    nest 2 (break 1 ^^ separate_map (hardline) (fun (_, prf) -> group (string " - " ^^ align (print_steps prf))) cases)

let rec print_steps : step list -> PP.document =
  let open PP in
  fun steps -> group (separate_map (break 1) (print_step print_steps) steps)
let print_step = print_step (fun _ -> PP.string "...")

let pp_step fmt vl = PP.ToFormatter.pretty 10.99 80 fmt (print_step vl)
let show_step vl = Format.to_string pp_step vl
let pp_steps fmt vl = PP.ToFormatter.pretty 0.99 80 fmt (print_steps vl)
let show_steps vl = Format.to_string pp_steps vl                        
