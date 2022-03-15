module Heap' = Heap
open Containers
module Heap = Heap'

module PProof = Proof_parser.Proof

let rec convert_ty: PProof.ty -> Type.t = function
  | Type ["int"] -> Int
  | Type ["func"] -> Func
  | Type ["loc"] -> Loc
  | Type [v] -> Var v
  | Type ["list"; ty] -> List (Var ty)
  | Type ["array"; ty] -> Array (Var ty)
  | Type (fn :: args) -> ADT (fn, List.map (fun v -> Type.Var v) args)
  | Prod tys -> Product (List.map convert_ty tys)
  | ty -> 
    failwith @@ Format.sprintf "unsupported type: %a" PProof.pp_ty ty

type t =
  Type.t =
  | Unit
  | Var of string
  | Int
  | Func
  | Loc
  | List of Type.t
  | Array of Type.t
  | Ref of Type.t
  | ADT of string * Type.t list
  | Product of Type.t list

let extract_params param =
  List.fold_left (
    let handle_params ts vl = function
      | PProof.Explicit (var, ty) ->
        let ty : Type.t = convert_ty ty in
        `Params (ts, (var, ty) :: vl)
      | _ as param -> failwith @@ Format.sprintf "unsupported spec parameter: %a" PProof.pp_param param in
    let handle_type ts = function
      | PProof.Explicit (var, (Type ["Type"])) -> `Types (var :: ts)
      | PProof.Implicit _ -> `Types ts
      | t -> handle_params (List.rev ts) [] t in
    function
      `Types ts -> fun vl -> handle_type ts vl
    | `Params (ts,vl) -> handle_params ts vl
  ) (`Types []) param
  |> function `Types ts -> (List.rev ts, []) | `Params (ts,vl) -> (ts, List.rev vl)

let convert_pattern_expression : PProof.pure_expression -> Expr.param = function
  | Var v -> `Var v
  | Tuple args ->
    let args = List.map (function PProof.Var v -> v
                                | e -> failwith @@ Format.sprintf "unsupported spec parameter: %a" PProof.pp_pure_expression e
    ) args in
    `Tuple args
  | e -> failwith @@ Format.sprintf "unsupported spec parameter: %a" PProof.pp_pure_expression e

let rec convert_pure_expression : PProof.pure_expression -> Expr.t = function
  | Var v -> `Var v
  | Int i -> `Int i
  | Add (l, r) ->
    let l = convert_pure_expression l in
    let r = convert_pure_expression r in
    `App ("(+)", [l;r])
  | Sub (l, r) ->
    let l = convert_pure_expression l in
    let r = convert_pure_expression r in
    `App ("(-)", [l;r])
  | Append (l, r) ->
    let l = convert_pure_expression l in
    let r = convert_pure_expression r in
    `App ("List.append", [l;r])
  | Cons (h, t) ->
    let h = convert_pure_expression h in
    let t = convert_pure_expression t in
    `Constructor ("::", [h;t])
  | Tuple elts ->
    let elts = List.map convert_pure_expression elts in
    `Tuple elts
  | Predicate (h, args) ->
    let args = List.map convert_pure_expression args in
    `Constructor (h, args)
  | Eq (l, r) ->
    let l = convert_pure_expression l in
    let r = convert_pure_expression r in
    `Constructor ("=", [l;r])

let convert_spatial_expression : PProof.spatial_expression -> Heap.Heaplet.t = function
  | PProof.PointsTo (var, exp) ->
    PointsTo (var, convert_pure_expression exp)

let convert_assertion: PProof.sep_spec -> Heap.Assertion.t =
  fun vl -> 
  List.fold_left (fun (pure, spatial) : (PProof.assertion -> _) -> function
    | PProof.Emp -> (pure,spatial)
    | PProof.Pure exp -> (convert_pure_expression exp :: pure, spatial)
    | PProof.Spatial spat -> (pure, convert_spatial_expression spat :: spatial)
  ) ([],[]) vl
  |> Pair.map List.rev List.rev
  |> Heap.Assertion.of_list


let convert_spec: PProof.spec -> Proof.spec = function
    Proof_parser.Proof.Spec (param, f_app, pre, res_param, post) ->
    let types, params  =  extract_params param in
    let invariants = [] in
    let pure_preconditions = [] in
    let impure_preconditions = [] in
    let pre = convert_assertion pre in
    let res_param = match res_param with
      | PProof.Explicit (arg, ty) -> (arg, convert_ty ty)
      | param -> failwith @@ Format.sprintf "unsupported spec result parameter: %a" PProof.pp_param param in
    let post = convert_assertion post in
    let application =
      let fn, args = f_app in
      let args =
        List.map (function
            PProof.Var v -> v
          | e -> failwith @@
            Format.sprintf "unsupported function application arg %a"
              PProof.pp_pure_expression e
        ) args in
      fn, args in
    ({
      types;
      params;
      invariants;
      pure_preconditions;
      impure_preconditions;
      pre;
      res_param;
      post;
      application;
    }: Proof.spec)

let convert_param : PProof.param -> Expr.typed_param = function
  | PProof.Implicit (v, ty) -> `Var (v, convert_ty ty)
  | PProof.Explicit (v, ty) -> `Var (v, convert_ty ty)
  | PProof.TupleParam (args, PProof.Prod ty) -> `Tuple (List.combine args (List.map convert_ty ty))
  | PProof.TupleParam (_args, PProof.Type _) -> failwith "not supported"
let convert_param_ty : PProof.param -> Expr.param * _ = function
  | PProof.Implicit (v, ty) -> (`Var v, convert_ty ty)
  | PProof.Explicit (v, ty) -> (`Var v, convert_ty ty)
  | PProof.TupleParam (args, ty) -> (`Tuple args, convert_ty ty)


let convert_spec_arg : PProof.spec_arg -> Proof.spec_arg = function
  | PProof.Lambda (params, HeapSpec heapspec) ->
    let params = List.map convert_param_ty params in
    let body = convert_assertion heapspec in
    `Spec (params, body)
  | PProof.Lambda (params, FunctionalSpec body) ->
    let params = List.map convert_param params in
    let body = convert_pure_expression body in
    `Expr (`Lambda (params, body))
  | PProof.Pure e -> `Expr (convert_pure_expression e)
  | PProof.Hole -> `Hole

let (let+) x f = x f

let rec mapM f ls kont =
  match ls with
  | [] -> kont []
  | h :: t ->
    let+ h = f h in
    let+ t = mapM f t in
    kont (h :: t)

let rec convert_proof ls (kont : (Proof.step list -> 'a)) : 'a = match ls with
  | [] -> kont []
  | PProof.Xcf :: rest ->
    let+ rest = convert_proof rest in
    kont (`Xcf :: rest)
  | (Xpullpure vars) :: rest ->
    let+ rest = convert_proof rest in
    kont (`Xpullpure vars :: rest)
  | Xapp (SpecApp (fn, args), _, _) :: Intros vars :: rest ->
    let args = List.map convert_spec_arg args in
    let rule = `Xapp (fn, args, vars) in
    let+ rest = convert_proof rest in
    kont (rule :: rest)
  | Xapp (SpecApp (fn, args), _, _) :: rest ->
    let args = List.map convert_spec_arg args in
    let rule = `Xapp (fn, args, []) in
    let+ rest = convert_proof rest in
    kont (rule :: rest)
  | Xdestruct vars :: rest ->
    let rule = `Xdestruct vars in
    let+ rest = convert_proof rest in
    kont (rule :: rest)
  | Rewrite (lemma, hyp) :: rest ->
    let rule = `Rewrite (lemma,hyp) in
    let+ rest = convert_proof rest in
    kont (rule :: rest)
  | SepSplitTuple (heq :: hn) :: rest ->
    let rule = `SepSplitTuple (heq, hn) in
    let+ rest = convert_proof rest in
    kont (rule :: rest)
  | Xmatchcase (i, intros) :: rest ->
    let rule = `Xmatchcase (i, intros) in
    let+ rest = convert_proof rest in
    kont (rule :: rest)
  | Xvalemptyarr :: rest ->
    let rule = `Xvalemptyarr in
    let+ rest = convert_proof rest in
    kont (rule :: rest)
  | Xalloc (arr, data, h_data) :: rest ->
    let rule = `Xalloc (arr, data, h_data) in
    let+ rest = convert_proof rest in
    kont (rule :: rest)
  | Xletopaque (f, h_f) :: rest ->
    let rule = `Xletopaque (f,h_f) in
    let+ rest = convert_proof rest in
    kont (rule :: rest)
  | Xvals _ :: rest ->
    let rule = `Xvals in
    let+ rest = convert_proof rest in
    kont (rule :: rest)    
  | Case (var, h_eq, intros, cases) :: rest ->
    let+ cases = mapM convert_proof cases in
    let sub_proofs = List.combine intros cases in
    let rule = `Case (var, h_eq, sub_proofs) in
    let+ rest = convert_proof rest in
    kont (rule :: rest)    
  | Intros _ :: _ -> failwith "solo intro pattern unsupported at the moment"
  | h :: _ -> failwith @@ Format.sprintf "unsupported at the moment %a" PProof.pp_proof_step h

let convert_proof ls = convert_proof ls Fun.id
