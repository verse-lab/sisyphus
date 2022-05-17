open Containers
module StringMap = Map.Make(String)

type expr = Lang.Expr.t
type holy_expr = expr -> expr
type ty = Lang.Type.t
type 'a map = 'a StringMap.t

let pp_expr = Lang.Expr.pp
let pp_ty = Lang.Type.pp
let pp_holy_expr fmt v =
  pp_expr fmt (v (`Var "??"))
let pp_map f fmt vl =
  StringMap.pp
    ~pp_start:(fun fmt () -> Format.fprintf fmt "{")
    ~pp_stop:(fun fmt () -> Format.fprintf fmt "}")
    ~pp_arrow:(fun fmt () -> Format.fprintf fmt " -> ")
    ~pp_sep:(fun fmt () -> Format.fprintf fmt ",@ ")
    Format.pp_print_string
    f fmt vl

type 'a condition = {
  quantified_over: (string * ty) list; (* list of variables being quantified over *)
  assumptions: (expr * expr) list;     (* list of assumed equalities *)
  goal: 'a;                             (* expression to be proved *)
} [@@deriving show]

type initial_vc = {
  assumptions: (expr * expr) list; (* assumptions *)
  expr_values: expr array; (* values for variables *)
  param_values: expr map;  (* initial values for invariant parameters *)
} [@@deriving show]

type vc = {
  qf: (string * ty) list;

  param_values: expr map;
  assumptions: (expr * expr) list;

  post_param_values: expr map;
  expr_values: holy_expr array;
} [@@deriving show]

type verification_condition = {
  initial: initial_vc;
  conditions: vc list;
} [@@deriving show]

let is_coq_eq fn =
  Constr.isInd fn &&
  String.(Constr.destInd fn |> fst |> fst |> Names.MutInd.label |> Names.Label.to_string = "eq")

let is_ind_eq str fn =
  Constr.isInd fn &&
  String.equal str
    (Constr.destInd fn |> fst |> fst |> Names.MutInd.to_string)

let is_constr_eq str fn =
  Constr.isConstruct fn &&
  String.equal str
    (Constr.destConstruct fn |> fst |> fst |> fst |> Names.MutInd.to_string)

let is_const_eq str fn =
  Constr.isConst fn &&
  String.equal str
    (Constr.destConst fn |> fst |> Names.Constant.to_string)


let is_constr_cons fn =
  is_constr_eq "Coq.Init.Datatypes.list" fn
    && (Constr.destConstruct fn |> fst |> snd) = 2

let is_constr_nil fn =
  is_constr_eq "Coq.Init.Datatypes.list" fn
    && (Constr.destConstruct fn |> fst |> snd) = 1

let is_constr_z0 fn =
  is_constr_eq "Coq.Numbers.BinNums.Z" fn
    && (Constr.destConstruct fn |> fst |> snd) = 1

let is_constr_zpos fn =
  is_constr_eq "Coq.Numbers.BinNums.Z" fn
    && (Constr.destConstruct fn |> fst |> snd) = 2

let is_constr_zneg fn =
  is_constr_eq "Coq.Numbers.BinNums.Z" fn
    && (Constr.destConstruct fn |> fst |> snd) = 3

let is_constr_pos_x0 fn =
  is_constr_eq "Coq.Numbers.BinNums.positive" fn
    && (Constr.destConstruct fn |> fst |> snd) = 2

let is_constr_pos_x1 fn =
  is_constr_eq "Coq.Numbers.BinNums.positive" fn
    && (Constr.destConstruct fn |> fst |> snd) = 1

let is_constr_pos_xh fn =
  is_constr_eq "Coq.Numbers.BinNums.positive" fn
    && (Constr.destConstruct fn |> fst |> snd) = 3


let rec extract_typ (c: Constr.t) : Lang.Type.t =
  match Constr.kind c with
  | Constr.Ind ((name, _), univ) -> begin
      match Names.MutInd.to_string name with
      | "Coq.Numbers.BinNums.Z" -> Int
      | _ -> Format.ksprintf ~f:failwith "found unknown type %s" (Names.MutInd.to_string name)
    end
  | Constr.App (fname, [|ty|]) when is_ind_eq "Coq.Init.Datatypes.list" fname -> 
      List (extract_typ ty)
  | Constr.App (fname, args) when is_ind_eq "Coq.Init.Datatypes.prod" fname ->
    Product (Array.to_iter args |> Iter.map extract_typ |> Iter.to_list)
  | Constr.Var name -> Var (Names.Id.to_string name)
  | _ ->
    Format.ksprintf ~f:failwith "found unhandled Coq term (%s) that could not be converted to a type"
      (Proof_debug.constr_to_string c)

let extract_const_int (c: Constr.t) : Lang.Expr.t =
  let rec extract_int c =
    match Constr.kind c with
    | Constr.App (const, [|inner|]) when is_constr_pos_x0 const ->
      2 * (extract_int inner)
    | Constr.App (const, [|inner|]) when is_constr_pos_x1 const ->
      1 + 2 * (extract_int inner)
    | _ when is_constr_pos_xh c ->
      1
    | _ ->
    Format.ksprintf ~f:failwith "found unhandled Coq term (%s) that could not be converted to a constant int"
      (Proof_debug.constr_to_string c) in
  match Constr.kind c with
  | Constr.App (const, [|inner|]) when is_constr_zpos const ->
    `Int (extract_int inner)
  | Constr.App (const, [|inner|]) when is_constr_zneg const ->
    `Int (- (extract_int inner))
  | Constr.App (const, [| |]) when is_constr_z0 const ->
    `Int 0
  | _ -> 
    Format.ksprintf ~f:failwith "found unhandled Coq term (%s) that could not be converted to a constant int expr"
      (Proof_debug.constr_to_string c)

let rec extract_expr ctx (c: Constr.t) : Lang.Expr.t =
  match Constr.kind c with
  | Constr.Var v -> `Var (Names.Id.to_string v)
  | Constr.App (const, [|ty; h; tl|]) when is_constr_cons const ->
    `Constructor ("::", [extract_expr ctx h; extract_expr ctx tl])
  | Constr.App (const, [|ty|]) when is_constr_nil const ->
    `Constructor ("[]", [])
  | Constr.App (const, _) when is_constr_eq "Coq.Numbers.BinNums.Z" const ->
    extract_const_int c
  | Constr.App (const, args) when is_constr_eq "Coq.Init.Datatypes.prod" const ->
    let no_types = Array.length args / 2 in
    let args = Array.to_iter args
               |> Iter.drop no_types
               |> Iter.map (extract_expr ctx)
               |> Iter.to_list in
    `Tuple (args)
  | Constr.App (fname, [| l; r |]) when is_const_eq "Coq.ZArith.BinInt.Z.sub" fname ->
    `App ("-", [extract_expr ctx l; extract_expr ctx r])    
  | Constr.App (fname, [| l; r |]) when is_const_eq "Coq.ZArith.BinInt.Z.add" fname ->
    `App ("+", [extract_expr ctx l; extract_expr ctx r])    
  | Constr.App (fname, [| l; r |]) when is_const_eq "Coq.ZArith.BinInt.Z.mul" fname ->
    `App ("*", [extract_expr ctx l; extract_expr ctx r])    
  | Constr.App (fname, args) when Constr.isConst fname ->
    let args = Array.to_iter args |> Iter.drop 1 |> Iter.map (extract_expr ctx) |> Iter.to_list in
    let fname, _ = Constr.destConst fname in
    `App (Names.Constant.to_string fname, args)
  | _ ->
    Format.ksprintf ~f:failwith "found unhandled Coq term (%s)[%s] in %s that could not be converted to a expr"
      (Proof_debug.constr_to_string c) (Proof_debug.tag c) (Proof_debug.constr_to_string_pretty c)
  

let build_verification_condition (t: Proof_context.t) : verification_condition =
  let assumptions = 
    List.filter_map (fun (name, o_vl, vl) ->
      let _name = (List.map Names.Id.to_string name |> String.concat ".") in
      begin match Constr.kind vl with
      | Constr.Sort _ -> None     (* represents (A: Type) *)
      | Constr.App (fn, [| ty; l; r |]) when is_coq_eq fn ->
        let ty = extract_typ ty in
        let l = extract_expr t l in
        let r = extract_expr t r in
        Some (ty, l, r)
      | Constr.App (fn, args) -> (* list A, and eq, and others *) None
      | Constr.Ind _              (* credits? *)
      | Constr.Var _              (* init: A *)
      | Constr.Const _ -> None
      | _ -> None
      end
    ) (Proof_context.current_goal t).hyp in

  List.iter (fun (ty, l, r) ->
    Format.printf "%a = %a (%a)@."
      Lang.Expr.pp l 
      Lang.Expr.pp r 
      Lang.Type.pp ty
  ) assumptions;
  assert false
