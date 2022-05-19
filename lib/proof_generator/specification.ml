open Containers
module IntSet = Set.Make(Int)
module StringMap = Map.Make(String)

let () =
  Printexc.register_printer (function
      Failure msg -> Some msg
    | _ -> None
  )

type def_map = [ `Lambda of Lang.Expr.typed_param list * Lang.Expr.t Lang.Program.stmt ] StringMap.t
type expr = Lang.Expr.t
type holy_expr = expr -> expr
type ty = Lang.Type.t
type 'a map = 'a StringMap.t

let pp_expr = Lang.Expr.pp
let pp_ty = Printer.pp_ty
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

type initial_vc = {
  expr_values: expr array; (* values for variables *)
  param_values: expr list;  (* initial values for invariant parameters *)
} [@@deriving show]

type vc = {
  qf: (string * ty) list;

  param_values: expr list;
  assumptions: (expr * expr) list;

  post_param_values: expr list;
  expr_values: holy_expr array;
} [@@deriving show]

type verification_condition = {
  env: (string * ty) list;
  assumptions: (expr * expr) list; (* assumptions *)
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


let rec extract_typ ?rel (c: Constr.t) : Lang.Type.t =
  match Constr.kind c, rel with
  | Constr.Ind ((name, _), univ), _ -> begin
      match Names.MutInd.to_string name with
      | "Coq.Numbers.BinNums.Z" -> Int
      | "CFML.Semantics.val" -> Var "val"
      | _ -> Format.ksprintf ~f:failwith "found unknown type %s" (Names.MutInd.to_string name)
    end
  | Constr.App (fname, [|ty|]), _ when is_ind_eq "Coq.Init.Datatypes.list" fname -> 
    List (extract_typ ?rel ty)
  | Constr.App (fname, [|ty|]), _ when is_const_eq "CFML.WPBuiltin.array" fname -> 
    Array (extract_typ ?rel ty)
  | Constr.App (fname, args), _ when is_ind_eq "Coq.Init.Datatypes.prod" fname ->
    Product (Array.to_iter args |> Iter.map (extract_typ ?rel) |> Iter.to_list)
  | Constr.Var name, _ -> Var (Names.Id.to_string name)
  | Constr.Const _, _ when is_const_eq "CFML.Semantics.loc" c -> Loc
  | Constr.Const _, _ when is_const_eq "CFML.WPBuiltin.func" c -> Func
  | Constr.Const _, _ when is_const_eq "CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop" c -> Var "HPROP"
  | Constr.Rel i, Some f -> f i
  | _ ->
    Format.ksprintf ~f:failwith "found unhandled Coq term (%s)[%s] in %s that could not be converted to a type"
      (Proof_debug.constr_to_string c)
      (Proof_debug.tag c)
      (Proof_debug.constr_to_string_pretty c)

let extract_typ_opt ?rel c =
  try
    Some (extract_typ ?rel c)
  with
    Failure msg ->
    Format.printf "suppressing error %s@." msg;
    None

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

let is_type (c: Constr.t) = Constr.is_Type c

let extract_fun_typ  =
  let rec extract_foralls implicits pos acc c =
    match Constr.kind c with
    | Constr.Prod ({binder_name=Name name;_}, ty, rest) when is_type ty ->
      let acc = ((Names.Id.to_string name) :: acc) in
      extract_foralls implicits (pos + 1) acc rest
    | ity -> List.rev acc, c, pos in
  let rec extract_types implicits pos no_foralls foralls acc c =
    let rel id =
      Format.printf "looking up %d"  id;
      let id = id - pos in
      Format.printf "-> %d"  id;
      let ind = (no_foralls - id - 1) in
      Format.printf "-> %d@."  ind;
      Lang.Type.Var (List.nth foralls ind) in
    let acc ty =
      if IntSet.mem pos implicits
      then acc
      else ((extract_typ ~rel ty) :: acc) in
    match Constr.kind c with
    | Constr.Prod ({binder_name=Name _;_}, ty, rest) ->
      extract_types implicits (pos + 1) no_foralls foralls (acc ty) rest
    | _ -> List.rev (acc c) in
  fun name c ->
    let implicits = Proof_utils.get_implicits_for_fun name in
    let qf, c, pos = extract_foralls implicits 0 [] c in
    let c = extract_types implicits pos pos qf [] c in
    Lang.Type.Forall (qf,c)

let rec extract_expr ?rel (c: Constr.t) : Lang.Expr.t =
  match Constr.kind c, rel with
  | Constr.Rel ind, Some f -> `Var (f ind)
  | Constr.Var v, _ -> `Var (Names.Id.to_string v)
  | Constr.App (const, [|ty; h; tl|]), _ when is_constr_cons const ->
    `Constructor ("::", [extract_expr ?rel h; extract_expr ?rel tl])
  | Constr.App (const, [|ty|]), _ when is_constr_nil const ->
    `Constructor ("[]", [])
  | Constr.App (const, _), _ when is_constr_eq "Coq.Numbers.BinNums.Z" const ->
    extract_const_int c
  | Constr.App (const, args), _ when is_constr_eq "Coq.Init.Datatypes.prod" const ->
    let no_types = Array.length args / 2 in
    let args = Array.to_iter args
               |> Iter.drop no_types
               |> Iter.map (extract_expr ?rel)
               |> Iter.to_list in
    `Tuple (args)
  | Constr.App (fname, [| l; r |]), _ when is_const_eq "Coq.ZArith.BinInt.Z.sub" fname ->
    `App ("-", [extract_expr ?rel l; extract_expr ?rel r])    
  | Constr.App (fname, [| l; r |]), _ when is_const_eq "Coq.ZArith.BinInt.Z.add" fname ->
    `App ("+", [extract_expr ?rel l; extract_expr ?rel r])    
  | Constr.App (fname, [| l; r |]), _ when is_const_eq "Coq.ZArith.BinInt.Z.mul" fname ->
    `App ("*", [extract_expr ?rel l; extract_expr ?rel r])    
  | Constr.App (fname, args), _ when Constr.isConst fname ->
    let fname, _ = Constr.destConst fname in
    let args = Proof_utils.drop_implicits fname (Array.to_list args) |> List.map (extract_expr ?rel) in
    `App (Names.Constant.to_string fname, args)
  | _ ->
    Format.ksprintf ~f:failwith "found unhandled Coq term (%s)[%s] in %s that could not be converted to a expr"
      (Proof_debug.constr_to_string c) (Proof_debug.tag c) (Proof_debug.constr_to_string_pretty c)

let extract_env (t: Proof_context.t) =
  List.filter_map (fun (name, o_vl, vl) ->
    let name = (List.map Names.Id.to_string name |> String.concat ".") in
    begin match Constr.kind vl with
    | Constr.Sort _ -> Some (name, `Type) (* represents (A: Type) *)
    | Constr.App (fn, [| ty; l; r |]) when is_coq_eq fn -> None
    | Constr.Const _ when is_const_eq "CFML.Semantics.loc" vl ->
      Some (name, `Val Lang.Type.Loc)
    | Constr.Const _ when is_const_eq "CFML.WPBuiltin.func" vl ->
      Some (name, `Val Lang.Type.Func)
    | Constr.App (fn, _)
      when is_const_eq "CFML.WPLifted.Wpgen_body" fn
        || is_const_eq "CFML.WPLifted.Wpgen_negpat" fn ->
      None                    (* specifications *)
    | Constr.Ind ((ty_name, _), _) ->
      Some (name, `Val (Lang.Type.Var (Names.MutInd.to_string ty_name)))
    | Constr.Var _              (* init: A *)
    | Constr.App (_, _) ->
      Option.map (fun vl -> (name, `Val (vl))) (extract_typ_opt vl)
    (* list A, and eq, and others *) 
    | Constr.Const _
    | _ ->
      let c= vl in
      Format.ksprintf ~f:failwith "found unhandled Coq term (%s)[%s] in (%s: %s) that could not be converted to a binding"
        (Proof_debug.constr_to_string c) (Proof_debug.tag c) name (Proof_debug.constr_to_string_pretty c)
    end
  ) @@ List.rev (Proof_context.current_goal t).hyp
  |> List.partition_filter_map (function
    | (name, `Type) -> `Left name
    | (name, `Val ty) -> `Right (name, ty)
  )

let extract_assumptions t =
  List.filter_map (fun (name, o_vl, vl) ->
    let _name = (List.map Names.Id.to_string name |> String.concat ".") in
    begin match Constr.kind vl with
    | Constr.Sort _ -> None     (* represents (A: Type) *)
    | Constr.App (fn, [| ty; l; r |]) when is_coq_eq fn ->
      let ty = extract_typ ty in
      let l = extract_expr l in
      let r = extract_expr r in
      Some (ty, l, r)
    | Constr.App (fn, args) -> (* list A, and eq, and others *) None
    | Constr.Ind _              (* credits? *)
    | Constr.Var _              (* init: A *)
    | Constr.Const _ -> None
    | _ -> None
    end
  ) @@ List.rev (Proof_context.current_goal t).hyp

type constr = Constr.t
let pp_constr fmt vl = Format.pp_print_string fmt (Proof_debug.constr_to_string_pretty vl)
let show_preheap = [%show: [> `Empty | `NonEmpty of [> `Impure of constr | `Pure of constr ] list ]]

let extract_impure_heaplet (c: Constr.t) : Proof_spec.Heap.Heaplet.t =
  let check_or_fail name pred v = 
      if pred v then v
      else Format.ksprintf ~f:failwith "failed to find %s in heaplet %s" name (Proof_debug.constr_to_string c) in
  match Constr.kind c with
  | Constr.App (fname, [| ty; body; var |]) when is_const_eq "CFML.SepBase.SepBasicSetup.HS.repr" fname ->
    let var =
      check_or_fail "variable" Constr.isVar var
      |> Constr.destVar |> Names.Id.to_string in
    let _ty = extract_typ ty in
    let body = extract_expr body in
    PointsTo (var, body)
  | _ ->
    Format.ksprintf ~f:failwith "found unhandled Coq term (%s)[%s] in (%s) that could not be converted to a heaplet"
      (Proof_debug.constr_to_string c) (Proof_debug.tag c) (Proof_debug.constr_to_string_pretty c)  

let build_hole_var id = (`Var (Format.sprintf "S__hole_%d" id))

let unwrap_inductive_list (c: Constr.t) =
  let rec loop acc c = 
    match Constr.kind c with
    | Constr.App (const, [|ty; h; tl|]) when is_constr_cons const ->
      loop (h :: acc) tl
    | Constr.App (const, [|ty|]) when is_constr_nil const ->
      List.rev acc
    | _ ->
      Format.ksprintf ~f:failwith "found unhandled Coq term (%s)[%s] in (%s) that could not be converted to a list"
        (Proof_debug.constr_to_string c) (Proof_debug.tag c) (Proof_debug.constr_to_string_pretty c) in
  loop [] c

let extract_dyn_var (c: Constr.t) =
  match Constr.kind c with
  | Constr.App (const, [| ty; _enc; vl |]) when is_constr_eq "CFML.SepLifted.dyn" const ->
    (extract_expr vl, extract_typ ty)
  | _ ->
    Format.ksprintf ~f:failwith "found unhandled Coq term (%s)[%s] in (%s) that could not be converted to a dyn"
      (Proof_debug.constr_to_string c) (Proof_debug.tag c) (Proof_debug.constr_to_string_pretty c) 

(** [extract_app_full t c] when given a CFML goal with a letapp of a function
   application, extracts the function and the arguments.

    Example:

        - Goal:

    {[
      PRE (..)
      CODE (Wpgen_let_trm
            (`(Wpgen_app credits List_ml.fold_left
                 ((Dyn ftmp) :: (Dyn idx) :: (Dyn rest) :: nil)))
            (fun x2__ : credits =>
             `(Wpgen_match (`Case x2__ is p0__ {p0__} Then 
                               Val arr
                             Else
                               Done))))
      POST (..)
    ]}

    produces:

    {[ List_ml.fold_left, [`Var ftmp; `Var idx; `Var rest] ]}
    
*)
let extract_app_full (t: Proof_context.t) (c: Constr.t) =
  let check_or_fail name pred v = 
    if pred v then v
    else Format.ksprintf ~f:failwith "failed to find %s in goal %s" name (Proof_debug.constr_to_string c) in

  let unwrap_app_const name c =
    c
    |> check_or_fail "App" Constr.isApp 
    |> Constr.destApp
    |> check_or_fail name Fun.(is_const_eq name % fst) in

  let unwrap_wptag c =
    c
    |> unwrap_app_const "CFML.WPLifted.Wptag"
    |> Fun.(flip Array.get 0 % snd) in
    
  let app =
    c
    |> unwrap_wptag
    |> check_or_fail "App under wptag" Constr.isApp 
    |> Constr.destApp
    |> check_or_fail "wpgen let term" Fun.(is_const_eq "CFML.WPLifted.Wpgen_let_trm" % fst)
    |> Fun.(flip Array.get 0 % snd)
    |> unwrap_wptag
    |> unwrap_app_const "CFML.WPLifted.Wpgen_app"
    |> snd
    |> check_or_fail "wpgen_app args" Fun.((=) 4 % Array.length) in

  let fn_name = app.(2)
                |> check_or_fail "a function name" Constr.isConst
                |> Constr.destConst
                |> fst in
  let args =
    unwrap_inductive_list app.(3)
    |> List.map extract_dyn_var in
  (fn_name, args)

let is_unnamed_prod (c: Constr.t) =
      Constr.isProd c
      && Constr.destProd c |> (fun (name, _, _) -> name.binder_name)
         |> Names.Name.is_anonymous

let unwrap_invariant_type (c: Constr.t) =
  let rec loop acc c = 
  match Constr.kind c with
  | Constr.Prod (_, ty, rest) ->
    loop ((extract_typ ty) :: acc) rest
  | Constr.Const _ when is_const_eq "CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop" c ->
    List.rev acc
  | _ -> 
    Format.ksprintf ~f:failwith
      "found unhandled Coq term (%s)[%s] in (%s) which was expected to be a invariant type (_  -> .. -> hprop)"
      (Proof_debug.constr_to_string c) (Proof_debug.tag c) (Proof_debug.constr_to_string_pretty c)  in
  loop [] c

let unwrap_eq ?rel (c: Constr.t) =
  match Constr.kind c with
  | Constr.App (fname, [| ty; l; r |]) when is_ind_eq "Coq.Init.Logic.eq" fname ->
    let ty = extract_typ ty in
    let l = extract_expr ?rel l in
    let r = extract_expr ?rel r in
    (ty, l, r)
  | _ ->
    Format.ksprintf ~f:failwith
      "found unexpected Coq term (%s)[%s] ==> %s, when expecting an equality"
      (Proof_debug.constr_to_string c) (Proof_debug.tag c) (Proof_debug.constr_to_string_pretty c)
    

let unwrap_invariant_spec no_formals (c: Constr.t) =
  let rec collect_params acc c = 
        let rel ind =
          let ind = ind - 1 in
          let ind = ind - no_formals in
          snd (List.nth acc ind) in
        match Constr.kind c with
        | Constr.Prod ({binder_name=Name name; _}, ty, rest) ->
          collect_params ((Names.Id.to_string name, extract_typ ~rel ty) :: acc) rest
        | Constr.Prod (_, _, _) -> collect_assumptions acc [] c
        | _ -> 
          Format.ksprintf ~f:failwith
            "found unhandled Coq term (%s)[%s] in (%s) which was expected to be a invariant spec (forall ..., eqns, SPEC (_), _)"
            (Proof_debug.constr_to_string c) (Proof_debug.tag c) (Proof_debug.constr_to_string_pretty c)
  and collect_assumptions params acc c = 
        match Constr.kind c with
        | Constr.Prod (_, ty, rest) ->
          let rel ind =
            let ind = ind - 1 in
            let ind = ind - List.length acc in
            fst (List.nth params ind) in
          let assum = unwrap_eq ~rel ty in
          collect_assumptions params (assum :: acc) rest
        | Constr.App (fname, _) when is_const_eq "CFML.SepLifted.Triple" fname ->
          collect_spec params acc c
        | _ ->
          Format.ksprintf ~f:failwith
          "found unhandled Coq term (%s)[%s] in (%s) which was \
           expected to be a invariant spec. Expecting (eqns, SPEC (_), \
           _)" (Proof_debug.constr_to_string c) (Proof_debug.tag c) (Proof_debug.constr_to_string_pretty c)
  and collect_spec params assums c =
    match Constr.kind c with
    | Constr.App (fname, [| pre; _; _; f_app; post |]) when is_const_eq "CFML.SepLifted.Triple" fname ->
      Format.printf "%s@." (Proof_debug.constr_to_string_pretty c);
      failwith "here"
    | _ ->
      Format.ksprintf ~f:failwith
        "found unhandled Coq term (%s)[%s] in (%s) which was \
         expected to be a invariant spec. Expecting (SPEC (..) PRE (..) POST(..))"
        (Proof_debug.constr_to_string c)
        (Proof_debug.tag c)
        (Proof_debug.constr_to_string_pretty c) in
  collect_params [] c


let unwrap_instantiated_specification (t: Proof_context.t) (c: Constr.t) =
  let rec loop = function
    | `State1 acc -> fun c ->
      begin match Constr.kind c with
      | Constr.Prod ({binder_name=Name name;_}, ty, rest) when is_unnamed_prod ty ->
        loop (`State1 ((Names.Id.to_string name, unwrap_invariant_type ty) :: acc)) rest
      | Constr.Prod (_, ty, _) when not @@ is_unnamed_prod ty ->
        loop (`State2 (acc, [])) c
      | _ -> 
        Format.ksprintf ~f:failwith
          "found unhandled Coq term (%s)[%s] \
           in (%s) which was expected to be \
           a specification"
          (Proof_debug.constr_to_string c) (Proof_debug.tag c) (Proof_debug.constr_to_string_pretty c) 
      end
    | `State2 (formals, acc) -> fun c ->
      begin match Constr.kind c with
      | Constr.Prod (_, ty, rest) ->
        loop (`State2 (formals, (unwrap_invariant_spec (List.length acc) ty) :: acc)) rest
      | _ -> 
        Format.ksprintf ~f:failwith
          "found unhandled Coq term (%s)[%s] \
           in (%s) which was expected to be \
           a specification (expecting \
           specification invariants)"
          (Proof_debug.constr_to_string c) (Proof_debug.tag c) (Proof_debug.constr_to_string_pretty c) 
      end in
  loop (`State1 []) c


let build_verification_condition (t: Proof_context.t) (env: def_map) (spec: Names.Constant.t) : verification_condition =
  (* extract polymorphic variables and typing env *)
  let poly_vars, env = extract_env t in
  (* extract initial equalities in the context *)
  let assumptions = extract_assumptions t in
  (* extract CFML goal *)
  let (pre, post) = Proof_cfml.extract_cfml_goal (Proof_context.current_goal t).ty in
  (* from the pre condition, build a symbolic heap and a set of initial expressions *)
  let sym_heap, initial_values =
    let hole_count = ref 0 in
    List.filter_map
      (function `Impure heaplet -> Some (extract_impure_heaplet heaplet) | _ -> None)
      (match pre with | `Empty -> [] | `NonEmpty ls -> ls)
    |> List.map Proof_spec.Heap.Heaplet.(function
      | PointsTo (var, `App (fname, [arg])) ->
        let id = !hole_count in
        incr hole_count;
        PointsTo (var, `App (fname, [build_hole_var id])), arg
      | _ -> failwith "unsupported heaplet"
    )
    |> List.split in
  let initial_values = Array.of_list initial_values in
  (* extract the Coq-name for the function being called, and the arguments being passed to it *)
  let (fname, args) = extract_app_full t post in
  (* instantiate specification *)
  let instantiated_spec =
    Format.ksprintf "%s %s"
      (Names.Constant.to_string spec)
      (List.map (fun (vl,_) -> "(" ^ Printer.show_expr vl ^ ")") args
       |> String.concat " ")
      ~f:(Proof_context.typeof t) in

  let _ = unwrap_instantiated_specification t instantiated_spec in


  Format.printf "type of invariant instantiated is %s@." (Proof_debug.constr_to_string_pretty instantiated_spec);



  assert false
