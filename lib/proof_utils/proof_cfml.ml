open Containers

module IntSet = Set.Make(Int)

let is_const_named name const =
  Constr.isConst const &&
  String.(
    (fst @@ Constr.destConst const)
    |> Names.Constant.label
    |> Names.Label.to_string = name
  )
let is_hempty const = is_const_named "hempty" const
let is_hstar const = is_const_named "hstar" const
let is_hpure const = is_const_named "hpure" const
let is_wptag const = is_const_named "Wptag" const
let is_wp_gen_let_trm const = is_const_named "Wpgen_let_trm" const
let is_wp_gen_app const = is_const_named "Wpgen_app" const
let is_xlet_val_lemma const = is_const_named "xlet_val_lemma" const
let is_xmatch_lemma const = is_const_named "xmatch_lemma" const
let is_mkstruct_erase const = is_const_named "MkStruct_erase" const
let is_himpl_hand_r const = is_const_named "himpl_hand_r" const
let is_himpl_hexists_r const = is_const_named "himpl_hexists_r" const
let is_himpl_frame_r const = is_const_named "himpl_frame_r" const
let is_himpl_hempty_pure const = is_const_named "himpl_hempty_hpure" const
let is_xsimpl_start const = is_const_named "xsimpl_start" const
let is_himpl_hstar_hpure_l const = is_const_named "himpl_hstar_hpure_l" const
let is_himpl_trans const = is_const_named "himpl_trans" const
let is_hstars_simpl_start const = is_const_named "hstars_simpl_start" const
let is_hstars_simpl_cancel const = is_const_named "hstars_simpl_cancel" const
let is_hstars_simpl_pick_lemma const = is_const_named "hstars_simpl_pick_lemma" const
let is_himpl_refl const = is_const_named "himpl_refl" const
let is_xsimpl_lr_exit_nogc_nocredits const = is_const_named "xsimpl_lr_exit_nogc_nocredits" const
let is_xdone_lemma const = is_const_named "xdone_lemma" const
let is_xval_lemma const = is_const_named "xval_lemma" const
let is_himpl_hforall_r const = is_const_named "himpl_hforall_r" const
let is_xlet_trm_cont_lemma const = is_const_named "xlet_trm_cont_lemma" const
let is_xapp_lemma const = is_const_named "xapp_lemma" const
let is_xsimpl_lr_cancel_same const = is_const_named "xsimpl_lr_cancel_same" const
let is_xsimpl_lr_qwand const = is_const_named "xsimpl_lr_qwand" const
let is_xsimpl_lr_hgc_nocredits const = is_const_named "xsimpl_lr_hgc_nocredits" const
let is_xsimpl_lr_refl_nocredits const = is_const_named "xsimpl_lr_refl_nocredits" const

(** [extract_typ ?rel c] extracts a Type from a Coq term. [rel] if
    provided is a function that coq's de-brujin indices to a concrete
    type. *)
let rec extract_typ ?rel (c: Constr.t) : Lang.Type.t =
  match Constr.kind c, rel with
  | Constr.Ind ((name, _), univ), _ -> begin
      match Names.MutInd.to_string name with
      | "Coq.Numbers.BinNums.Z" -> Int
      | "CFML.Semantics.val" -> Val
      | "Coq.Init.Datatypes.nat" -> Int
      | _ -> Format.ksprintf ~f:failwith "found unknown type %s" (Names.MutInd.to_string name)
    end
  | Constr.App (fname, [|ty|]), _ when Utils.is_ind_eq "Coq.Init.Datatypes.list" fname -> 
    List (extract_typ ?rel ty)
  | Constr.App (fname, [|ty|]), _ when Utils.is_const_eq "CFML.WPBuiltin.array" fname -> 
    Array (extract_typ ?rel ty)
  | Constr.App (fname, args), _ when Utils.is_ind_eq "Coq.Init.Datatypes.prod" fname ->
    Product (Array.to_iter args |> Iter.map (extract_typ ?rel) |> Iter.to_list)
  | Constr.Var name, _ -> Var (Names.Id.to_string name)
  | Constr.Const _, _ when Utils.is_const_eq "CFML.Semantics.loc" c -> Loc
  | Constr.Const _, _ when Utils.is_const_eq "CFML.WPBuiltin.func" c -> Func
  | Constr.Const _, _ when Utils.is_const_eq "CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop" c ->
    Var "HPROP"
  | Constr.Rel i, Some f -> f i
  | _ ->
    Format.ksprintf ~f:failwith "found unhandled Coq term (%s)[%s] in %s that could not be converted to a type"
      (Proof_debug.constr_to_string c)
      (Proof_debug.tag c)
      (Proof_debug.constr_to_string_pretty c)

(** [extract_typ_opt ?rel c] is the same as [extract_typ], but returns
    None when the constructor can not be represented as an internal
    type. *)
let extract_typ_opt ?rel c =
  try
    Some (extract_typ ?rel c)
  with
    Failure msg ->
    None

(** [extract_fun_typ name c], given a function name [name] and Coq
    term [c] representing [name]'s type, returns an internal encoding
    of the function's type.  *)
let extract_fun_typ name c' =
  let rec extract_foralls implicits pos acc c =
    match Constr.kind c with
    | Constr.Prod ({binder_name=Name name;_}, ty, rest) when Constr.is_Type ty ->
      let acc = ((Names.Id.to_string name) :: acc) in
      extract_foralls implicits (pos + 1) acc rest
    | ity -> acc, c, pos in
  let rec extract_types implicits pos foralls acc c =
    let rel id =
      let id = pos - id in
      Lang.Type.Var (List.nth foralls id) in
    let acc ty =
      if IntSet.mem pos implicits
      then acc
      else ((extract_typ ~rel ty) :: acc) in
    match Constr.kind c with
    | Constr.Prod ({binder_name=Name _;_}, ty, rest) ->
      extract_types implicits (pos + 1) foralls (acc ty) rest
    | _ -> List.rev (acc c) in
  (* first, retrieve implicits - we will be ignoring them *)
  let implicits = Utils.get_implicits_for_fun name in
  (* extract forall quantified types *)
  let qf, c, pos = extract_foralls implicits 0 [] c' in
  (* extract remaining types *)
  let c = extract_types implicits pos qf [] c in
  Lang.Type.Forall (List.rev qf,c)

(** [extract_expr ?rel c] extracts an expression from a Coq term
    [c]. [rel] is a function that maps Coq's de-bruijin indices to the
    corresponding terms in the wider typing environment. *)
let rec extract_expr ?rel (c: Constr.t) : Lang.Expr.t =
  match Constr.kind c, rel with
  | Constr.Rel ind, Some f -> `Var (f ind)
  | Constr.Var v, _ -> `Var (Names.Id.to_string v)
  | Constr.App (value, [| c |]), _ when Utils.is_const_eq "CFML.Semantics.trms_vals" value ->
    extract_expr ?rel c
  | Constr.App (value, [| c |]), _ when Utils.is_const_eq "TLC.LibInt.nat_to_Z" value ->
    extract_expr ?rel c
  | Constr.App (value, [| c |]), _ when Utils.is_constr_eq "CFML.Semantics.val" value ->
    extract_expr ?rel c
  | Constr.App (const, [|ty; h; tl|]), _ when Utils.is_constr_cons const ->
    `Constructor ("::", [extract_expr ?rel h; extract_expr ?rel tl])
  | Constr.App (const, [|ty|]), _ when Utils.is_constr_nil const ->
    `Constructor ("[]", [])
  | Constr.Construct _, _ when Utils.is_constr_z0 c ->
    `Int 0
  | Constr.App (const, _), _ when Utils.is_constr_eq "Coq.Numbers.BinNums.Z" const ->
    `Int (Utils.extract_const_int c)
  | Constr.App (const, args), _ when Utils.is_constr_eq "Coq.Init.Datatypes.prod" const ->
    let no_types = Array.length args / 2 in
    let args = Array.to_iter args
               |> Iter.drop no_types
               |> Iter.map (extract_expr ?rel)
               |> Iter.to_list in
    `Tuple (args)
  | Constr.App (fname, [| l; r |]), _ when Utils.is_const_eq "Coq.Init.Nat.sub" fname ->
    `App ("-", [extract_expr ?rel l; extract_expr ?rel r])    
  | Constr.App (fname, [| l; r |]), _ when Utils.is_const_eq "Coq.ZArith.BinInt.Z.sub" fname ->
    `App ("-", [extract_expr ?rel l; extract_expr ?rel r])    
  | Constr.App (fname, [| l; r |]), _ when Utils.is_const_eq "Coq.Init.Nat.add" fname ->
    `App ("+", [extract_expr ?rel l; extract_expr ?rel r])    
  | Constr.App (fname, [| l; r |]), _ when Utils.is_const_eq "Coq.ZArith.BinInt.Z.add" fname ->
    `App ("+", [extract_expr ?rel l; extract_expr ?rel r])    
  | Constr.App (fname, [| l; r |]), _ when Utils.is_const_eq "Coq.ZArith.BinInt.Z.mul" fname ->
    `App ("*", [extract_expr ?rel l; extract_expr ?rel r])    
  | Constr.App (fname, args), _ when Constr.isConst fname ->
    let fname, _ = Constr.destConst fname in
    let args = Utils.drop_implicits fname (Array.to_list args) |> List.map (extract_expr ?rel) in
    `App (Names.Constant.to_string fname, args)
  | Constr.App (fname, args), _ when Constr.isVar fname ->
    let fname = Constr.destVar fname |> Names.Id.to_string in
    let args = List.map (extract_expr ?rel) (Array.to_list args) in
    `App (fname, args)
  | _ ->
    Format.ksprintf ~f:failwith "found unhandled Coq term (%s)[%s] in %s that could not be converted to a expr"
      (Proof_debug.constr_to_string c) (Proof_debug.tag c) (Proof_debug.constr_to_string_pretty c)

(** [extract_cfml_goal goal] when given an intermediate CFML [goal],
    extracts the pre and post condition.  *)
let extract_cfml_goal goal =
  let[@warning "-8"] himpl, [pre; post] = Constr.decompose_app goal in
  assert begin
    String.equal
      "himpl"
      (fst (Constr.destConst himpl)
       |> Names.Constant.label
       |> Names.Label.to_string)
  end;
  let destruct_heap pre =
    let rec loop acc pre =
      match Constr.kind pre with
      | Constr.Const (_, _) when is_hempty pre -> acc
      | Constr.App (fname, [|heaplet; rest|]) when is_hstar fname ->
        begin match Constr.kind heaplet with
        | Constr.App (fname, _) when is_hpure fname ->
          loop (`Pure heaplet :: acc) rest             
        | _ ->
          loop (`Impure heaplet :: acc) rest 
        end
      | _ ->
        (`Impure pre :: acc) in
    loop [] pre in
  let pre =
    match Constr.kind pre with
    | Constr.Const (_, _) when is_hempty pre -> `Empty
    | Constr.App (fname, _) when is_hstar fname ->
      begin match destruct_heap pre with
      | heap -> `NonEmpty heap
      | exception _ -> failwith ("unexpected pre-heap structure: " ^ (Proof_debug.constr_to_string pre))
      end
    | Constr.App (fname, _) when is_hpure fname ->
      `NonEmpty ([`Pure pre])
    | _ -> `NonEmpty ([`Impure pre])
  in
  (pre, post)

(** [extract_xapp_fun c] given a coq term [c] representing a reified
    CFML encoding of an OCaml program with a let of a function as the
    next statement, extracts the function being calle'ds arguments *)
let extract_x_app_fun pre =
  let extract_app_enforce name f n pre =
    match Constr.kind pre with
    | Constr.App (fname, args) when f fname ->
      args.(n)
    | _ ->
      Format.eprintf "failed because unknown structure for %s: %s\n" name (Proof_debug.constr_to_string pre);
      failwith "" in
  try
    pre
    |> extract_app_enforce "wptag" is_wptag 0
    |> extract_app_enforce "xlet" is_wp_gen_let_trm 0
    |> extract_app_enforce "wptag" is_wptag 0
    |> extract_app_enforce "xapp" is_wp_gen_app 2
    |> Constr.destConst
    |> fst
  with
    Failure _ -> failwith ("extract_f_app failed because unsupported context: " ^ (Proof_debug.constr_to_string pre))

(** [extract spec c] given a Coq term [c] representing a CFML
    specification, returns a triple of the parameters (named
    arguments), invariants (assumptions) and the body (assertion).

    Note: assumes that a CFML spec is of the form of a sequence of
    named arguments, followed by a sequence of unnamed parameters and
    finally a non-product body. *)
let extract_spec pre =
  let extract_spec pre =
    let rec loop acc pre = 
      if Constr.isProd pre
      then
        let ({Context.binder_name; _}, ty, pre)  = Constr.destProd pre in
        loop ((binder_name, ty) :: acc) pre
      else List.rev acc, pre in
    loop [] pre in
  let rec split acc ls =
    match ls with
    | [] -> (List.rev acc,[])
    | ((name, _) as h) :: t when Names.Name.is_anonymous name ->
      (List.rev acc, h::t)
    | h :: t -> split (h :: acc) t in
  let params, body = extract_spec pre in
  let params, invariants = split [] params in
  (params, invariants, body)

(** [extract_dyn_var ?rel c] given a Coq term [c] of the form {[Dyn v]}, extracts the corresponding expression and type.  *)
let extract_dyn_var ?rel (c: Constr.t) =
  match Constr.kind c with
  | Constr.App (const, [| ty; _enc; vl |]) when Utils.is_constr_eq "CFML.SepLifted.dyn" const ->
    (extract_expr ?rel vl, extract_typ ty)
  | _ ->
    Format.ksprintf ~f:failwith "found unhandled Coq term (%s)[%s] in (%s) that could not be converted to a dyn"
      (Proof_debug.constr_to_string c) (Proof_debug.tag c) (Proof_debug.constr_to_string_pretty c)

(** [extract_env ctx] given a Coq context [ctx] extracts the typing
    env of the current proof goal.  *)
let extract_env hyp =
  List.filter_map (fun (name, o_vl, vl) ->
    let name = (List.map Names.Id.to_string name |> String.concat ".") in
    begin match Constr.kind vl with
    | Constr.Sort _ -> Some (name, `Type) (* represents (A: Type) *)
    | Constr.App (fn, [| ty; l; r |]) when Utils.is_coq_eq fn -> None
    | Constr.Ind _ when Utils.is_ind_eq "CFML.Semantics.val" vl ->
      Some (name, `Val Lang.Type.Val)
    | Constr.Const _ when Utils.is_const_eq "CFML.Semantics.loc" vl ->
      Some (name, `Val Lang.Type.Loc)
    | Constr.Const _ when Utils.is_const_eq "CFML.WPBuiltin.func" vl ->
      Some (name, `Val Lang.Type.Func)
    | Constr.App (fn, _)
      when Utils.is_const_eq "CFML.WPLifted.Wpgen_body" fn
        || Utils.is_const_eq "CFML.WPLifted.Wpgen_negpat" fn ->
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
  ) @@ List.rev hyp
  |> List.partition_filter_map (function
    | (name, `Type) -> `Left name
    | (name, `Val ty) -> `Right (name, ty)
  )

(** [extract assumptions ctx] given a Coq context [ctx] extracts the
    list of assumptions (equalities) in the current proof goal. *)
let extract_assumptions hyp =
  List.filter_map (fun (name, o_vl, vl) ->
    let _name = (List.map Names.Id.to_string name |> String.concat ".") in
    begin match Constr.kind vl with
    | Constr.Sort _ -> None     (* represents (A: Type) *)
    | Constr.App (fn, [| ty; l; r |]) when Utils.is_coq_eq fn ->
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
  ) @@ List.rev hyp


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
let extract_app_full (c: Constr.t) =
  let check_or_fail name pred v = 
    if pred v then v
    else Format.ksprintf ~f:failwith "failed to find %s in goal %s" name (Proof_debug.constr_to_string c) in

  let unwrap_app_const name c =
    c
    |> check_or_fail "App" Constr.isApp 
    |> Constr.destApp
    |> check_or_fail name Fun.(Utils.is_const_eq name % fst) in

  let unwrap_wptag c =
    c
    |> unwrap_app_const "CFML.WPLifted.Wptag"
    |> Fun.(flip Array.get 0 % snd) in

  let app =
    c
    |> unwrap_wptag
    |> check_or_fail "App under wptag" Constr.isApp 
    |> Constr.destApp
    |> check_or_fail "wpgen let term" Fun.(Utils.is_const_eq "CFML.WPLifted.Wpgen_let_trm" % fst)
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
    Utils.unwrap_inductive_list app.(3)
    |> List.map extract_dyn_var in
  (fn_name, args)

(** [unwrap_invariant_type c] when given a Coq term [c] representing
    the type signature of an invariant (e.g. {[I: int -> List A ->
      hprop]}), extracts a list of the types of the arguments of the invariant.  *)
let unwrap_invariant_type ?rel (c: Constr.t) =
  let rel acc = match rel with
      None -> None
    | Some rel -> Some (fun i ->
      let i = i - 1 in
      let acc_len = List.length acc in
      if i < acc_len
      then List.nth acc i
      else rel (i - acc_len + 1)) in
  let rec loop acc c = 
    match Constr.kind c with
    | Constr.Prod (_, ty, rest) ->
      loop ((extract_typ ?rel:(rel acc) ty) :: acc) rest
    | Constr.Const _ when Utils.is_const_eq "CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop" c ->
      List.rev acc
    | _ -> 
      Format.ksprintf ~f:failwith
        "found unhandled Coq term (%s)[%s] in (%s) which was expected to be a invariant type (_  -> .. -> hprop)"
        (Proof_debug.constr_to_string c) (Proof_debug.tag c) (Proof_debug.constr_to_string_pretty c)  in
  loop [] c

(** [unwrap_eq ?rel c] when given a Coq term [c] representing an
    propositional equality, extracts the left and right hand sides of
    the equality. *)
let unwrap_eq ?rel (c: Constr.t) =
  match Constr.kind c with
  | Constr.App (fname, [| ty; l; r |]) when Utils.is_ind_eq "Coq.Init.Logic.eq" fname ->
    let ty = extract_typ ty in
    let l = extract_expr ?rel l in
    let r = extract_expr ?rel r in
    (ty, l, r)
  | _ ->
    Format.ksprintf ~f:failwith
      "found unexpected Coq term (%s)[%s] ==> %s, when expecting an equality"
      (Proof_debug.constr_to_string c) (Proof_debug.tag c) (Proof_debug.constr_to_string_pretty c)

(** [extract_embedded_expr ?rel c] extracts a deeply embedded CFML
   expression from a Coq term [c]. [rel] is a function that maps Coq's
   de-bruijin indices to the corresponding terms in the wider typing
   environment. *)
let rec extract_embedded_expr ?rel (c: Constr.t) : Lang.Expr.t =
  match Constr.kind c, rel with
  | Constr.App (fn, [| f |]), _ when Utils.is_const_eq "CFML.WPLifted.Wptag" fn ->
    extract_embedded_expr ?rel f
  | Constr.App (fn, [| ty; enc_ty; f; args |]), _ when Utils.is_const_eq "CFML.WPLifted.Wpgen_app" fn ->
    let fn = extract_expr ?rel f |> function `Var v -> v | _ -> failwith "found application to non-constant function" in
    let args = 
      Utils.unwrap_inductive_list args
      |> List.map (extract_dyn_var ?rel) in
    `App (fn, List.map fst args)
  | _ ->
    Format.ksprintf ~f:failwith "found unhandled embedded Coq term (%s)[%s] in %s that could not be converted to a expr"
      (Proof_debug.constr_to_string c) (Proof_debug.tag c) (Proof_debug.constr_to_string_pretty c)


(** [extract_impure_heaplet c] when given a Coq term representing a
    CFML heaplet, extracts an internal representation of the heaplet. *)
let extract_impure_heaplet (c: Constr.t) : Proof_spec.Heap.Heaplet.t =
  let check_or_fail name pred v = 
    if pred v then v
    else Format.ksprintf ~f:failwith "failed to find %s in heaplet %s" name (Proof_debug.constr_to_string c) in
  match Constr.kind c with
  | Constr.App (fname, [| ty; body; var |]) when
      Utils.is_const_eq "CFML.SepBase.SepBasicSetup.HS.repr" fname ->
    let var =
      check_or_fail "variable" Constr.isVar var
      |> Constr.destVar |> Names.Id.to_string in
    let ty = extract_typ ty in
    let body = extract_expr body in
    PointsTo (var, Some ty, body)
  | _ ->
    Format.ksprintf ~f:failwith "found unhandled Coq term (%s)[%s] in (%s) that could not be converted to a heaplet"
      (Proof_debug.constr_to_string c) (Proof_debug.tag c) (Proof_debug.constr_to_string_pretty c)