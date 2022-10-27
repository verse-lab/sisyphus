open Containers

module Log = (val Logs.src_log (Logs.Src.create ~doc:"Utilities for working with proofs" "pr.utils.debug"))

module IntSet = Set.Make(Int)
module StringSet = Set.Make(String)

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
let is_xlet_fun_lemma const = is_const_named "xlet_fun_lemma" const
let is_xlet_val_lemma const = is_const_named "xlet_val_lemma" const
let is_xlet_trm_cont_lemma const = is_const_named "xlet_trm_cont_lemma" const
let is_xseq_cont_lemma const = is_const_named "xseq_cont_lemma" const
let is_xchange_lemma const = is_const_named "xchange_lemma" const
let is_xmatch_lemma const = is_const_named "xmatch_lemma" const
let is_xapp_lemma const = is_const_named "xapp_lemma" const
let is_xapps_lemma const = is_const_named "xapps_lemma" const
let is_xapp_record_Get const = is_const_named "xapp_record_Get" const
let is_xapp_record_Set const = is_const_named "xapp_record_Set" const
let is_xval_lemma const = is_const_named "xval_lemma" const
let is_xval'_lemma const = is_const_named "xval'_lemma" const
let is_xifval_lemma const = is_const_named "xifval_lemma" const
let is_xifval_lemma_isTrue const = is_const_named "xifval_lemma_isTrue" const
let is_xdone_lemma const = is_const_named "xdone_lemma" const
let is_mkstruct_erase const = is_const_named "MkStruct_erase" const
let is_himpl const = is_const_named "himpl" const
let is_himpl_hand_r const = is_const_named "himpl_hand_r" const
let is_himpl_hexists_r const = is_const_named "himpl_hexists_r" const
let is_himpl_hexists_l const = is_const_named "himpl_hexists_l" const
let is_hstars_simpl_keep const = is_const_named "hstars_simpl_keep" const
let is_himpl_frame_r const = is_const_named "himpl_frame_r" const
let is_himpl_hempty_pure const = is_const_named "himpl_hempty_hpure" const
let is_xsimpl_start const = is_const_named "xsimpl_start" const
let is_xsimpl_pick_lemma const = is_const_named "xsimpl_pick_lemma" const
let is_himpl_hstar_hpure_l const = is_const_named "himpl_hstar_hpure_l" const
let is_himpl_trans const = is_const_named "himpl_trans" const
let is_hstars_simpl_start const = is_const_named "hstars_simpl_start" const
let is_hstars_simpl_cancel const = is_const_named "hstars_simpl_cancel" const
let is_hstars_simpl_pick_lemma const = is_const_named "hstars_simpl_pick_lemma" const
let is_himpl_refl const = is_const_named "himpl_refl" const
let is_himpl_of_eq const = is_const_named "himpl_of_eq" const
let is_xsimpl_lr_exit_nogc_nocredits const = is_const_named "xsimpl_lr_exit_nogc_nocredits" const
let is_xsimpl_lr_exit_nocredits const = is_const_named "xsimpl_lr_exit_nocredits" const
let is_himpl_hforall_r const = is_const_named "himpl_hforall_r" const
let is_hwand_hpure_r_intro const = is_const_named "hwand_hpure_r_intro" const
let is_xpull_protect const = is_const_named "xpull_protect" const
let is_xsimpl_l_acc_other const = is_const_named "xsimpl_l_acc_other" const
let is_xsimpl_lr_cancel_same const = is_const_named "xsimpl_lr_cancel_same" const
let is_xsimpl_r_keep const = is_const_named "xsimpl_r_keep" const
let is_xsimpl_lr_qwand const = is_const_named "xsimpl_lr_qwand" const
let is_xsimpl_lr_hwand const = is_const_named "xsimpl_lr_hwand" const
let is_xsimpl_flip_acc_l const = is_const_named "xsimpl_flip_acc_l" const
let is_xsimpl_flip_acc_r const = is_const_named "xsimpl_flip_acc_r" const
let is_xsimpl_r_hgc_or_htop const = is_const_named "xsimpl_r_hgc_or_htop" const
let is_xsimpl_lr_qwand_unit const = is_const_named "xsimpl_lr_qwand_unit" const
let is_xsimpl_lr_hgc_nocredits const = is_const_named "xsimpl_lr_hgc_nocredits" const
let is_xsimpl_lr_refl_nocredits const = is_const_named "xsimpl_lr_refl_nocredits" const
let is_infix_colon_eq_spec const = is_const_named "infix_colon_eq_spec" const

let to_cfml_ocaml_type s =
  let elts = String.split_on_char '.' s in
  match List.rev elts with
  | ty_name :: modl :: _
    when String.suffix ~suf:"_" ty_name && String.suffix ~suf:"_ml" modl ->
    let modl = String.take (String.length modl - 3) modl in
    let ty_name = String.take (String.length ty_name - 1) ty_name in
    if String.equal modl "Pervasives"
    then Some (None, ty_name)
    else Some (Some modl, ty_name)
  | _ -> None

let unwrap_cfml_ocaml_type c = begin match Constr.kind_nocast c with
  | Constr.Const (cst, _) ->
    let label = Names.Constant.to_string cst in
    to_cfml_ocaml_type label
  | Constr.Ind ((ind, _), _) ->
    let label = Names.MutInd.to_string ind in
    to_cfml_ocaml_type label
  | _ -> None
end |> Option.map (function (None, ty) -> ty | (Some modl, ty) -> (modl ^ "." ^ ty))

(** [is_cfml_custom_user_lemma] determines whether a given Coq term is
    a custom user lemma used in folding and unfolding. *)
let is_cfml_custom_user_lemma trm =
  Constr.isConst trm && begin
    let (cst, _) = Constr.destConst trm in
    Names.Constant.to_string cst |> String.prefix ~pre:"Common."
  end

let unwrap_cfml_ocaml_constructor c =
  match Constr.kind_nocast c with
  | Constr.Construct (((cst, _), _), _) ->
    let label = Names.MutInd.to_string cst in
    to_cfml_ocaml_type label
  | _ -> None

(** [extract_typ ?rel c] extracts a Type from a Coq term. [rel] if
    provided is a function that coq's de-brujin indices to a concrete
    type. *)
let rec extract_typ ?rel (c: Constr.t) : Lang.Type.t =
  match Constr.kind c, rel with
  | Constr.Ind ((name, _), univ), _ -> begin
      match Names.MutInd.to_string name with
      | "Coq.Numbers.BinNums.Z" -> Int
      | "CFML.Semantics.val" -> Val
      | "Coq.Init.Datatypes.bool" -> Bool
      | "Coq.Init.Datatypes.nat" -> Int
      | "Coq.Init.Datatypes.unit" -> Unit
      | _ -> Format.ksprintf ~f:failwith "found unknown type %s" (Names.MutInd.to_string name)
    end
  | Constr.App (fname, [|ty|]), _ when Utils.is_ind_eq "Coq.Init.Datatypes.list" fname -> 
    List (extract_typ ?rel ty)
  | Constr.App (fname, [|ty|]), _ when Utils.is_const_eq "CFML.WPBuiltin.array" fname -> 
    Array (extract_typ ?rel ty)
  | Constr.App (fname, [| ty |]), _ when  Utils.is_const_eq "CFML.Stdlib.Pervasives_ml.ref_" fname ->
    Ref (extract_typ ?rel ty)
  | Constr.App (fname, args), _ when Utils.is_ind_eq "Coq.Init.Datatypes.prod" fname ->
    Product (Array.to_iter args |> Iter.map (extract_typ ?rel) |> Iter.to_list)
  | Constr.App (fname, [| ty |]), _ when Utils.is_ind_eq "Coq.Init.Datatypes.option" fname ->
    ADT ("option", [extract_typ ?rel ty], None)
  | Constr.Var name, _ when String.equal "Coq.Numbers.BinNums.Z" (Names.Id.to_string name) -> Int
  | Constr.Var name, _ -> Var (Names.Id.to_string name)
  | Constr.Const _, _ when Utils.is_const_eq "CFML.Semantics.loc" c -> Loc
  | Constr.Const _, _ when Utils.is_const_eq "CFML.WPBuiltin.func" c -> Func None
  | Constr.Const _, _ when Utils.is_const_eq "CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop" c ->
    Var "HPROP"
  | Constr.Rel i, Some f -> f i
  | Constr.Prod (_, _, _), _ ->
    let rec loop acc t =
      let rel = match rel with None -> None | Some f -> Some (fun ind -> f (ind - List.length acc))in
      match Constr.kind t with
      | Constr.Prod (_, arg, rest) ->
        let arg = extract_typ ?rel arg in
        loop (arg :: acc) rest
      | _ ->
        let res = extract_typ ?rel t in
        Lang.Type.Func (Some (List.rev acc, res)) in
    loop [] c
  (* Proof irrelevance? pfftt... not on my watch:  *)
  | Constr.Sort Prop, _ -> Lang.Type.Bool
  | Constr.App (fname, [| ty |]), _ when Utils.is_const_eq "Common.Verify_sll.sll" fname ||
                                         Utils.is_const_eq "Common.Sll_ml.sll_" fname ||
                                         Utils.is_const_eq "Common.Verify_stack.stack" fname ||
                                         Utils.is_const_eq "Common.Verify_queue.queue" fname ->
    let fname, _ = Constr.destConst fname in
    let fname = Names.Label.to_string (Names.Constant.label fname) in
    let fname = if String.suffix ~suf:"_" fname then String.sub fname 0 (String.length fname - 1) else fname in
    ADT (fname, [extract_typ ?rel ty], None)
  | Constr.App (fname, [| ty |]), _ when Option.is_some (unwrap_cfml_ocaml_type fname) ->
    let fname = unwrap_cfml_ocaml_type fname |> Option.get_exn_or "invalid assumptions" in
    ADT (fname, [extract_typ ?rel ty], None)
  | _ ->
    Format.ksprintf ~f:failwith "found unhandled Coq term (%s)[%s] in %s that could not be converted to a type"
      (Proof_debug.constr_to_string c)
      (Proof_debug.tag c)
      (Proof_debug.constr_to_string_pretty c)

(** [is_invariant_ty ty] checks that [ty] is a arrow type that returns
    HPROP. Raises an exception if the input constructor is not of the
    correct form to be an argument to a loop spec. *)
let is_invariant_ty ty =
  let rec loop ity =
    match Constr.kind_nocast ity with
    | Constr.Const _ when Utils.is_const_eq "CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop" ity -> true
    | Constr.Const _
    | Constr.Rel _
    | Constr.Var _
    | Constr.Ind _
    | Constr.App (_, _) -> false
    | Constr.Prod ({ Context.binder_name=Names.Name.Anonymous; _ }, _, rest) -> loop rest
    | _ ->
      Format.ksprintf ~f:failwith "found unexpected form of argument type [%s] to function. %s in %s"
        (Proof_debug.tag ity)
        (Proof_debug.constr_to_string_pretty ity)
        (Proof_debug.constr_to_string_pretty ty) in
  loop ty

(** [extract_typ_opt ?rel c] is the same as [extract_typ], but returns
    None when the constructor can not be represented as an internal
    type. *)
let extract_typ_opt ?rel c =
  try
    Some (extract_typ ?rel c)
  with
    Failure msg ->
    None

(** [extract_fun_typ ?name c], given a function name [name] and Coq
    term [c] representing [name]'s type, returns an internal encoding
    of the function's type.  *)
let extract_fun_typ ?name c' =
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
  let implicits =
    match name with
    | None -> IntSet.empty
    | Some name -> Utils.get_implicits_for_fun name in
  (* extract forall quantified types *)
  let qf, c, pos = extract_foralls implicits 0 [] c' in
  (* extract remaining types *)
  let c = extract_types implicits pos qf [] c in
  Lang.Type.Forall (List.rev qf,c)

(** [extract_expr ?env ?rel c] extracts an expression from a Coq term
    [c]. [rel] is a function that maps Coq's de-bruijin indices to the
    corresponding terms in the wider typing environment. *)
let rec extract_expr ?env ?rel (c: Constr.t) : Lang.Expr.t =
  match Constr.kind c, rel with
  | Constr.Cast (c, _, _), _ -> extract_expr ?env ?rel c
  | Constr.Rel ind, Some f -> `Var (f ind)
  | Constr.Var v, _ -> `Var (Names.Id.to_string v)
  | Constr.App (value, [| c |]), _ when Utils.is_const_eq "TLC.LibReflect.istrue" value
                                     || Utils.is_const_eq "TLC.LibReflect.isTrue" value ->
    extract_expr ?env ?rel c
  | Constr.App (value, [| c |]), _ when Utils.is_const_eq "CFML.Semantics.trms_vals" value ->
    extract_expr ?env ?rel c
  | Constr.App (value, [| c |]), _ when Utils.is_const_eq "TLC.LibInt.nat_to_Z" value ->
    extract_expr ?env ?rel c
  | Constr.App (value, [| c |]), _ when Utils.is_constr_eq "CFML.Semantics.val" value ->
    extract_expr ?env ?rel c

  (* boolean *)
  | Constr.App (trm, [| l; r |]), _ when Utils.is_ind_eq "Coq.Init.Logic.and" trm ->
    `App ("&&", [extract_expr ?env ?rel l; extract_expr ?env ?rel r])
  | Constr.App (trm, [| l; r |]), _ when Utils.is_const_eq "Coq.Init.Datatypes.implb" trm ->
    `App ("||", [`App ("not",  [extract_expr ?env ?rel l]); extract_expr ?env ?rel r])

  | Constr.Construct _ , _ when Utils.is_constr_bool_true c ->
    `Constructor ("true", [ ])
  | Constr.Construct _ , _ when Utils.is_constr_bool_false c ->
    `Constructor ("false", [ ])

  (* lists *)
  | Constr.App (const, [|ty; h; tl|]), _ when Utils.is_constr_cons const ->
    `Constructor ("::", [extract_expr ?env ?rel h; extract_expr ?env ?rel tl])
  | Constr.App (const, [|ty|]), _ when Utils.is_constr_nil const ->
    `Constructor ("[]", [])
  (* Hey, idiot! Yes. You. If you're adding things here to make
     extraction work, DONT. Instead add it to [normalize] in
     proof_extraction.ml See below for the graveyard of useless work
     that some idiot (you) did in the past.  *)

  (* | Constr.App (const, [| _int; _ty; _ls_ty; _read_inst; ls; int |]), _ when Utils.is_const_eq "TLC.LibContainer.read" const ->
   *   `App ("List.nth", [extract_expr ?rel ls; extract_expr ?rel int]) *)
  (* | Constr.App (const, [| ty; ls |]), _ when Utils.is_const_eq "TLC.LibListZ.length" const ->
   *   `App ("List.length", []) *)

  (* unit *)
  | Constr.Construct _, _ when Utils.is_constr_unit c ->
    `Constructor ("()", [])

  (* option *)
  | Constr.App (const, [|ty|]), _ when Utils.is_constr_option_none const ->
    `Constructor ("None", [])
  | Constr.App (const, [|ty; vl|]), _ when Utils.is_constr_option_some const ->
    `Constructor ("Some", [extract_expr ?env ?rel vl])

  (* equality *)
  | Constr.App (const, [| l; r |]), _ when Utils.is_const_eq "Coq.ZArith.BinInt.Z.eqb" const ->
    let l = extract_expr ?env ?rel l in
    let r = extract_expr ?env ?rel r in
    `App ("=", [l;r])
  | Constr.App (const, [|_ty; l; r|]), _ when Utils.is_coq_eq const ->
    let l = extract_expr ?rel l in
    let r = extract_expr ?rel r in
    `App ("=", [l;r])

  (* ints *)
  | Constr.Construct _, _ when Utils.is_constr_z0 c ->
    `Int 0
  | Constr.App (const, _), _ when Utils.is_constr_eq "Coq.Numbers.BinNums.Z" const ->
    `Int (Utils.extract_const_int c)
  | Constr.App (const, args), _ when Utils.is_constr_eq "Coq.Init.Datatypes.prod" const ->
    let no_types = Array.length args / 2 in
    let args = Array.to_iter args
               |> Iter.drop no_types
               |> Iter.map (extract_expr ?env ?rel)
               |> Iter.to_list in
    `Tuple (args)

  (* arithmetic *)
  | Constr.App (fname, [| _; _; l; r |]), _ when Utils.is_const_eq "TLC.LibOrder.lt" fname ->
    `App ("<", [extract_expr ?env ?rel l; extract_expr ?env ?rel r])        
  | Constr.App (fname, [| _; _; l; r |]), _ when Utils.is_const_eq "TLC.LibOrder.le" fname ->
    `App ("<=", [extract_expr ?env ?rel l; extract_expr ?env ?rel r])        
  | Constr.App (fname, [| l; r |]), _ when Utils.is_const_eq "Coq.Init.Nat.sub" fname ->
    `App ("-", [extract_expr ?env ?rel l; extract_expr ?env ?rel r])    
  | Constr.App (fname, [| l; r |]), _ when Utils.is_const_eq "Coq.ZArith.BinInt.Z.sub" fname ->
    `App ("-", [extract_expr ?env ?rel l; extract_expr ?env ?rel r])    
  | Constr.App (fname, [| l; r |]), _ when Utils.is_const_eq "Coq.Init.Nat.add" fname ->
    `App ("+", [extract_expr ?env ?rel l; extract_expr ?env ?rel r])    
  | Constr.App (fname, [| l; r |]), _ when Utils.is_const_eq "Coq.ZArith.BinInt.Z.add" fname ->
    `App ("+", [extract_expr ?env ?rel l; extract_expr ?env ?rel r])    
  | Constr.App (fname, [| l; r |]), _ when Utils.is_const_eq "Coq.ZArith.BinInt.Z.mul" fname ->
    `App ("*", [extract_expr ?env ?rel l; extract_expr ?env ?rel r])    

  | Constr.App (fname, args), _ when Constr.isConst fname ->
    let fname, _ = Constr.destConst fname in
    let args = Utils.drop_implicits fname (Array.to_list args) |> List.map (extract_expr ?env ?rel) in
    `App (Names.Constant.to_string fname, args)

  | Constr.App (fname, args), _ when Constr.isVar fname ->
    let fname = Constr.destVar fname |> Names.Id.to_string in
    let args = List.map (extract_expr ?env ?rel) (Array.to_list args) in
    `App (fname, args)
  | Constr.Const (c, _), _ when not @@ String.equal (Names.Constant.to_string c) "CFML.Semantics.loc" ->
    `Var (Names.Constant.to_string c)
  | Constr.App (fname, args), _ when Option.is_some (unwrap_cfml_ocaml_constructor fname) && Option.is_some env ->
    let ((id, _), constructor_ind), _ = Constr.destConstruct fname in
    let modl_name, _ = unwrap_cfml_ocaml_constructor fname |> Option.get_exn_or "invalid assumptions" in
    let fname =
      let inductive_type = Environ.lookup_mind id (Option.get_exn_or "invalid assumptions" env) in
      let inductive_name = inductive_type.mind_packets.(0).mind_consnames.(constructor_ind - 1) in
      Names.Id.to_string inductive_name in
    let fname = match modl_name with None -> fname | Some modl -> modl ^ "." ^ fname in
    let args = Array.to_list args |> List.drop 1 |> List.map (extract_expr ?env ?rel) in
    `Constructor (fname, args)
  | Constr.Lambda (_, _, _), _ -> extract_and_eta_expand_lambda ?env ?rel c
  | _ ->
    Format.ksprintf ~f:failwith "found unhandled Coq term (%s)[%s] in %s that could not be converted to a expr"
      (Proof_debug.constr_to_string c) (Proof_debug.tag c) (Proof_debug.constr_to_string_pretty c)
(** [extract_and_eta_expand_lambda ?env ?rel c] when given a coq term
   [c] of the form [fun (x: 'a) => istrue (f x)] returns the
   expression obtained by extracting [f] (i.e performs the eta
   expansion and then extracts f). This function is required because
   sometimes the coq context contains lambdas that we don't support in
   general, but can support after eta-expansion. *)
and extract_and_eta_expand_lambda ?env ?rel c =
  let failwith fmt = Format.ksprintf ~f:failwith fmt in
  let asserts cond = if not cond then failwith "unexpected form for lambda %s" (Proof_debug.constr_to_string_pretty c) in
  asserts (Constr.isLambda c);
  let binder, ty, body = Constr.destLambda c in
  asserts (Constr.isApp body);
  let (is_true, is_true_args) = Constr.destApp body in
  asserts (Utils.is_const_eq "TLC.LibReflect.istrue" is_true && Array.length is_true_args = 1);
  let is_true_arg = is_true_args.(0) in
  asserts (Constr.isApp is_true_arg);
  let (applied_fun, applied_args) = Constr.destApp is_true_arg in
  asserts (Array.length applied_args = 1);
  let rel = match rel with
    | None -> None              (* update rel to account for the binding  *)
    | Some f -> Some (fun ind -> f (ind - 1)) in
  extract_expr ?env ?rel applied_fun


(** [extract_heap c] when given a coq term [c] representing a heap,
    returns a list of its constituent heaplets. *)
let extract_heap c =
  let destruct_heap pre =
    let rec loop acc pre =
      match Constr.kind pre with
      | Constr.Const (_, _) when is_hempty pre -> acc
      | Constr.App (fname, [|heaplet; rest|]) when is_hstar fname ->
        begin match Constr.kind heaplet with
        | Constr.App (fname, [| fn |]) when is_hpure fname ->
          loop (`Pure fn :: acc) rest             
        | Constr.App (fname, _) when is_hpure fname ->
          loop (`Pure heaplet :: acc) rest             
        | _ ->
          loop (`Impure heaplet :: acc) rest
        end
      | _ ->
        `Impure pre :: acc in
    loop [] pre in
  let pre =
    match Constr.kind c with
    | Constr.Const (_, _) when is_hempty c -> `Empty
    | Constr.App (fname, _) when is_hstar fname ->
      begin match destruct_heap c with
      | heap -> `NonEmpty (List.rev heap)
      | exception _ -> failwith ("unexpected heap structure: " ^ (Proof_debug.constr_to_string c))
      end
    | Constr.App (fname, [| c |]) when is_hpure fname ->
      `NonEmpty ([`Pure c])
    | Constr.App (fname, _) when is_hpure fname ->
      `NonEmpty ([`Pure c])
    | _ -> `NonEmpty ([`Impure c]) in
  pre

(** [cfml_extract_logical_functions ?set c] returns the set [set] of all logical
    functions used inside a CFML heaplet [c]. *)
let cfml_extract_logical_functions ?(set=StringSet.empty) c =
  let rec loop ?(is_repr=false) set c =
    match Constr.kind_nocast c with
    | Constr.App (f, [| arg |]) when is_hpure f ->
      loop set arg
    | Constr.App (f, [| _ty; body; _var |]) when is_const_named "repr" f ->
      loop ~is_repr:true set body
    | Constr.App (f, args) when is_repr ->
      loop set args.(Array.length args - 1)
    | Constr.App (f, [| _ty; body |]) when is_const_named "hexists" f ->
      let _, _, body = Constr.destLambda body in
      loop set body
    | Constr.App (f, [| l; r |]) when is_const_named "hstar" f ->
      let set = loop set l in
      loop set r
    | Constr.App (f, [| _ty; l; r |]) when Utils.is_coq_eq f ->
      let set = loop set l in
      loop set r
    | Constr.App (f, args) when Constr.isConst f ->
      let name, _ = Constr.destConst f in
      let set = StringSet.add (Names.Constant.to_string name) set in
      let args = Utils.drop_implicits name (Array.to_list args) in
      List.fold_left loop set args
    | _ -> set in
  loop set c

(** [extract_cfml_goal goal] when given an intermediate CFML [goal],
    extracts the pre and post condition.  *)
let extract_cfml_goal goal =
  let himpl, args = Constr.decompose_app goal in
  if not begin
    String.equal "himpl"
      (fst (Constr.destConst himpl)
       |> Names.Constant.label
       |> Names.Label.to_string)
  end then
    Format.ksprintf ~f:failwith
      "unexpected goal format, expected himpl, found %s"
      (Proof_debug.constr_to_string_pretty himpl);

  if List.length args <> 2 then
    Format.ksprintf ~f:failwith
      "unexpected arguments to himpl [%s]"
      (List.map Proof_debug.constr_to_string_pretty args
       |> String.concat "; ");

  let pre = List.nth args 0 and post = List.nth args 1 in

  let pre = extract_heap pre in

  (pre, post)

(** [extract_xapp_type c] given a coq term [c] representing a CFML
    goal immediately prior to calling a function, returns the return
    type of the function. *)
let extract_xapp_type pre =
  let extract_app_enforce name f n pre =
    match Constr.kind pre with
    | Constr.App (fname, args) when f fname && Array.length args > n ->
      args.(n)
    | _ ->
      Log.err (fun f -> f "failed because unknown structure for %s: %s\n" name (Proof_debug.constr_to_string pre));
      failwith name in
  try
    pre
    |> extract_app_enforce "himpl" is_himpl 1
    |> extract_app_enforce "wptag" is_wptag 0
    |> extract_app_enforce "wpgen_let_trm" is_wp_gen_let_trm 0
    |> extract_app_enforce "wptag" is_wptag 0
    |> extract_app_enforce "xapp" is_wp_gen_app 0
    |> extract_typ
  with
    Failure msg -> failwith ("extract_f_app failed " ^ msg ^ " because unsupported context: " ^ (Proof_debug.constr_to_string pre))


(** [extract_xapp_fun c] given a coq term [c] representing a reified
    CFML encoding of an OCaml program with a let of a function as the
    next statement, extracts the function being called's arguments. *)
let extract_x_app_fun pre =
  let extract_app_enforce name f n pre =
    match Constr.kind pre with
    | Constr.App (fname, args) when f fname ->
      args.(n)
    | _ ->
      Log.warn (fun f ->
        f "failed because unknown structure for %s: %s\n" name (Proof_debug.constr_to_string pre));
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
  (* extract spec repeatedly destructs products (arrow types) until it
     reaches a non-product type.  *)
  let extract_spec pre =
    let rec loop acc pre = 
      if Constr.isProd pre
      then
        let ({Context.binder_name; _}, ty, pre)  = Constr.destProd pre in
        loop ((binder_name, ty) :: acc) pre
      else List.rev acc, pre in
    loop [] pre in
  (* split_anonymous, given a list of parameters, partitions by the
     first occurrence of an anonymous argument into a tuple of the
     named arguments, and the remaining arguments *)
  let rec split_anonymous acc ls =
    match ls with
    | [] -> (List.rev acc,[])
    | ((name, _) as h) :: t when Names.Name.is_anonymous name ->
      (List.rev acc, h::t)
    | h :: t -> split_anonymous (h :: acc) t in
  let params, body = extract_spec pre in
  let params, invariants = split_anonymous [] params in
  (params, invariants, body)

(** [extract_dyn_var ?rel c] given a Coq term [c] of the form {[Dyn v]}, extracts the corresponding expression and type.  *)
let extract_dyn_var ?env ?rel (c: Constr.t) =
  match Constr.kind c with
  | Constr.App (const, [| ty; _enc; vl |]) when Utils.is_constr_eq "CFML.SepLifted.dyn" const ->
    (extract_expr ?env ?rel vl, extract_typ ty)
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
      Some (name, `Val (Lang.Type.Func None))
    | Constr.App (fn, _)
      when Utils.is_const_eq "CFML.WPLifted.Wpgen_body" fn
        || Utils.is_const_eq "CFML.WPLifted.Wpgen_negpat" fn ->
      None                    (* specifications *)
    | Constr.Ind ((ty_name, _), _) ->
      Some (name, `Val (extract_typ vl))
    | Constr.Var _              (* init: A *)
    | Constr.App (_, _) ->
      Option.map (fun vl -> (name, `Val (vl))) (extract_typ_opt vl)
    | Constr.Prod (_, _, _) ->
      begin match extract_typ_opt vl with
      | None -> None
      | Some ty -> Some (name, `Val ty)
      end
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

(** [unwrap_eq ?env ?rel c] when given a Coq term [c] representing an
    propositional equality, extracts the left and right hand sides of
    the equality. *)
let unwrap_eq ?env ?rel (c: Constr.t) =
  match Constr.kind c with
  | Constr.App (fname, [| ty; l; r |]) when Utils.is_ind_eq "Coq.Init.Logic.eq" fname ->
    let ty = extract_typ ty in
    let l = extract_expr ?env ?rel l in
    let r = extract_expr ?env ?rel r in
    (ty, l, r)
  | _ ->
    Format.ksprintf ~f:failwith
      "found unexpected Coq term (%s)[%s] ==> %s, when expecting an equality"
      (Proof_debug.constr_to_string c) (Proof_debug.tag c) (Proof_debug.constr_to_string_pretty c)

(** [extract_embedded_function_name expr] extracts a function name
   from an [expr] expression representing an embedded CFML program AST. *)
let extract_embedded_function_name expr =
  match expr with 
  | `Var v -> v
  | `App ("CFML.WPRecord.val_get_field", [`Var fld]) ->
    (* CFML encodes field accesses in the form (CFML.WPRecord.val_get_field Common.<module-name>_ml.<field-name>') *)
    let components = String.split_on_char '.' fld |> List.rev in
    (* extract the components *)
    let field_name, components = List.hd_tl components in
    let modl, _ = List.hd_tl components in
    (* drop the last apostrophe in the field name *)
    let field_name = String.take (String.length field_name - 1) field_name in
    (* drop the _ml in the module name *)
    let modl = String.take (String.length modl - 3) modl in
    modl ^ ".get_field_" ^ field_name
  | expr -> Format.ksprintf ~f:failwith "found application to non-constant function (%a)"
              Lang.Expr.pp expr  

(** [extract_embedded_expr ?rel c] extracts a deeply embedded CFML
    expression from a Coq term [c]. [rel] is a function that maps Coq's
    de-bruijin indices to the corresponding terms in the wider typing
    environment. *)
let rec extract_embedded_expr ?rel (c: Constr.t) : Lang.Expr.t =
  match Constr.kind c, rel with
  | Constr.App (fn, [| f |]), _ when Utils.is_const_eq "CFML.WPLifted.Wptag" fn ->
    extract_embedded_expr ?rel f
  | Constr.App (fn, [| ty; enc_ty; f; args |]), _ when Utils.is_const_eq "CFML.WPLifted.Wpgen_app" fn ->
    let fn = extract_expr ?rel f |> extract_embedded_function_name in
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
    let var = if Constr.isCast var then let (t, _, _) = Constr.destCast var in t else var in
    let var =
      check_or_fail "variable" Constr.isVar var
      |> Constr.destVar |> Names.Id.to_string in
    let ty = extract_typ ty in
    let body' = extract_expr body in
    Log.debug (fun f -> f "extracting %s ==> %a" (Proof_debug.constr_to_string body) Lang.Expr.pp body');
    PointsTo (var, Some ty, body')
  | _ ->
    Format.ksprintf ~f:failwith "found unhandled Coq term (%s)[%s] in (%s) that could not be converted to a heaplet"
      (Proof_debug.constr_to_string c) (Proof_debug.tag c) (Proof_debug.constr_to_string_pretty c)

(** [is_const_wp_fn cst] determines whether a {!Names.Constant.t} constant
    represents a constant weakest precondition helper. *)
let is_const_wp_fn cst =
  String.suffix ~suf:"_cf__" @@  Names.Constant.to_string cst

(** [is_const_wp_fn_trm cst] determines whether a {!Constr.t} term
    represents a constant weakest precondition helper. *)
let is_const_wp_fn_trm cst =
  Constr.isConst cst && begin
    let cst, _ = Constr.destConst cst  in
    is_const_wp_fn cst
  end


(** [extract_pre_heap c] given a Coq term [c] representing a partially
    instantiated CFML specification, returns the pre-heap.

    Note: assumes that a CFML spec has been sufficiently instantiated
    such that any variables occuring in the pre-heap are not bound by
    binders within [c]. *)
let extract_pre_heap pre =
  let extract_spec pre =
    let rec loop pre =
      if Constr.isProd pre
      then
        let (_, _, pre)  = Constr.destProd pre in
        loop pre
      else pre in
    loop pre in
  let spec = extract_spec pre in
  let pre =
    match (Constr.kind_nocast spec) with
    | Constr.App (f, args) when Utils.is_const_eq "CFML.SepLifted.Triple" f ->
      args.(3)
    | _ ->
      Format.ksprintf ~f:failwith
        "unexpected structure for specification: %s" (Proof_debug.constr_to_string spec) in
  Log.debug (fun f -> f "extract_pre_heap pre: %s" (Proof_debug.constr_to_string pre));
  match extract_heap pre with
  | `Empty -> []
  | `NonEmpty heap ->
    let heap = List.rev heap in
    (List.filter_map
       (function `Pure p -> Some (`Pure p)
               | `Impure inv when Constr.isApp inv && begin let (f, _) = Constr.destApp inv in Constr.isVar f end -> None
               | `Impure c ->
                 match Constr.kind_nocast c with
                 | Constr.App (fname, [| ty; body; var |]) when
                     Utils.is_const_eq "CFML.SepBase.SepBasicSetup.HS.repr" fname ->
                   let var = match Constr.kind_nocast var with
                     | Constr.Var name -> Names.Id.to_string name
                     | _ -> 
                       Format.ksprintf ~f:failwith "found unhandled Coq term (%s)[%s] in (%s) that could not be converted to a var"
                         (Proof_debug.constr_to_string var) (Proof_debug.tag var) (Proof_debug.constr_to_string_pretty var) in
                   let ty = extract_typ ty in
                   Some (`Impure (var, ty))
                 | _ ->
                   Format.ksprintf ~f:failwith "found unhandled Coq term (%s)[%s] in (%s) that could not be converted to a heaplet"
                     (Proof_debug.constr_to_string c) (Proof_debug.tag c) (Proof_debug.constr_to_string_pretty c)
       )
    ) heap

(** [count_no_existentials_in_unfold ty] counts the number of
    existentials introduced by an unfold lemma with type [ty].  *)
let count_no_existentials_in_unfold ty =
  (* drop prods repeatedly drop prods until we reach the core lemmas *)
  let rec drop_prods ty = match Constr.kind_nocast ty with
    | Constr.Prod (_, _, ty) -> drop_prods ty
    | _ -> ty in
  let rec count_existentials acc ty = match Constr.kind_nocast ty with
    | Constr.Prod (_, _, ty) -> count_existentials acc ty
    | Constr.Lambda (_, _, ty) -> count_existentials acc ty
    | Constr.App (trm, [| _; ty |]) when Utils.is_const_eq "CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists" trm ->
      count_existentials (acc + 1) ty
    | _ -> acc in
  let inner_ty = drop_prods ty in
  match Constr.kind_nocast inner_ty with
  | Constr.App (eq, [| _; _; ty |]) when Utils.is_coq_eq eq  ->
    count_existentials 0 ty
  | Constr.App (himpl, [| _; ty |]) when is_himpl himpl ->
    count_existentials 0 ty
  | _ ->
    Format.ksprintf ~f:failwith "unexpected structure for unfold lemma \
                                 %s - expecting a sequence of products \
                                 followed by an equality or himpl."
      (Proof_debug.constr_to_string ty)
