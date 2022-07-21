[@@@warning "-26"]
open Containers
module StringMap = Map.Make(String)

type t = Parsetree.expression
type lambda_env = (Lang.Id.t * [ `Lambda of Lang.Expr.typed_param list * Lang.Expr.t Lang.Program.stmt ]) StringMap.t

module PCFML = Proof_utils.CFML

(** [is_const_wp_fn cst] determines whether a {!Constr.t} term
    represents a constant weakest precondition helper. *)
let is_const_wp_fn cst =
  Constr.isConst cst && begin
    let cst, _ = Constr.destConst cst  in
    String.suffix ~suf:"_cf__" @@  Names.Constant.to_string cst
  end

(** [is_case_of_eq_sym] determines whether a {!Constr.t} term
   represents a case over an [Logic.eq_sym] equality.

    TODO: generalise to case over arbitrary equalities? should be
   fairly straightforward.  *)
let is_case_of_eq_sym case =
  Constr.isCase case &&
  let (_, _, _, _, _, case_expr, branches) = Constr.destCase case in      
  Array.length branches = 1 && Constr.isApp case_expr && begin
    let trm, _ = Constr.destApp case_expr in
    PCFML.is_const_named "eq_sym" trm
  end  

let name_to_string name = Format.to_string Pp.pp_with (Names.Name.print name)

type env = (string * Lang.Type.t option) list

let rel_ty env ind =
  let ind = ind - 1 in
  List.nth env ind
  |> snd
  |> Option.get_exn_or "attempted to construct invalid typ"

let rel_expr env ind =
  let ind = ind - 1 in
  match (List.nth_opt env ind) with
  | None ->
    Format.ksprintf ~f:failwith "attempted to access index %d in env of length %d; env is %s" ind (List.length env)
      ([%show: (string * Lang.Type.t option) list] env)
  | Some (v, _) -> v

let add_binding ?ty var env =
  (var, ty) :: env

let extract_proof_value env ty =
  try `Eq (PCFML.unwrap_eq ~rel:(rel_expr env) ty) with
  | e ->
    Format.printf "received exception: %s@." (Printexc.to_string e);
    try  `Expr (PCFML.extract_expr ~rel:(rel_expr env) ty)  with
    | e ->
      Format.printf "received exception: %s@." (Printexc.to_string e);
      try `Ty (PCFML.extract_typ ~rel:(rel_ty env) ty) with
      | e ->
        Format.printf "received exception: %s@." (Printexc.to_string e);
        `Proof (Proof_utils.Debug.constr_to_string ty)

let extract_typ_from_proof_value = function
    | (`Ty vl) as p_vl -> Some vl, p_vl
    | _ as p_vl -> None, p_vl

let rec extract_sym_heap env c =
  Format.printf "extract_sym_heap of %s@.%s@."
    (Proof_utils.Debug.constr_to_string_pretty c)
    (Proof_utils.Debug.constr_to_string c);
  match Constr.kind c with
  | Constr.App (fn, [| h1; h2|]) when Proof_utils.is_const_eq "CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar" fn ->
    extract_sym_heap env h1 @ extract_sym_heap env h2
  | Constr.App (fn, _) when Proof_utils.is_const_eq "CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hcredits" fn ->
    []
  | Constr.Const _ when Proof_utils.is_const_eq "CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hempty" c -> []
  | _ -> 
    try [`Invariant (PCFML.extract_expr ~rel:(rel_expr env) c)] with
    | _ -> []

let extract_trm_apps env (trm: Constr.t) =
  match Constr.kind trm with
  | Constr.App (fn, [| f; args |]) when Proof_utils.is_const_eq "CFML.SepLifted.Trm_apps" fn ->
    let f = Constr.destConst f |> fst |> Names.Constant.to_string in
    let args =
      Proof_utils.unwrap_inductive_list args
      |> List.map (PCFML.extract_dyn_var ~rel:(rel_expr env))
      |> List.map fst
    in
    f, args
  | _ ->
    Format.ksprintf ~f:failwith "expected CFML.SepLifted.Trm_apps, but received %s"
      (Proof_utils.Debug.constr_to_string_pretty trm)
    
let extract_prop_type env (trm: Constr.t) =
  let rec extract_params env params trm =
    match Constr.kind trm with
    | Constr.Prod ({Context.binder_name; _}, ty, trm) ->
      let name = name_to_string binder_name in
      let ty, proof_ty = extract_proof_value env ty |> extract_typ_from_proof_value in
      let env = add_binding ?ty name env in
      extract_params env ((name, proof_ty) :: params) trm
    | _ ->
      extract_spec env (List.rev params) trm
  and extract_spec env params trm =
    match Constr.kind trm with
    | Constr.App (fn, [| vl; ret_ty; enc_ret_ty; pre; post |]) when Proof_utils.is_const_eq "CFML.SepLifted.Triple" fn ->
      let spec = extract_trm_apps env vl in
      let pre = extract_sym_heap env pre in
      let post =
        let {Context.binder_name=ret_name; _}, ty, post = Constr.destLambda post in
        let ret_name = name_to_string ret_name in
        let ty = PCFML.extract_typ ~rel:(rel_ty env) ty in
        let env = add_binding ~ty ret_name env in
        let post = extract_sym_heap env post in
        (ret_name, ty, post) in
      ({
        params;
        spec;
        pre;
        post
      }: Proof_term.prop_type)
    | _ -> 
      Format.ksprintf ~f:failwith "expected CFML.SepLifted.Triple, but received %s"
        (Proof_utils.Debug.constr_to_string_pretty trm)
  in
  extract_params env [] trm

let extract_prop_spec env (trm: Constr.t) =
  let ({Context.binder_name;_}, ty, body) = Constr.destLambda trm in
  let name = name_to_string binder_name in 
  let ty, proof_ty = extract_proof_value env ty |> extract_typ_from_proof_value in
  let env = add_binding ?ty name env in
  (name, Option.get_exn_or "found invalid type" ty), extract_prop_type env body

let extract_match_code_case_values env (trm: Constr.t) : (Lang.Expr.t * Lang.Expr.t) list =
  let rec extract_case_vl env vl =
    match Constr.kind vl with
    | Constr.App (wp_tag, [| vl |]) when Proof_utils.is_const_eq "CFML.WPLifted.Wptag" wp_tag ->
      extract_case_vl env vl
    | Constr.App (negpat, [| vl |]) when Proof_utils.is_const_eq "CFML.WPLifted.Wpgen_negpat" negpat ->
      drop_lambdas env vl       
    | _ ->
      Format.ksprintf ~f:failwith "expected a negpat, but received %s (in env %s)"
        (Proof_utils.Debug.constr_to_string_pretty vl)
        ([%show: (string * Lang.Type.t option) list] env);
  and drop_lambdas env vl =
    match Constr.kind vl with
    | Constr.Prod ({Context.binder_name; _}, ty, vl) ->
      let binder_name = name_to_string binder_name in
      let ty, proof_ty = extract_proof_value env ty |> extract_typ_from_proof_value in
      let env = add_binding ?ty binder_name env in
      drop_lambdas env vl
    | _ ->
      drop_not env vl
  and drop_not env vl =
    match Constr.kind vl with
    | Constr.App (nt, [| vl |]) when Proof_utils.is_const_eq "Coq.Init.Logic.not" nt ->
      drop_eq env vl
    | _ ->
      Format.ksprintf ~f:failwith "expected a logical not, but received %s (in env %s)"
        (Proof_utils.Debug.constr_to_string_pretty vl)
        ([%show: (string * Lang.Type.t option) list] env)
  and drop_eq env vl = 
    match Constr.kind vl with
    | Constr.App (eq, [| ty; vl; case |]) when Proof_utils.is_coq_eq eq ->
      let vl = PCFML.extract_expr ~rel:(rel_expr env) vl in
      let case = PCFML.extract_expr ~rel:(rel_expr env) case in
      (vl, case)
    | _ ->
      Format.ksprintf ~f:failwith "expected a logical equality, but received %s (in env %s)"
        (Proof_utils.Debug.constr_to_string_pretty vl)
        ([%show: (string * Lang.Type.t option) list] env)
  in
  let rec loop acc trm =
    match Constr.kind trm with
    | Constr.App (wp_tag, [| trm |])
      when Proof_utils.is_const_eq "CFML.WPLifted.Wptag" wp_tag ->
      loop acc trm
    | Constr.App (wpgen_case, [| _; neg_pat; trm |]) ->
      let vl = extract_case_vl env neg_pat in
      loop (vl :: acc) trm 
    | Constr.Const _ when Proof_utils.is_const_eq "CFML.WPLifted.Wpgen_done" trm ->
      List.rev acc
    | _ -> failwith "lol" in
  loop [] trm

let rec reify_proof_term (env: env) (trm: Constr.t) : Proof_term.t  =
  match Constr.kind trm with
  | Constr.App (acc_rect, args) when PCFML.is_const_named "Acc_rect" acc_rect ->
    extract_fold_specification env trm
  | Constr.App (trm , [| typ; proof |]) when Proof_utils.is_const_eq "TLC.LibTactics.rm" trm ->
    reify_proof_term env proof
  | Constr.App (trm, [| typ; vl; prop; proof; vl'; proof_eq |]) when PCFML.is_const_named "eq_ind" trm ->
    reify_proof_term env proof
  | Constr.App (trm, args) when PCFML.is_const_named "reflexive_proper" trm ->
    let proof = args.(Array.length args - 1) in
    reify_proof_term env proof
  | Constr.App (trm, [|
    pre; credits; hla;  hlw; hlt; hra; hrg; hrt; proof
  |]) when PCFML.is_xsimpl_lr_cancel_same trm ->
    reify_proof_term env proof
  | Constr.App (trm, [| a; q1; q2; hla; nc; proof |]) when PCFML.is_xsimpl_lr_qwand trm ->
    let ({Context.binder_name; _}, ty, proof) = Constr.destLambda proof in
    let binder_name = name_to_string binder_name in
    let ty, proof_ty = extract_proof_value env ty |> extract_typ_from_proof_value in
    let env = add_binding ?ty binder_name env in
    Lambda ( binder_name, proof_ty,
      reify_proof_term env proof
    )
  | Constr.App (trm, [| hla; hrg; haffine; proof |]) when PCFML.is_xsimpl_lr_hgc_nocredits trm ->
    reify_proof_term env proof    
  | Constr.App (trm, args (* [| ty; vl; prop; proof; vl'; proof_vl_eq_vl'; |] *)) when PCFML.is_const_named "eq_ind_r" trm ->
    let proof = args.(3) in
    reify_proof_term env proof
  | Constr.App (trm, [| ty; vl; prop; proof; vl'; proof_vl_eq_vl'; |]) when PCFML.is_const_named "eq_ind_r" trm ->
    reify_proof_term env proof
  | Constr.App (trm, [| post_1; post_2; pre; proof_of_post_1; proof_of_post_2; |]) when PCFML.is_himpl_hand_r trm ->
    let pre = extract_sym_heap env pre in
    HimplHandR (
      pre,
      reify_proof_term env proof_of_post_1,
      reify_proof_term env proof_of_post_2
    )
  | Constr.App (trm, [|
    new_pre;
    pre;
    post;
    proof_pre_impl_new_pre;
    proof_new_pre_impl_post
  |]) when PCFML.is_himpl_trans trm ->
    let pre = extract_sym_heap env pre in
    let new_pre = extract_sym_heap env new_pre in
    HimplTrans (
      pre,
      new_pre,
      reify_proof_term env proof_pre_impl_new_pre,
      reify_proof_term env proof_new_pre_impl_post    
    )
  | Constr.App (trm, [| pre_frame_a;  pre_frame_b; post; proof |]) when PCFML.is_himpl_frame_r trm ->
    reify_proof_term env proof
  | Constr.App (trm, [| prop; pre; post; proof |]) when PCFML.is_himpl_hstar_hpure_l trm ->
    let ({Context.binder_name=proof_binding_name;_}, ty, proof) = Constr.destLambda proof in
    let proof_binding_name = name_to_string proof_binding_name in
    let ty, proof_ty = extract_proof_value env ty |> extract_typ_from_proof_value in
    let env = add_binding ?ty proof_binding_name env in
    Lambda (
      proof_binding_name,
      proof_ty,
      reify_proof_term env proof
    )
  | Constr.App (trm, [| pre; post; proof |]) when PCFML.is_xsimpl_lr_exit_nogc_nocredits trm ->
    reify_proof_term env proof
  | Constr.App (trm, ([| pre; post; proof |] as args)) when PCFML.is_xsimpl_start trm ->
    reify_proof_term env proof
  | Constr.App (trm, [| pre; post; proof |]) when PCFML.is_hstars_simpl_start trm ->
    reify_proof_term env proof
  | Constr.App (trm, [| pre'; post_left; framed; post_right; proof |]) when PCFML.is_hstars_simpl_cancel trm ->
    reify_proof_term env proof
  | Constr.App (trm, [| pre; pre'; post; proof_pre_eq_pre'; proof |]) when PCFML.is_hstars_simpl_pick_lemma trm ->
    reify_proof_term env proof
  | Constr.App (trm, [| post; post_proof |] ) when PCFML.is_himpl_hempty_pure trm ->
    reify_proof_term env post_proof
  | Constr.App (trm, [|
    exists_ty; exists_binding;
    pre;
    post;
    proof
  |]) when PCFML.is_himpl_hexists_r trm ->
    reify_proof_term env proof
  | Constr.App (trm, [| ty; post; pre; proof |]) when PCFML.is_himpl_hforall_r trm ->
    let ({Context.binder_name=binding;_}, ty, proof) = Constr.destLambda proof in
    let binding_name = name_to_string binding in
    let ty, proof_ty = extract_proof_value env ty |> extract_typ_from_proof_value in
    let env = add_binding ?ty binding_name env in
    Lambda (
      binding_name, proof_ty,
      reify_proof_term env proof      
    )
  | Constr.App (trm, [|
    pre;                        (* current heap state at current program point *)
    code;                       (* code of rest of program *)
    _res_ty; _res_ty_enc;       (* result type, result type encoding  *)
    post;                       (* post condition (parameterised by value of result type) *)
    proof                       (* proof of rest *)
  |]) when PCFML.is_mkstruct_erase trm ->
    reify_proof_term env proof
  | Constr.App (trm, [|
    let_ty;                     (* type of value being let bound *)
    pre;                        (* current heap state at let binding *)
    let_body;                   (* lambda that returns the code of the body of the binding  *)
    let_vl;                     (* the value being bound *)
    _res_ty;                    (* type of the result of the body *)
    _res_ty_enc;                (* Enc type for the type of the result of the body *)
    _post;                      (* function that takes in the result of body and returns the post condition *)
    proof                       (* function takes a value, and a proof value equals [let_vl], producing a proof  *)
  |]) when PCFML.is_xlet_val_lemma trm ->
    let let_vl = PCFML.extract_expr ~rel:(rel_expr env) let_vl in
    let pre = extract_sym_heap env pre in
    let ({Context.binder_name=let_binding_name;_}, let_binding_ty, proof) = Constr.destLambda proof in
    let let_binding_name = name_to_string let_binding_name in
    let let_binding_ty, let_binding_proof_ty = extract_proof_value env let_binding_ty |> extract_typ_from_proof_value in
    let env = add_binding ?ty:let_binding_ty let_binding_name env in
    let ({Context.binder_name=eq_prf_name;_}, eq_prf_ty, proof) = Constr.destLambda proof in
    let eq_prf_name = name_to_string eq_prf_name in
    let eq_prf_ty, eq_prf_proof_ty = extract_proof_value env eq_prf_ty |> extract_typ_from_proof_value in
    let env = add_binding ?ty:eq_prf_ty eq_prf_name env in
    let let_ty, _ = extract_proof_value env let_ty |> extract_typ_from_proof_value in
    let let_ty = Option.get_exn_or "found invalid type" let_ty in
    let eq_prf_ty = match eq_prf_proof_ty with
      | `Eq (_, `Var var, expr) -> (var, expr)
      | _ -> failwith "invalid type" in
    XLetVal {
      pre=pre;
      binding_ty=let_ty;
      let_binding=(let_binding_name, Option.get_exn_or "found invalid type" let_binding_ty);
      eq_binding=(eq_prf_name, eq_prf_ty);
      value=let_vl;
      proof=reify_proof_term env proof;
    }
  | Constr.App (trm, [|
    _res_ty;
    _res_ty_enc;
    pre;
    code;
    post;
    proof
  |]) when PCFML.is_xmatch_lemma trm ->
    let pre = extract_sym_heap env pre in
    let value = extract_match_code_case_values env code in
    XMatch {
      value;
      pre=pre;
      proof=reify_proof_term env proof;
    }
  | Constr.App (trm, [|
    binding_ty; enc_binding_ty;
    pre;
    ret_ty; enc_ret_ty;
    post;
    value_code;
    rest_code;
    proof
  |]) when PCFML.is_xlet_trm_cont_lemma trm ->
    let pre = extract_sym_heap env pre in
    let value_code = PCFML.extract_embedded_expr ~rel:(rel_expr env) value_code in
    let binding_ty, binding_proof_ty = extract_proof_value env binding_ty |> extract_typ_from_proof_value in
    XLetTrmCont {
      pre=pre;
      binding_ty=Option.get_exn_or "found invalid type" binding_ty;
      value_code=value_code;
      proof=reify_proof_term env proof
    }
  | Constr.App (trm, [|
    ret_ty; enc_ret_ty;
    fun_post;
    f;
    args;
    fun_pre;
    pre;
    post;
    proof_fun;
    proof;
  |]) when PCFML.is_xapp_lemma trm ->
    let pre = extract_sym_heap env pre in
    let fun_pre = extract_sym_heap env fun_pre in
    let application =
      let f =
        match Constr.kind f with
        | Constr.Var v -> Names.Id.to_string v
        | Constr.Const (c, _) -> Names.Constant.to_string c
        | Constr.Rel n -> rel_expr env n
        | _ -> Format.ksprintf ~f:failwith "expected constant function, received %s" (Proof_utils.Debug.constr_to_string_pretty f) in
      let args = Proof_utils.unwrap_inductive_list args
                 |> List.map (PCFML.extract_dyn_var ~rel:(rel_expr env))
                 |> List.map fst in
      (f, args) in
    XApp {
      pre=pre;
      application;
      fun_pre=fun_pre;
      proof_fun=reify_proof_term env proof_fun;
      proof=reify_proof_term env proof;
    }
  | Constr.App (case, args) when is_case_of_eq_sym case ->
    let (_, _, _, _, _, case_expr, branches) = Constr.destCase case in
    let (names, body) = branches.(0) in
    let kont, proof, env =
      Iter.repeat ()
      |> Iter.fold_while
           (fun (kont, v, env) () ->
              if Constr.isLambda v then
                let {Context.binder_name=vl; _}, ty, v = Constr.destLambda v in
                let vl = name_to_string vl in
                let ty, proof_ty = extract_proof_value env ty |> extract_typ_from_proof_value in
                let env = add_binding ?ty vl env in
                let kont proof = kont (Proof_term.Lambda (
                  vl,
                  proof_ty,
                  proof
                )) in
                (kont, v, env), `Continue
              else
                (kont, v, env), `Stop
           ) ((fun x -> x), body, env) in
    kont (reify_proof_term env proof)
  | Constr.App (trm, [| ty |]) when PCFML.is_xsimpl_lr_refl_nocredits trm ->
    Refl
  | Constr.App (trm, [| ret_ty; enc_ret_ty; post; heaplet |]) when PCFML.is_xdone_lemma trm ->
    let heaplet = extract_sym_heap env heaplet in
    XDone heaplet
  | Constr.App (trm, [| heaplet |]) when PCFML.is_himpl_refl trm ->
    Refl
  | Constr.App (trm, [| ty; enc_ty; vl; pre; post; proof |]) when PCFML.is_xval_lemma trm ->
    let pre = extract_sym_heap env pre in
    let ty, proof_ty = extract_proof_value env ty |> extract_typ_from_proof_value in
    let vl = PCFML.extract_expr ~rel:(rel_expr env) vl in
    XVal {
      pre=pre;
      value_ty=Option.get_exn_or "found invalid type" ty;
      value=vl
    }
  | Constr.App (var, args) when Constr.isVar var ->
    let var = Constr.destVar var |> Names.Id.to_string in
    let args = Array.to_iter args
               |> Iter.map (extract_proof_value env)
               |> Iter.map (function
                   `Expr e -> `Expr e
                 | v -> `ProofTerm ([%show: Proof_term.proof_value] v))
               |> Iter.to_list in
    VarApp (var, args)
  | Constr.App (var, args) when Constr.isRel var ->
    let var = Constr.destRel var |> rel_expr env in
    let args = Array.to_iter args
               |> Iter.map (extract_proof_value env)
               |> Iter.map (function
                   `Expr e -> `Expr e
                 | v -> `ProofTerm ([%show: Proof_term.proof_value] v))
               |> Iter.to_list in
    VarApp (var, args)
  | Constr.App (trm, args) when is_const_wp_fn trm && Array.length args > 5 ->
    let pre = args.(Array.length args - 5) |> extract_sym_heap env in
    let proof = args.(Array.length args - 1) in
    let args = 
      Iter.int_range ~start:0 ~stop:(Array.length args - 1 - 5)
      |> Iter.map (Array.get args)
      |> Iter.map (extract_proof_value env)
      |> Iter.to_list in
    CharacteristicFormulae {
      pre;
      args;
      proof=reify_proof_term env proof
    }
  | Constr.App (trm, args) ->
    Format.ksprintf ~f:failwith
      "reify_proof_term env received App of %s (%s) to %d args\n%s@."
      (String.take 400_000 (Proof_utils.Debug.constr_to_string trm)) (Proof_utils.Debug.tag trm)
      (Array.length args)
      (Array.to_string (fun v -> "{" ^ String.take 40_000 (Proof_utils.Debug.constr_to_string v) ^ "}") args)
  | Constr.Lambda ({Context.binder_name;_}, ty, proof) ->
    let binder_name = name_to_string binder_name in
    let ty, proof_ty = extract_proof_value env ty |> extract_typ_from_proof_value in
    let env = add_binding ?ty binder_name env in
    Lambda (
      binder_name,
      proof_ty,
      reify_proof_term env proof      
    )
  | _ ->
    Format.ksprintf ~f:failwith
      "reify_proof_term env received %s"
      (String.take 4000_000 (Proof_utils.Debug.constr_to_string trm))

and extract_fold_specification (env: env) (trm: Constr.t) : Proof_term.t =
  let (_, args) = Constr.destApp trm in
  let prop_spec = args.(2) |> extract_prop_spec env in
  let recursive_spec = args.(3) in
  let vl = PCFML.extract_expr ~rel:(rel_expr env) args.(4) in
  let args = Iter.int_range ~start:6 ~stop:(Array.length args - 1)
         |> Iter.map (fun i -> args.(i))
         |> Iter.map (extract_proof_value env)
         |> Iter.map (function `Expr e -> `Expr e | v -> `ProofTerm ([%show: Proof_term.proof_value] v))
         |> Iter.to_list in
  (* t: args.(6)  == nil & x *)
  (* init: args.(7) == init *)
  let ({Context.binder_name=rec_vl;_}, rec_vl_ty, recursive_spec) = Constr.destLambda recursive_spec in
    let rec_vl = name_to_string rec_vl in
    let rec_vl_ty, rec_vl_proof_ty = extract_proof_value env rec_vl_ty |> extract_typ_from_proof_value in
    let env = add_binding ?ty:rec_vl_ty rec_vl env in
  let ({Context.binder_name=h_acc;_}, ty_h_acc, recursive_spec) = Constr.destLambda recursive_spec in
    let h_acc = name_to_string h_acc in
    let h_acc_ty, h_acc_proof_ty = extract_proof_value env ty_h_acc |> extract_typ_from_proof_value in
    let env = add_binding ?ty:h_acc_ty h_acc env in

  let ({Context.binder_name=ih_vl;_}, ih_vl_ty, recursive_spec) = Constr.destLambda recursive_spec in
    let ih_vl = name_to_string ih_vl in
    let ih_vl_prop_ty = extract_prop_type env ih_vl_ty in
    let env = add_binding ih_vl env in

  

  AccRect {
    prop_type=prop_spec;
    proof={
      x=rec_vl; ty_x=Option.get_exn_or "found invalid type" rec_vl_ty;
      h_acc=h_acc; ty_h_acc=Proof_utils.Debug.constr_to_string_pretty ty_h_acc;
      ih_x= ih_vl; ty_ih_x=ih_vl_prop_ty;
      proof=reify_proof_term env recursive_spec
    };
    vl=vl;
    args=args
  }

let analyse (lambda_env: lambda_env) (obs: (Dynamic.Concrete.context * Dynamic.Concrete.heap_context)) (trm: Constr.t) : t =
  match Constr.kind trm with
  | Constr.App (trm, args) when is_const_wp_fn trm && Array.length args > 0 ->
    let wp = args.(Array.length args - 1) in
    let proof_term = reify_proof_term [] wp in
    let test_spec = (Proof_extraction.extract proof_term) in
    test_spec
  | _ ->

    failwith ("lol " ^ Proof_utils.Debug.tag trm)
  
