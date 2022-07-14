[@@@warning "-26"]
open Containers

type t = Lol

module PCFML = Proof_utils.CFML

(** [is_const_wp_fn cst] determines whether a {!Constr.t} term
   represents a constant weakest precondition helper. *)
let is_const_wp_fn cst =
  Constr.isConst cst && begin
    let cst, _ = Constr.destConst cst  in
    String.suffix ~suf:"_cf__" @@  Names.Constant.to_string cst
  end

let is_case_of_eq_sym case =
  Constr.isCase case &&
  let (_, _, _, _, _, case_expr, branches) = Constr.destCase case in      
  Array.length branches = 1 && Constr.isApp case_expr && begin
    let trm, _ = Constr.destApp case_expr in
    PCFML.is_const_named "eq_sym" trm
  end  

exception EOP

let rec extract_fold_specification (trm: Constr.t) : t  =
  (* let extract_fold_specification v =
   *   if Constr.isConst v then
   *     Format.ksprintf ~f:failwith "When destructing %s, returns const!"
   *       (String.take 10_000 @@ Proof_utils.Debug.constr_to_string trm);
   *   extract_fold_specification v in *)      
  match Constr.kind trm with
  | Constr.App (trm , [| typ; proof |]) when
      Constr.isConst trm && String.equal (Names.Constant.to_string (fst (Constr.destConst trm)))  "TLC.LibTactics.rm" ->
    extract_fold_specification proof
  | Constr.App (trm, [| typ; vl; prop; proof; vl'; proof_eq |]) when PCFML.is_const_named "eq_ind" trm ->
    extract_fold_specification proof
  | Constr.App (trm, args) when PCFML.is_const_named "reflexive_proper" trm ->
    let proof = args.(Array.length args - 1) in
    extract_fold_specification proof
  | Constr.App (trm, [|
    pre; credits; hla;  hlw; hlt; hra; hrg; hrt; proof
  |]) when PCFML.is_xsimpl_lr_cancel_same trm ->
    extract_fold_specification proof
  | Constr.App (trm, [| a; q1; q2; hla; nc; proof |]) when PCFML.is_xsimpl_lr_qwand trm ->
    let (name, ty, proof) = Constr.destLambda proof in
    extract_fold_specification proof
  | Constr.App (trm, [| hla; hrg; haffine; proof |]) when PCFML.is_xsimpl_lr_hgc_nocredits trm ->
    extract_fold_specification proof    
  | Constr.App (trm, args (* [| ty; vl; prop; proof; vl'; proof_vl_eq_vl'; |] *)) when PCFML.is_const_named "eq_ind_r" trm ->
    let proof = args.(3) in
    extract_fold_specification proof
  | Constr.App (trm, [|
    ty;
    vl;
    prop;
    proof;
    vl';
    proof_vl_eq_vl';
  |]) when PCFML.is_const_named "eq_ind_r" trm ->
    extract_fold_specification proof
  | Constr.App (trm, [|
    post_1;
    post_2;
    pre;
    proof_of_post_1;
    proof_of_post_2;
  |]) when PCFML.is_himpl_hand_r trm ->
    (try ignore @@ extract_fold_specification proof_of_post_1 with EOP -> ());
    extract_fold_specification proof_of_post_2

  | Constr.App (trm, [|
    new_pre;
    pre;
    post;
    proof_pre_impl_new_pre;
    proof_new_pre_impl_post
  |]) when PCFML.is_himpl_trans trm ->
    (try ignore @@ extract_fold_specification proof_pre_impl_new_pre with EOP -> ());
    extract_fold_specification proof_new_pre_impl_post
  | Constr.App (trm, [|
    pre_frame_a;  pre_frame_b; post;
    proof
  |]) when PCFML.is_himpl_frame_r trm ->
    extract_fold_specification proof
  | Constr.App (trm, [|
    prop;
    pre;
    post;
    proof
  |]) when PCFML.is_himpl_hstar_hpure_l trm ->
    let (proof_binding_name, proof_binding_ty, proof) = Constr.destLambda proof in
    extract_fold_specification proof
  | Constr.App (trm, [| pre; post; proof |]) when PCFML.is_xsimpl_lr_exit_nogc_nocredits trm ->
    extract_fold_specification proof
    (* Format.ksprintf ~f:failwith "Kaboom! new_pre: %s, old_pre: %s\nproof_1: %s\nproof_2: %s@."
     *   (String.take 10_000 (Proof_utils.Debug.constr_to_string_pretty new_pre))
     *   (String.take 10_000 (Proof_utils.Debug.constr_to_string_pretty pre))
     *   (String.take 10_000 (Proof_utils.Debug.constr_to_string proof_pre_impl_new_pre))
     *   (String.take 10_000 (Proof_utils.Debug.constr_to_string proof_new_pre_impl_post)) *)
  | Constr.App (trm, ([| pre; post; proof |] as args)) when PCFML.is_xsimpl_start trm ->
    extract_fold_specification proof
  | Constr.App (trm, [| pre; post; proof |]) when PCFML.is_hstars_simpl_start trm ->
    extract_fold_specification proof
  | Constr.App (trm, [| pre'; post_left; framed; post_right; proof |]) when PCFML.is_hstars_simpl_cancel trm ->
    extract_fold_specification proof
  | Constr.App (trm, [| pre; pre'; post; proof_pre_eq_pre'; proof |]) when PCFML.is_hstars_simpl_pick_lemma trm ->
    extract_fold_specification proof
  | Constr.App (trm, [| post; post_proof |] ) when PCFML.is_himpl_hempty_pure trm ->
    extract_fold_specification post_proof
  | Constr.App (trm, [|
    let_ty;                     (* type of value being let bound *)
    pre;                        (* current heap state at let binding *)
    let_body;                   (* lambda that returns the code of the body of the binding  *)
    let_vl;                     (* the value being bound *)
    _res_ty;                    (* type of the result of the body *)
    _res_ty_enc;                (* Enc type for the type of the result of the body *)
    _post;                      (* function that takes in the result of body and returns the post condition *)
    proof                       (* function takes a value, and a proof value equals [let_vl], producing a proof  *)
  |])
    when PCFML.is_xlet_val_lemma trm ->
    let (let_binding_name, let_binding_ty, proof) = Constr.destLambda proof in
    let (eq_prf_name, eq_prf_ty, proof) = Constr.destLambda proof in
    extract_fold_specification proof
  | Constr.App (trm, [|
    _res_ty;
    _res_ty_enc;
    pre;
    code;
    post;
    proof
  |]) when PCFML.is_xmatch_lemma trm ->
    extract_fold_specification proof
  | Constr.App (trm, [|
    exists_ty; exists_binding;
    pre;
    post;
    proof
  |]) when PCFML.is_himpl_hexists_r trm ->
    extract_fold_specification proof
  | Constr.App (trm, [|
    pre;                        (* current heap state at current program point *)
    code;                       (* code of rest of program *)
    _res_ty; _res_ty_enc;       (* result type, result type encoding  *)
    post;                       (* post condition (parameterised by value of result type) *)
    proof                       (* proof of rest *)
  |]) when PCFML.is_mkstruct_erase trm ->
    extract_fold_specification proof
  | Constr.App (trm, [| ty; post; pre; proof |]) when PCFML.is_himpl_hforall_r trm ->
    let (binding, ty, proof) = Constr.destLambda proof in
    extract_fold_specification proof
  | Constr.App (trm, [|
    binding_ty; enc_binding_ty;
    pre;
    ret_ty; enc_ret_ty;
    post;
    value_code;
    rest_code;
    proof
  |]) when PCFML.is_xlet_trm_cont_lemma trm ->
    extract_fold_specification proof
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
    (try ignore @@ extract_fold_specification proof_fun with EOP -> ());
    extract_fold_specification proof
  | Constr.App (case, args) when is_case_of_eq_sym case ->
    let (_, _, _, _, _, case_expr, branches) = Constr.destCase case in
    let (names, body) = branches.(0) in
    let proof =
      Iter.repeat ()
      |> Iter.fold_while
           (fun v () ->
              if Constr.isLambda v then
                let (_, _, v) = Constr.destLambda v in
                v, `Continue
              else
                v, `Stop
           ) body in
    extract_fold_specification proof
  | Constr.App (trm, [| ty |]) when PCFML.is_xsimpl_lr_refl_nocredits trm ->
    raise EOP
  | Constr.App (trm, [| ret_ty; enc_ret_ty; post; heaplet |]) when PCFML.is_xdone_lemma trm ->
    raise EOP
  | Constr.App (trm, [| heaplet |]) when PCFML.is_himpl_refl trm ->
    raise EOP
  | Constr.App (trm, [| ty; enc_ty; vl; pre; post; proof |]) when PCFML.is_xval_lemma trm ->
    raise EOP
  | Constr.App (trm, _) when Constr.isVar trm ->
    raise EOP
  | Constr.App (trm, args) ->
    Format.ksprintf ~f:failwith
      "extract_fold_specification received App of %s (%s) to %d args\n%s@."
      (String.take 400_000 (Proof_utils.Debug.constr_to_string trm)) (Proof_utils.Debug.tag trm)
      (Array.length args)
      (Array.to_string (fun v -> "{" ^ String.take 40_000 (Proof_utils.Debug.constr_to_string v) ^ "}") args)
  | Constr.Lambda (name, ty, proof) ->
    extract_fold_specification proof
  | _ ->
    Format.ksprintf ~f:failwith
      "extract_fold_specification received %s"
      (String.take 4000_000 (Proof_utils.Debug.constr_to_string trm))

  
let analyse (trm: Constr.t) : t =
  let oc = open_out "/tmp/epic.txt" in
  Fun.protect ~finally:(fun () -> close_out_noerr oc) begin fun () ->
    output_string oc (Proof_utils.Debug.constr_to_string trm);
  end;
  let oc = open_out "/tmp/epic-pretty.txt" in
  Fun.protect ~finally:(fun () -> close_out_noerr oc) begin fun () ->
    output_string oc (Proof_utils.Debug.constr_to_string_pretty trm);
  end;
  match Constr.kind trm with
  | Constr.App (trm, args) when is_const_wp_fn trm && Array.length args > 0 ->
    let _initial_args = 
      Array.to_iter args |> Iter.find_map (fun trm ->
        match Constr.kind trm with
        | Constr.App (trm, args) when Constr.isVar trm ->
          Some args
        | _ ->
          None
      ) in
    let wp = args.(Array.length args - 1) in

    let _fspec = extract_fold_specification wp in

    failwith "lol"
  | _ -> 
    failwith ("lol " ^ Proof_utils.Debug.tag trm)
  
