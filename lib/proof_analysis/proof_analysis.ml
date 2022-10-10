[@@@warning "-26-23"]
open Containers
module Embedding = Proof_term_embedding
module StringMap = Map.Make(String)
module StringSet = Set.Make(String)
module PCFML = Proof_utils.CFML

module Log = (val Logs.src_log (Logs.Src.create ~doc:"Analyses proof terms to generate executable specs" "analysis"))


type t = Parsetree.expression
type lambda_env = (Lang.Id.t * [ `Lambda of Lang.Expr.typed_param list * Lang.Expr.t Lang.Program.stmt ]) StringMap.t
type obs = Dynamic.Concrete.context * Dynamic.Concrete.heap_context
type invariant_spec = string * string list
type invariant = Lang.Expr.t * Lang.Expr.t list
type 'a tester = 'a -> bool

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

type constr = Constr.t
let pp_constr fmt c = Format.pp_print_string fmt (Proof_utils.Debug.constr_to_string_pretty c)

type 'a string_map = 'a StringMap.t
let pp_string_map f fmt vl =
  StringMap.pp
    ~pp_start:(fun fmt () -> Format.fprintf fmt "{@[<hov 2>@ ")
    ~pp_stop:(fun fmt () -> Format.fprintf fmt "@ @]}")
    ~pp_arrow:(fun fmt () -> Format.fprintf fmt " ~>@ ")
    ~pp_sep:(fun fmt () -> Format.fprintf fmt ",@ ")
    String.pp f fmt vl

type string_set = StringSet.t
let pp_string_set fmt vl =
  StringSet.pp
    ~pp_start:(fun fmt () -> Format.fprintf fmt "{@[<hov 2>@ ")
    ~pp_stop:(fun fmt () -> Format.fprintf fmt "@ @]}")
    ~pp_sep:(fun fmt () -> Format.fprintf fmt ",@ ")
    String.pp fmt vl

type env = {
  bindings: (string * Lang.Type.t option) list;
  (** [bindings] is the typing environment - an ordered list of
      variable names, and optionally their types if they can be
      represented. *)
  values: [`Expr of Lang.Expr.t | `Term of constr] string_map;
  (** [values] is a definition environment - when we find terms
      of the form [((fun (x: _) => <body>) vl)], we add [x] to [bindings]
      and [x -> vl] to [values] and evaluate [<body>]. *)

  bound_variables: string_set;
  (** [bound_variables] is a string set used to track variables bound
     in the current context, and thereby avoid naming clashes.

      Whenever a new binding is added, this set must be updated. *)


  lambdas: (string, unit) Hashtbl.t;
  (** [lambdas] is a hash set of all the function symbols used in
      applications seen so far in the proof term. This is used by
      {!Proof_test.with_function_definitions} to add any anonymous
      lambdas used in the application to the testing function. *)

  in_let_fun_context: bool;
  (** [in_let_fun_context] is used as a flag to track whether we are
      currently searching for the proof binding for an auxiliary
      helper.

      Typically, xlet_fun_lemma (used to reason about local helpers)
      takes a proof term that proves the post condition using a
      separating wand to encode the semantics of the body of the
      helper:

      {[ \[`Code ... PRE (...) POST (...)] \-* POST ]}.

      We want to track when function calls may be using these kind of
      internal helpers, so we need to retrieve the binding used to
      reference the helper's body, and we do that by tracking when we
      are in a let fun context and assuming that the closest
      [hwand_hpure_r_intro] is naming this internal function.

      Thank you for listening to my ted talk...
  *)

  auxiliary_function_lemmas: string_set;
  (** [auxiliary_function_lemmas] is a set of the names of any
      lemmas which are used to refer to the semantics of helper
      functions. In these cases, any var applications using these
      lemmas will have the last term being a proof term that we will
      want to analyse for constructing testing assertions within the
      body of the auxiliary function. *)
}
(** [env] represents the current analysis env that is maintained as we
    traverse proof terms. *)
[@@deriving show]

let empty_env vars = {
  bindings=[];
  values = StringMap.empty;
  bound_variables=StringSet.of_iter vars;
  lambdas=Hashtbl.create 10;
  in_let_fun_context=false;
  auxiliary_function_lemmas=StringSet.empty
}

let used_functions env = Hashtbl.keys_list env.lambdas

let rel_ty env ind =
  let ind = ind - 1 in
  List.nth env.bindings ind
  |> snd
  |> Option.get_exn_or "attempted to construct invalid typ"

let rel_expr env ind =
  let ind = ind - 1 in
  match (List.nth_opt env.bindings ind) with
  | None ->
    Format.ksprintf ~f:failwith "attempted to access index %d in env of length %d; env is %s"
      ind
      (List.length env.bindings)
      ([%show: (string * Lang.Type.t option) list] env.bindings)
  | Some (v, _) -> v

let is_in_let_fun_context env =
  env.in_let_fun_context

let add_binding ?ty var env =
  let var =
    if not (StringSet.mem var env.bound_variables)
    then var
    else
      let rec loop i =
        let var = var ^ "_" ^ string_of_int i in
        if not (StringSet.mem var env.bound_variables)
        then var
        else loop (i + 1) in
      loop 0 in
  var, {env with bindings = (var, ty) :: env.bindings; bound_variables=StringSet.add var env.bound_variables}

let add_definition var value env =
  {env with values=StringMap.add var value env.values}

let with_auxiliary_lemma var env =
  {env with auxiliary_function_lemmas = StringSet.add var env.auxiliary_function_lemmas}

let with_let_fun_context ~ctx env =
  {env with in_let_fun_context = ctx}

let is_auxiliary_lemma env var =
  StringSet.mem var env.auxiliary_function_lemmas

let record_fun_usage env var =
  Hashtbl.add env.lambdas var ()

let extract_expr_opt env vl =
  try Some (`Expr (PCFML.extract_expr ~rel:(rel_expr env) vl))  with
  | e ->
    None

let extract_proof_value env ty =
  try `Eq (PCFML.unwrap_eq ~rel:(rel_expr env) ty) with
  | e ->
    try  `Expr (PCFML.extract_expr ~rel:(rel_expr env) ty)  with
    | e ->
      try `Ty (PCFML.extract_typ ~rel:(rel_ty env) ty) with
      | e ->
        `Proof (Proof_utils.Debug.constr_to_string ty)

let extract_typ_from_proof_value = function
  | (`Ty vl) as p_vl -> Some vl, p_vl
  | _ as p_vl -> None, p_vl

let rec extract_sym_heap env c =
  (* Format.printf "extract_sym_heap of %s@.%s@."
   *   (Proof_utils.Debug.constr_to_string_pretty c)
   *   (Proof_utils.Debug.constr_to_string c); *)
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
  | Constr.App (fn, [| f; args |]) when Proof_utils.is_const_eq "CFML.SepLifted.Trm_apps" fn && (Constr.isConst f || Constr.isRel f) ->
    let f =
      if Constr.isConst f
      then Constr.destConst f |> fst |> Names.Constant.to_string
      else Constr.destRel f |> rel_expr env in
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
      let name, env = add_binding ?ty name env in
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
        let ret_name, env = add_binding ~ty ret_name env in
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
  let name, env = add_binding ?ty name env in
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
        ([%show: (string * Lang.Type.t option) list] env.bindings);
  and drop_lambdas env vl =
    match Constr.kind vl with
    | Constr.Prod ({Context.binder_name; _}, ty, vl) ->
      let binder_name = name_to_string binder_name in
      let ty, proof_ty = extract_proof_value env ty |> extract_typ_from_proof_value in
      let binder_name, env = add_binding ?ty binder_name env in
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
        ([%show: (string * Lang.Type.t option) list] env.bindings)
  and drop_eq env vl = 
    match Constr.kind vl with
    | Constr.App (eq, [| ty; vl; case |]) when Proof_utils.is_coq_eq eq ->
      let vl = PCFML.extract_expr ~rel:(rel_expr env) vl in
      let case = PCFML.extract_expr ~rel:(rel_expr env) case in
      (vl, case)
    | _ ->
      Format.ksprintf ~f:failwith "expected a logical equality, but received %s (in env %s)"
        (Proof_utils.Debug.constr_to_string_pretty vl)
        ([%show: (string * Lang.Type.t option) list] env.bindings)
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

(** [reify_proof_term env trm] traverses a Coq Constr.t and builds a
    simplified representation of type {!Proof_term.t}.  *)
let rec reify_proof_term (coq_env: Environ.env) (env: env) (trm: Constr.t) : Proof_term.t  =
  match Constr.kind trm with
  | Constr.App (acc_rect, args) when PCFML.is_const_named "Acc_rect" acc_rect ->
    extract_fold_specification coq_env env trm
  | Constr.App (trm , [| typ; proof |]) when Proof_utils.is_const_eq "TLC.LibTactics.rm" trm ->
    reify_proof_term coq_env env proof
  | Constr.App (trm, [| typ; vl; prop; proof; vl'; proof_eq |]) when PCFML.is_const_named "eq_ind" trm ->
    reify_proof_term coq_env env proof
  | Constr.App (trm, args) when PCFML.is_const_named "eq_ind" trm && Array.length args > 6 ->
    let proof_term  = args.(3) in
    let args = Array.sub args 6 (Array.length args - 6) in
    let env, proof_term =
      let unwrap_arg arg =
        extract_expr_opt env arg
        |> Option.get_lazy (fun () -> `Term arg) in
      Array.fold (fun (env, proof) arg ->
        let ({Context.binder_name; _}, ty, proof) = Constr.destLambda proof in
        let binder_name = name_to_string binder_name in
        let ty, proof_ty = extract_proof_value env ty |> extract_typ_from_proof_value in
        let arg = unwrap_arg arg in
        let binder_name, env = add_binding ?ty binder_name env in
        let env = add_definition binder_name arg env in
        (env, proof)
      ) (env, proof_term) args in
    reify_proof_term coq_env env proof_term
  | Constr.App (trm, args) when PCFML.is_const_named "reflexive_proper" trm ->
    let proof = args.(Array.length args - 1) in
    reify_proof_term coq_env env proof
  | Constr.App (trm, [|
    pre; credits; hla;  hlw; hlt; hra; hrg; hrt; proof
  |]) when PCFML.is_xsimpl_lr_cancel_same trm ->
    reify_proof_term coq_env env proof
  | Constr.App (trm, [| a; q1; q2; hla; nc; proof |]) when PCFML.is_xsimpl_lr_qwand trm ->
    let ({Context.binder_name; _}, ty, proof) = Constr.destLambda proof in
    let binder_name = name_to_string binder_name in
    let ty, proof_ty = extract_proof_value env ty |> extract_typ_from_proof_value in
    let binder_name, env = add_binding ?ty binder_name env in
    Lambda ( binder_name, proof_ty,
             reify_proof_term coq_env env proof
           )
  | Constr.App (trm, [| q1; q2; hla; nc; proof |]) when PCFML.is_xsimpl_lr_qwand_unit trm ->
    reify_proof_term coq_env env proof
  | Constr.App (trm, [| hla; hrg; haffine; proof |]) when PCFML.is_xsimpl_lr_hgc_nocredits trm ->
    reify_proof_term coq_env env proof    
  | Constr.App (trm, args (* [| ty; vl; prop; proof; vl'; proof_vl_eq_vl'; |] *)) when PCFML.is_const_named "eq_ind_r" trm ->
    let proof = args.(3) in
    reify_proof_term coq_env env proof
  | Constr.App (trm, [| ty; vl; prop; proof; vl'; proof_vl_eq_vl'; |]) when PCFML.is_const_named "eq_ind_r" trm ->
    reify_proof_term coq_env env proof
  | Constr.App (trm, [| post_1; post_2; pre; proof_of_post_1; proof_of_post_2; |]) when PCFML.is_himpl_hand_r trm ->
    let pre = extract_sym_heap env pre in
    HimplHandR (
      pre,
      reify_proof_term coq_env env proof_of_post_1,
      reify_proof_term coq_env env proof_of_post_2
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
      reify_proof_term coq_env env proof_pre_impl_new_pre,
      reify_proof_term coq_env env proof_new_pre_impl_post    
    )
  | Constr.App (trm, [| pre_frame_a;  pre_frame_b; post; proof |]) when PCFML.is_himpl_frame_r trm ->
    reify_proof_term coq_env env proof
  | Constr.App (trm, [| prop; pre; post; proof |]) when PCFML.is_himpl_hstar_hpure_l trm ->
    let ({Context.binder_name=proof_binding_name;_}, ty, proof) = Constr.destLambda proof in
    let proof_binding_name = name_to_string proof_binding_name in
    let ty, proof_ty = extract_proof_value env ty |> extract_typ_from_proof_value in
    let proof_binding_name, env = add_binding ?ty proof_binding_name env in
    Lambda (
      proof_binding_name,
      proof_ty,
      reify_proof_term coq_env env proof
    )
  | Constr.App (trm, [| pre; post; proof |]) when PCFML.is_xsimpl_lr_exit_nogc_nocredits trm ->
    reify_proof_term coq_env env proof
  | Constr.App (trm, ([| pre; post; proof |] as args)) when PCFML.is_xsimpl_start trm ->
    reify_proof_term coq_env env proof
  | Constr.App (trm, [| pre; post; proof |]) when PCFML.is_hstars_simpl_start trm ->
    reify_proof_term coq_env env proof
  | Constr.App (trm, [| pre'; post_left; framed; post_right; proof |]) when PCFML.is_hstars_simpl_cancel trm ->
    reify_proof_term coq_env env proof
  | Constr.App (trm, [| pre; pre'; post; proof_pre_eq_pre'; proof |]) when PCFML.is_hstars_simpl_pick_lemma trm ->
    reify_proof_term coq_env env proof
  | Constr.App (trm, [| post; post_proof |] ) when PCFML.is_himpl_hempty_pure trm ->
    reify_proof_term coq_env env post_proof
  | Constr.App (trm, [|
    exists_ty; exists_binding;
    pre;
    post;
    proof
  |]) when PCFML.is_himpl_hexists_r trm ->
    reify_proof_term coq_env env proof
  | Constr.App (trm, [| ty; post; pre; proof |]) when PCFML.is_himpl_hforall_r trm ->
    let ({Context.binder_name=binding;_}, ty, proof) = Constr.destLambda proof in
    let binding_name = name_to_string binding in
    let ty, proof_ty = extract_proof_value env ty |> extract_typ_from_proof_value in
    let binding_name, env = add_binding ?ty binding_name env in
    Lambda (
      binding_name, proof_ty,
      reify_proof_term coq_env env proof      
    )
  | Constr.App (trm, [|
    pre;
    post;
    code;
    proof                       (* proof is a function with a binding *)
  |]) when PCFML.is_hwand_hpure_r_intro trm ->
    let ({Context.binder_name=binding;_}, ty, proof) = Constr.destLambda proof in
    let binding_name = name_to_string binding in
    let ty, proof_ty = extract_proof_value env ty |> extract_typ_from_proof_value in
    let binding_name, env = add_binding ?ty binding_name env in
    let env =
      if is_in_let_fun_context env
      then begin
        env
        |> with_auxiliary_lemma binding_name
        |> with_let_fun_context ~ctx:false
      end
      else env in
    Lambda (
      binding_name, proof_ty,
      reify_proof_term coq_env env proof
    )
  | Constr.App (trm, [|
    pre;                        (* current heap state at current program point *)
    code;                       (* code of rest of program *)
    _res_ty; _res_ty_enc;       (* result type, result type encoding  *)
    post;                       (* post condition (parameterised by value of result type) *)
    proof                       (* proof of rest *)
  |]) when PCFML.is_mkstruct_erase trm ->
    reify_proof_term coq_env env proof
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
    let let_binding_name, env = add_binding ?ty:let_binding_ty let_binding_name env in
    let ({Context.binder_name=eq_prf_name;_}, eq_prf_ty, proof) = Constr.destLambda proof in
    let eq_prf_name = name_to_string eq_prf_name in
    let eq_prf_ty, eq_prf_proof_ty = extract_proof_value env eq_prf_ty |> extract_typ_from_proof_value in
    let eq_prf_name, env = add_binding ?ty:eq_prf_ty eq_prf_name env in
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
      proof=reify_proof_term coq_env env proof;
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
      proof=reify_proof_term coq_env env proof;
    }
  | Constr.App (trm, [|
    _ret_ty;                 (* type of return type of the current function *)
    _ret_ty_enc;             (* Enc type of return type of the current function *)
    fun_body;                (* body of the function *)
    pre;                     (* lambda that returns the code of the body of the binding  *)
    _post;                   (* post-condition of the term *)
    proof;                   (* rest of proof, should be a lambda that firsts binds fun  *)
  |]) when PCFML.is_xlet_fun_lemma trm ->
    let pre = extract_sym_heap env pre in
    let env = env
              |> with_let_fun_context ~ctx:true in
    XLetFun {
      pre;
      proof=reify_proof_term coq_env env proof
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
      proof=reify_proof_term coq_env env proof
    }
  | Constr.App (trm, [|
    pre;
    _ret_ty; _enc_ret_ty;
    _post;
    _code_fst;
    _code_snd;
    proof
  |]) when PCFML.is_xseq_cont_lemma trm ->
    reify_proof_term coq_env env proof
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
    record_fun_usage env (fst application);
    XApp {
      pre=pre;
      application;
      fun_pre=fun_pre;
      proof_fun=reify_proof_term coq_env env proof_fun;
      proof=reify_proof_term coq_env env proof;
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
                let vl, env = add_binding ?ty vl env in
                let kont proof = kont (Proof_term.Lambda (
                  vl,
                  proof_ty,
                  proof
                )) in
                (kont, v, env), `Continue
              else
                (kont, v, env), `Stop
           ) ((fun x -> x), body, env) in
    kont (reify_proof_term coq_env env proof)
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
    if is_auxiliary_lemma env var
    then
      (* if it's an auxiliary lemma *)
      (* every arg but the last are specification arguments to the auxiliary  *)
      let spec_args = Array.to_iter args
                      |> Iter.take (Array.length args - 1)
                      |> Iter.map (extract_proof_value env)
                      |> Iter.map (function
                          `Expr e -> `Expr e
                        | v -> `ProofTerm ([%show: Proof_term.proof_value] v))
                      |> Iter.to_list in
      AuxVarApp (var, spec_args, reify_proof_term coq_env env args.(Array.length args - 1))
    else    
      let args = Array.to_iter args
                 |> Iter.map (extract_proof_value env)
                 |> Iter.map (function
                     `Expr e -> `Expr e
                   | v -> `ProofTerm ([%show: Proof_term.proof_value] v))
                 |> Iter.to_list in
      VarApp (var, args)
  | Constr.App (trm, args) when PCFML.is_const_wp_fn_trm trm && Array.length args > 5 ->
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
      proof=reify_proof_term coq_env env proof
    }
  | Constr.App (trm, args) ->
    Format.ksprintf ~f:failwith
      "reify_proof_term env received App of %s (%s) to %d args\n%s@."
      (String.take 4000 (Proof_utils.Debug.constr_to_string trm)) (Proof_utils.Debug.tag trm)
      (Array.length args)
      (Array.to_string (fun v -> "{" ^ String.take 40_000 (Proof_utils.Debug.constr_to_string v) ^ "}") args)
  | Constr.Lambda ({Context.binder_name;_}, ty, proof) ->
    let binder_name = name_to_string binder_name in
    let ty, proof_ty = extract_proof_value env ty |> extract_typ_from_proof_value in
    let binder_name, env = add_binding ?ty binder_name env in
    Lambda (
      binder_name,
      proof_ty,
      reify_proof_term coq_env env proof      
    )
  | _ ->
    Format.ksprintf ~f:failwith
      "reify_proof_term env received %s"
      (String.take 4000 (Proof_utils.Debug.constr_to_string trm))

and extract_fold_specification (coq_env: Environ.env) (env: env) (trm: Constr.t) : Proof_term.t =
  let (_, args) = Constr.destApp trm in
  let prop_spec = args.(2) |> extract_prop_spec env in
  let recursive_spec = args.(3) in
  let vl = PCFML.extract_expr ~rel:(rel_expr env) args.(4) in
  let oargs = args in
  let args = Iter.int_range ~start:6 ~stop:(Array.length args - 1)
             |> Iter.map (fun i -> args.(i))
             |> Iter.map (extract_proof_value env)
             |> Iter.map (function `Expr e -> `Expr e | v -> `ProofTerm ([%show: Proof_term.proof_value] v))
             |> Iter.to_list in
  Log.debug (fun f ->
    f "args to fold spec were %s (input 2 was %s)@. env is %a@."
      ([%show: [ `Expr of Lang.Expr.t
               | `ProofTerm of string ] list] args)
      (Proof_utils.Debug.constr_to_string_pretty oargs.(7))
      pp_env env)
  ;
  (* t: args.(6)  == nil & x *)
  (* init: args.(7) == init *)
  let ({Context.binder_name=rec_vl;_}, rec_vl_ty, recursive_spec) = Constr.destLambda recursive_spec in
  let rec_vl = name_to_string rec_vl in
  let rec_vl_ty, rec_vl_proof_ty = extract_proof_value env rec_vl_ty |> extract_typ_from_proof_value in
  let rec_vl, env = add_binding ?ty:rec_vl_ty rec_vl env in
  let ({Context.binder_name=h_acc;_}, ty_h_acc, recursive_spec) = Constr.destLambda recursive_spec in
  let h_acc = name_to_string h_acc in
  let h_acc_ty, h_acc_proof_ty = extract_proof_value env ty_h_acc |> extract_typ_from_proof_value in
  let h_acc, env = add_binding ?ty:h_acc_ty h_acc env in

  let ({Context.binder_name=ih_vl;_}, ih_vl_ty, recursive_spec) = Constr.destLambda recursive_spec in
  let ih_vl = name_to_string ih_vl in
  let ih_vl_prop_ty = extract_prop_type env ih_vl_ty in
  let ih_vl, env = add_binding ih_vl env in

  AccRect {
    prop_type=prop_spec;
    proof={
      x=rec_vl; ty_x=Option.get_exn_or "found invalid type" rec_vl_ty;
      h_acc=h_acc; ty_h_acc=Proof_utils.Debug.constr_to_string_pretty ty_h_acc;
      ih_x= ih_vl; ty_ih_x=ih_vl_prop_ty;
      proof=reify_proof_term coq_env env recursive_spec
    };
    vl=vl;
    args=args
  }

let unique ls = StringSet.of_list ls |> StringSet.to_list

let analyse (coq_env: Environ.env)
      (lambda_env: lambda_env)
      (obs: (Dynamic.Concrete.context * Dynamic.Concrete.heap_context))
      invariant_spec
      (trm: Constr.t)  =
  match Constr.kind trm with
  (* check that we first have a characteristic formula term at our
     proof root (these terms will always block as CFML actually uses
     axioms to encode them). *)
  | Constr.App (trm, args) when PCFML.is_const_wp_fn_trm trm && Array.length args > 0 ->
    (* the last argument to the CF is the proof of correctness that we care about *)
    let wp = args.(Array.length args - 1) in
    (* initialise the env with the invariant and any temporary functions bound  *)
    let env = empty_env (Iter.cons (fst invariant_spec) (StringMap.keys lambda_env)) in
    (* convert proof term to simplified representation *)
    let proof_term = reify_proof_term coq_env env wp in
    IO.with_out "/tmp/extracted" (fun chn -> Proof_term.pp ( Format.of_chan chn) proof_term);
    (* extract a testing function from the code *)
    let test_spec = (Proof_extraction.extract proof_term) in
    let used_functions =
      used_functions env
      |> unique
      |> List.filter_map (fun name ->
        StringMap.find_opt name lambda_env
        |> Option.map (fun (_, v) -> (name, v))) in
    Proof_test.build_test obs used_functions invariant_spec test_spec
  | _ -> failwith ("found unsupported term " ^ Proof_utils.Debug.tag trm)
  
