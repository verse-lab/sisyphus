open Containers

let drop_last ls =
  let rec loop acc = function
    | [] | [_] -> List.rev acc
    | h :: t -> loop (h :: acc) t in
  loop [] ls

let combine_rem xz yz =
  let rec loop acc xz yz =
    match xz, yz with
    | [], [] -> List.rev acc, None
    | _ :: _ as xz, [] -> List.rev acc, Some (Either.Left xz)
    | [], (_ :: _ as yz) -> List.rev acc, Some (Either.Right yz)
    | x :: xz, y :: yz -> loop ((x, y) :: acc) xz yz in
  loop [] xz yz

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

let find_spec t const =
  Proof_context.search t [
    true, Search.(GlobSearchLiteral (GlobSearchString "spec"));
    true, Search.(GlobSearchLiteral
                    (GlobSearchSubPattern (Vernacexpr.InConcl, false, Pattern.PRef (Names.GlobRef.ConstRef const))))
  ] |> function
  | [(Names.GlobRef.ConstRef name, _, ty)] -> (name, ty)
  | [_] -> failwith "failure finding specification for function application: non-constant name for reference"
  | [] -> failwith "failure finding specification for function application: could not find an appropriate specification"
  | _ -> failwith "failure finding specification for function application: ambiguity - more than one valid specification found"

type constr = Constr.constr
let pp_constr fmt v =
  Format.pp_print_string fmt @@ Proof_debug.constr_to_string v

let show_preheap = [%show: [> `Empty | `NonEmpty of [> `Impure of constr | `Pure of constr ] list ]]

let rec update_program_id_over_lambda (t: Proof_context.t)
      (`Lambda (_, body): [ `Lambda of Lang.Expr.typed_param list * Lang.Expr.t Lang.Program.stmt ])  =
  let rec loop (body: Lang.Expr.t Lang.Program.stmt) = match body with
    | `Match (_, cases) -> 
      t.current_program_id <- Lang.Id.incr t.current_program_id;
      List.iter (fun (_, _, body) -> loop body) cases
    | `Write (_, _, _, body) ->
      t.current_program_id <- Lang.Id.incr t.current_program_id;
      loop body
    | `LetLambda (_, lambody, body) ->
      update_program_id_over_lambda t lambody;
      loop body
    | `LetExp (_, _, _, body) ->
      t.current_program_id <- Lang.Id.incr t.current_program_id;
      loop body
    | `EmptyArray ->
      t.current_program_id <- Lang.Id.incr t.current_program_id
    | `Value _ ->
      t.current_program_id <- Lang.Id.incr t.current_program_id in
  loop body


let rec symexec (t: Proof_context.t) env (body: Lang.Expr.t Lang.Program.stmt) =
  (* Format.printf "current program id is %s: %s@."
   *   (t.Proof_context.current_program_id |>  Lang.Id.show)
   *   (Lang.Program.show_stmt_line Lang.Expr.print body |> String.replace ~sub:"\n" ~by:" "); *)
  match body with
  | `LetLambda (name, body, rest) ->
    symexec_lambda t env name body rest
  | `LetExp (pat, rewrite_hint, body, rest) ->
    t.current_program_id <- Lang.Id.incr t.current_program_id;
    begin match body with
    | `App ("Array.make", [_; _]) ->
      symexec_alloc t env pat rest
    | `App (_, prog_args)
      when List.exists (function
        |`Var v -> Proof_env.is_pure_lambda env v
        | _ -> false
      ) prog_args ->
      symexec_higher_order_pure_fun t env pat rewrite_hint prog_args rest      
    | `App (_, args)
      when List.exists (function
        |`Var v -> Proof_env.has_definition env v (* StringMap.mem v env *)
        | _ -> false
      ) args ->
      symexec_higher_order_fun t env pat rewrite_hint args body rest
    | _ -> symexec_opaque_let t env pat rewrite_hint body rest
    end
  | `Match (prog_expr, cases) ->
    t.current_program_id <- Lang.Id.incr t.current_program_id;
    symexec_match t env prog_expr cases
  | `EmptyArray ->
    t.current_program_id <- Lang.Id.incr t.current_program_id;
    Proof_context.append t "xvalemptyarr."
  | `Write _ -> failwith "don't know how to handle write"
  | `Value _ -> failwith "don't know how to handle value"
and symexec_lambda t env name body rest =
  let fname = Proof_context.fresh ~base:name t in
  let h_fname = Proof_context.fresh ~base:("H" ^ name) t in
  Proof_context.append t "xletopaque %s %s." fname h_fname;
  let env = Proof_env.add_lambda_def t env name body in
  update_program_id_over_lambda t body;
  symexec t env rest
and symexec_alloc t env pat rest =
  let prog_arr = match pat with
    | `Tuple _ -> failwith "found tuple pattern in result of array.make"
    | `Var (var, _) -> var in
  let arr = Proof_context.fresh ~base:(prog_arr) t in
  let data = Proof_context.fresh ~base:"data"  t in
  let h_data = Proof_context.fresh ~base:("H" ^ data) t in
  Proof_context.append t "xalloc %s %s %s." arr data h_data;
  let env = Proof_env.add_proof_binding env ~proof_var:arr ~program_var:prog_arr in
  symexec t env rest
and symexec_opaque_let t env pat _rewrite_hint body rest =
  let prog_var = match pat with
    | `Tuple _ ->
      failwith (Format.sprintf "TODO: implement handling of let _ = %a expressions" Lang.Expr.pp body)
    | `Var (var, _) -> var in
  let var = Proof_context.fresh ~base:(prog_var) t in
  let h_var = Proof_context.fresh ~base:("H" ^ var) t in
  Proof_context.append t "xletopaque %s %s."  var h_var;
  let env = Proof_env.add_proof_binding env ~proof_var:var ~program_var:prog_var in
  symexec t env rest
and symexec_match t env prog_expr cases =
  (* emit a case analysis to correspond to the program match    *)
  (* for each subproof, first intro variables using the same names as in the program *)
  let sub_proof_vars = 
    List.map (fun (_, args, _) ->
      List.map (fun (base, _) -> Proof_context.fresh ~base t) args
    ) cases in
  let case_intro_strs =
    List.map (String.concat " ") sub_proof_vars
    |> String.concat " | "  in
  (* preserve the equality of the program expression *)
  let eqn_var = Proof_context.fresh ~base:("H_eqn") t in
  (* emit a case analysis: *)
  Proof_context.append t "case %a as [%s] eqn:%s."
    Printer.pp_expr prog_expr case_intro_strs eqn_var;
  (* now, handle all of the sub proofs *)
  List.iter (fun ((_, args, rest), proof_args) ->
    (* start each subproof with an xmatch to determine the appropriate branch *)
    Proof_context.append t "- xmatch.";
    (* update env with bindings for each of the new program vars *)
    let env =
      List.fold_left (fun env ((program_var, _), proof_var) ->
        Proof_env.add_proof_binding env ~proof_var ~program_var
      ) env (List.combine args proof_args) in
    (* now emit the rest *)
    symexec t env rest;
    (* dispatch remaining subgoals by the best method: *)
    while (Proof_context.current_subproof t).goals |> List.length > 0 do 
      Proof_context.append t "{ admit. }";
    done;
  ) (List.combine cases sub_proof_vars)
and symexec_higher_order_pure_fun t env pat rewrite_hint prog_args rest =
  (* work out the name of function being called and the spec for it *)
  let (f_name, raw_spec) =
    (* extract the proof script name for the function being called *)
    let (_, post) = Proof_cfml.extract_cfml_goal (Proof_context.current_goal t).ty in
    let f_app = Proof_cfml.extract_x_app_fun post in
    (* use Coq's searching functionality to work out the spec for the function *)
    find_spec t f_app in
  let (params, invariant, spec) = Proof_cfml.extract_spec raw_spec in

  (* work out the parameters to instantiate *)
  let evar_params =
    params
    (* drop implicits from parameters *)
    |> Proof_utils.drop_implicits f_name
    (* drop concrete arguments *)
    |> List.drop (List.length prog_args)
    (* last parameter is the concretisation of the pure function *)
    |> drop_last in

  (* instantiate evars, and collect variables to clear at end *)
  let clear_vars =
    List.fold_left (fun to_clear (name, _) ->
      let name = Format.to_string Pp.pp_with @@ Names.Name.print name in
      let ty = Proof_context.fresh ~base:("ty_" ^ name ) t in
      Proof_context.append t "evar (%s: Type)." ty;
      let name = Proof_context.fresh ~base:name t in
      Proof_context.append t "evar (%s: %s)." name ty;
      to_clear
      |> List.cons ty
      |> List.cons name
    ) [] evar_params |> List.rev in

  (* emit xapp call *)
  let observation_id, fn_body =
    List.find_map (function
        `Var v -> Proof_env.find_pure_lambda_def env v (* StringMap.find_opt v env |> Option.flat_map (Option.if_ Program_utils.is_pure) *)
      | _ -> None) prog_args
    |> Option.get_exn_or "invalid assumptions" in

  Proof_context.append t "xapp (%s %s %s %s)."
    (Names.Constant.to_string f_name)
    (List.map (Printer.show_expr) prog_args |> String.concat " ")
    (List.map (fun (name, _) -> "?" ^ Format.to_string Pp.pp_with (Names.Name.print name))
       evar_params
     |> String.concat " ")
    (Printer.show_lambda fn_body);

  (* solve immediate subgoal of xapp automatically. *)
  Proof_context.append t "sep_solve.";

  (* TODO: repeat based on goal shape, not no goals   *)
  (* any remaining subgoals we assume we can dispatch automatically by eauto. *)
  while List.length (Proof_context.current_subproof t).goals > 1 do
    Proof_context.append t "eauto.";
  done;

  (* finally, clear any evars we introduced at the start  *)
  Proof_context.append t "clear %s." (String.concat " " clear_vars);

  (* destructuring of arguments *)
  begin
    match pat with
    | `Var _ -> ()
    | `Tuple vars ->
      (* if we have a tuple, then we need to do some extra work *)
      let vars = List.map (fun (name, _) ->
        Proof_context.fresh ~base:name t
      ) vars in
      let h_var = Proof_context.fresh ~base:("H" ^ String.concat "" vars) t in
      (* first, emit a xdestruct to split the tuple output - [hvar] remembers the equality *)
      Proof_context.append t "xdestruct %s %s." (String.concat " " vars) h_var;
      (* next, use a user-provided rewrite hint to simplify the equality  *)
      begin match rewrite_hint with
      | Some rewrite_hint ->
        Proof_context.append t "rewrite %s in %s." rewrite_hint h_var;
      | None ->
        failwith "tuple destructuring with functions requires a rewrite hint."
      end;
      (* finally, split the simplified equality on tuples into an equality on terms  *)
      let split_vars = List.map (fun var -> Proof_context.fresh ~base:("H" ^ var) t) vars in
      Proof_context.append t "injection %s; intros %s."
                            h_var (String.concat " " @@ List.rev split_vars);
  end;
  symexec t env rest
and symexec_higher_order_fun t env pat rewrite_hint prog_args body rest =
  let (pre, post) = Proof_cfml.extract_cfml_goal (Proof_context.current_goal t).ty in
  (* work out the name of function being called and the spec for it *)
  let (f_name, raw_spec) =
    (* extract the proof script name for the function being called *)
    let f_app = Proof_cfml.extract_x_app_fun post in
    (* use Coq's searching functionality to work out the spec for the function *)
    find_spec t f_app in
  let _vc = Specification.build_verification_condition t (Proof_env.env_to_defmap env) f_name in

  print_endline @@ Printf.sprintf "lemma is %s, spec is %s"
                     (Names.Constant.to_string f_name)
                     (Proof_debug.constr_to_string raw_spec);
  let (params, invariant, spec) = Proof_cfml.extract_spec raw_spec in
  let explicit_params = Proof_utils.drop_implicits f_name params in
  let (_, _f_args) = Proof_cfml.extract_app_full t post in

  let param_bindings, remaining = combine_rem explicit_params _f_args in
  match remaining with
  | Some (Right _) | None | Some (Left [])  ->
    Format.ksprintf ~f:failwith "TODO: found function application %a with no invariant?" Pp.pp_with (Names.Constant.print f_name )
  | Some (Left (_ :: _ :: _)) ->
    Format.ksprintf ~f:failwith "TODO: found function application %a with multiple invariants"
      Pp.pp_with (Names.Constant.print f_name )
  | Some (Left [inv]) ->

    let name_to_string name = Format.to_string Pp.pp_with (Names.Name.print name) in
    print_endline @@
    Printf.sprintf "params are: %s" 
      (List.map (fun (name, _) -> name_to_string name) params |> String.concat ", ");

    print_endline @@
    Printf.sprintf "invariants are: %s" 
      (List.map (fun (_, sg) -> Proof_debug.constr_to_string sg) invariant |> String.concat ", ");


    print_endline @@
    Printf.sprintf "real params are: %s" 
      (List.map (fun (name, _) -> name_to_string name) explicit_params |> String.concat ", ");


    print_endline @@ Format.sprintf "args: (%s)"@@
    (List.map (fun (exp, _) -> Lang.Expr.show exp) _f_args |> String.concat ", ");

    failwith ("TODO: implement handling of let _ = " ^ Format.to_string Lang.Expr.pp body ^ " expressions")

let generate t (prog: Lang.Expr.t Lang.Program.t) =
  Proof_context.append t {|xcf.|};
  let pre, _ = Proof_cfml.extract_cfml_goal (Proof_context.current_goal t).ty in

  (* handle pure preconditions *)
  begin match pre with
  | `NonEmpty ls ->
    let no_pure = List.count (function `Pure _ -> true | _ -> false) ls in
    let pat = 
      Int.range 1 no_pure
      |> Iter.map (fun i -> "H" ^ Int.to_string i)
      |> Iter.concat_str in
    Proof_context.append t "xpullpure %s." pat;
  | _ -> ()
  end;
  symexec t Proof_env.initial_env prog.body;
  Proof_context.extract_proof_script t

