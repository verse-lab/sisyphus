open Containers

let drop_last ls =
  let rec loop acc = function
    | [] | [_] -> List.rev acc
    | h :: t -> loop (h :: acc) t in
  loop [] ls


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

let rec symexec t env (body: Lang.Expr.t Lang.Program.stmt) =
  match body with
  | `LetLambda (name, body, rest) ->
    symexec_lambda t env name body rest
  | `LetExp (pat, rewrite_hint, body, rest) ->
    begin match body with
    | `App ("Array.make", [_; _]) ->
      symexec_alloc t env pat rest
    | `App (_, prog_args)
      when List.exists (function
        |`Var v -> StringMap.find_opt v env |> Option.exists Program_utils.is_pure
        | _ -> false
      ) prog_args ->
      symexec_higher_order_pure_fun t env pat rewrite_hint prog_args rest      
    | `App (_, args)
      when List.exists (function
        |`Var v -> StringMap.mem v env
        | _ -> false
      ) args ->
      symexec_higher_order_fun t env pat rewrite_hint args body rest
    | _ -> symexec_opaque_let t env pat rewrite_hint body rest
    end
  | `Match (prog_expr, cases) ->
    symexec_match t env prog_expr cases
  | `EmptyArray ->
    Proof_context.append t "xvalemptyarr."
  | `Write _ -> failwith "don't know how to handle write"
  | `Value _ -> failwith "don't know how to handle value"
and symexec_lambda t env name body rest =
  let fname = Proof_context.fresh ~base:name t in
  let h_fname = Proof_context.fresh ~base:("H" ^ name) t in
  Proof_context.append t "xletopaque %s %s." fname h_fname;
  let env = StringMap.add name body env in
  symexec t env rest
and symexec_alloc t env pat rest =
  let prog_arr = match pat with
    | `Tuple _ -> failwith "found tuple pattern in result of array.make"
    | `Var (var, _) -> var in
  let arr = Proof_context.fresh ~base:(prog_arr) t in
  let data = Proof_context.fresh ~base:"data"  t in
  let h_data = Proof_context.fresh ~base:("H" ^ data) t in
  Proof_context.append t "xalloc %s %s %s." arr data h_data;
  symexec t env rest
and symexec_opaque_let t env pat _rewrite_hint body rest =
  let prog_var = match pat with
    | `Tuple _ ->
      failwith ("TODO: implement handling of let _ = " ^ Format.to_string Lang.Expr.pp body ^ " expressions")
    | `Var (var, _) -> var in
  let var = Proof_context.fresh ~base:(prog_var) t in
  let h_var = Proof_context.fresh ~base:("H" ^ var) t in
  Proof_context.append t "xletopaque %s %s."  var h_var;
  symexec t env rest
and symexec_match t env prog_expr cases =
  (* emit a case analysis to correspond to the program match    *)
  (* for each subproof, first intro variables using the same names as in the program *)
  let case_intro_strs =
    List.map (fun (_, args, _) ->
      List.map (fun (name, _) ->
        Proof_context.fresh ~base:(name) t
      ) args
      |> String.concat " "
    ) cases in
  (* preserve the equality of the program expression *)
  let eqn_var = Proof_context.fresh ~base:("H_eqn") t in
  (* emit a case analysis: *)
  Proof_context.append t "case %a as [%s] eqn:%s."
    Printer.pp_expr prog_expr
    (String.concat " | " case_intro_strs)
    eqn_var;

  (* now, handle all of the sub proofs *)
  List.iter (fun (_, _, rest) ->
    (* start each subproof with an xmatch to determine the appropriate branch *)
    Proof_context.append t "- xmatch.";
    (* now emit the rest *)
    symexec t env rest;
    (* dispatch remaining subgoals by the best method: *)
    while (Proof_context.current_subproof t).goals |> List.length > 0 do 
      Proof_context.append t "{ admit. }";
    done;
  ) cases
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
  let fn_body =
    List.find_map (function
        `Var v -> StringMap.find_opt v env |> Option.flat_map (Option.if_ Program_utils.is_pure)
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
  (* Proof_context.pretty_print_current_goal t;
   * Proof_context.debug_print_current_goal t; *)
  let vc = Specification.build_verification_condition t env in
  print_endline @@ Specification.show_verification_condition vc;
  let (pre, post) = Proof_cfml.extract_cfml_goal (Proof_context.current_goal t).ty in
  print_endline @@ show_preheap pre;
  (* work out the name of function being called and the spec for it *)
  let (f_name, raw_spec) =
    (* extract the proof script name for the function being called *)
    let f_app = Proof_cfml.extract_x_app_fun post in
    (* use Coq's searching functionality to work out the spec for the function *)
    find_spec t f_app in

  print_endline @@ Printf.sprintf "lemma is %s, spec is %s"
                     (Names.Constant.to_string f_name)
                     (Proof_debug.constr_to_string raw_spec);
  let (params, invariant, spec) = Proof_cfml.extract_spec raw_spec in

  let name_to_string name = Format.to_string Pp.pp_with (Names.Name.print name) in

  print_endline @@
  Printf.sprintf "params are: %s" 
    (List.map (fun (name, _) -> name_to_string name) params |> String.concat ", ");

  print_endline @@
  Printf.sprintf "invariants are: %s" 
    (List.map (fun (_, sg) -> Proof_debug.constr_to_string sg) invariant |> String.concat ", ");

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
  symexec t StringMap.empty prog.body;
  Proof_context.extract_proof_script t

