[@@@warning "-23"]
open Containers
module AH = Ast_helper
module AT = Asttypes

module Log = (val Logs.src_log (Logs.Src.create ~doc:"Extracts ocaml programs from proof terms" "analysis.extract"))

let debug pp =
  if Configuration.print_proof_extraction ()
  then Log.debug (fun f -> pp f)
  else ()

let () = Printexc.register_printer (function Failure e -> Some e | _ -> None)

let loc v = Location.{txt=v; loc=none} 

let pvar s = AH.Pat.var (loc s)

let lid s = Longident.Lident s
let const v = AH.Exp.constant v

let pconst v = AH.Pat.constant v
let str_const v = const (Parsetree.Pconst_string (v, Location.none, None))
let int_const v = const (Parsetree.Pconst_integer (string_of_int v, None))
let pstr_const v = pconst (Parsetree.Pconst_string (v, Location.none, None))
let pint_const v = pconst (Parsetree.Pconst_integer (string_of_int v, None))
let var v =
  let id = if String.contains v '.'
    then Longident.unflatten (String.split_on_char '.' v)
    else None in
  AH.Exp.ident (loc (Option.value ~default:(lid v) id))

let fun_ args body =
  List.fold_left
    (fun body arg -> AH.Exp.fun_ AT.Nolabel None arg body)
    body
    (List.rev args)

let lowercase s =
  let start, stop = String.take_drop 1 s in
  String.lowercase_ascii start ^ stop

let normalize = function
  | "TLC.LibList.app" -> "@"
  | "TLC.LibListZ.length" -> "List.length"
  | s -> lowercase s

let extract_sym s =
  match String.drop (String.length "symbol_") s |> String.split_on_char '_' with
  | [sym; id] -> (sym,id)
  | _ -> Format.ksprintf ~f:failwith "unexpected format for symbol value %s" s

let sym_of_raw = Longident.Ldot (Ldot (Lident "Sisyphus_tracing", "Symbol"), "of_raw")
let rec encode_expr_as_pat (expr: Lang.Expr.t) : Parsetree.pattern =
  match expr with
  | `Tuple vls ->
    AH.Pat.tuple (List.map encode_expr_as_pat vls)
  | `Var v when String.prefix ~pre:"symbol_" v ->
    AH.Pat.construct (loc (Longident.Ldot (Lident "Sisyphus_tracing", "Symbol"))) (Some (pstr_const v))
  | `Var v -> pvar v
  | `Int n -> pint_const n
  | `Constructor (f, []) ->
    AH.Pat.construct (loc (lid f)) None
  | `Constructor (f, [arg]) ->
    AH.Pat.construct (loc (lid f)) (Some (encode_expr_as_pat arg))

  | `Constructor (f, args) ->
    AH.Pat.construct (loc (lid f)) (Some (AH.Pat.tuple @@ List.map encode_expr_as_pat args))
  | `App (_, _)
  | `Lambda (_, _) ->
    Format.ksprintf ~f:failwith "found use of unsupported expression %s in pattern context" (Lang.Expr.show expr)

let rec encode_expr (expr: Lang.Expr.t) : Parsetree.expression =
  match expr with
  | `Tuple [vl] ->
    encode_expr vl
  | `Tuple vls ->
    AH.Exp.tuple (List.map encode_expr vls)
  | `Var v when String.prefix ~pre:"symbol_" v ->
    let (sym, id) = extract_sym v in
    AH.Exp.apply
      (AH.Exp.ident (loc sym_of_raw))
      [ Nolabel, AH.Exp.tuple [AH.Exp.constant (Pconst_integer (id, None));
                                          AH.Exp.constant (Pconst_string (sym, Location.none, None))] ]
  | `Var v -> var v
  | `App (f, args) ->
    AH.Exp.apply (var (normalize f)) (List.map (fun e -> (AT.Nolabel, encode_expr e)) args)
  | `Lambda (args, body) ->
    let args = List.map (function
      | `Tuple params -> AH.Pat.tuple (List.map Fun.(pvar % fst) params)
      | `Var (v, _) -> pvar v) args in
    fun_ args (encode_expr body)
  | `Int n -> int_const n
  | `Constructor (f, []) ->
    AH.Exp.construct (loc (lid f)) None
  | `Constructor (f, [arg]) ->
    AH.Exp.construct (loc (lid f)) (Some (encode_expr arg))

  | `Constructor (f, args) ->
    AH.Exp.construct (loc (lid f)) (Some (AH.Exp.tuple @@ List.map encode_expr args))

let rec contains_symexec (trm: Proof_term.t) : bool =
  match trm with
  | Proof_term.CaseFalse -> false
  | Proof_term.XDone _ -> false
  | Proof_term.HimplHandR (_, l1, l2)
  | Proof_term.HimplTrans (_, _, l1, l2) ->
    contains_symexec l1 || contains_symexec l2
  | Proof_term.Lambda (_, _, rest) ->
    contains_symexec rest
  | Proof_term.AuxVarApp _
  | Proof_term.VarApp _ -> 
    failwith "attempt to call contains symexec on Variable Application term"
  | Proof_term.CharacteristicFormulae { args; pre; proof } -> contains_symexec proof
  | Proof_term.AccRect { proof={ proof; _ }; _ } -> contains_symexec proof
  | Proof_term.Refl -> false
  | Proof_term.XIfVal _
  | Proof_term.XLetFun _
  | Proof_term.XLetVal _ 
  | Proof_term.XLetTrmCont _
  | Proof_term.XMatch _ 
  | Proof_term.XApp _ 
  | Proof_term.XVal _  -> true
  | Proof_term.CaseADT {cases; _} ->
    List.exists (fun (_name,_args, rest) -> contains_symexec rest) cases
  | Proof_term.CaseBool {if_true; if_false; _} ->
    contains_symexec if_true || contains_symexec if_false

(** [extract_xmatch_cases n trm] extracts [n] xmatch cases from [trm].

    The general structure of a proof term used to analyse a match
   construct is with an xmatch lemma at the root, and then a subproof
   consistent of a sequence of `himplhandr` lemmas, one for each case,
   with the final `himplhandr` being terminated with an xdone lemma by
   contradiction (this doesn't correspond to anything in the program,
   but rather is required in the proof to capture the exhaustiveness
   of the match so we ignore it). *)
let extract_xmatch_cases n trm =
  let rec extract_eq acc trm =
    match trm with
    | Proof_term.Lambda (_, `Eq (_, left, right), rest) ->
      (left,right,rest)
    | Proof_term.Lambda (_, _, rest) ->
      extract_eq acc rest
    | _ ->
      Format.ksprintf ~f:failwith "extract_eq: found unsupported proof term %s" (String.take 1000 ([%show: Proof_term.t] trm)) in
  let rec loop n acc trm =
    match trm with
    | Proof_term.HimplHandR (inv, l, r) ->
      let acc =
        let vl = extract_eq [] l in
        vl :: acc in
      let n = n - 1 in
      if n > 0
      then loop n acc r
      else n, acc
    | Proof_term.Lambda (_, _, rest) ->
      loop n acc rest

    | Proof_term.CaseFalse
    | Proof_term.Refl -> n, acc

    | Proof_term.HimplTrans (_, _, l1, l2) ->
      let n, acc = loop n acc l1 in
      if n > 0
      then loop n acc l2
      else n, acc
    | _ ->
      Format.ksprintf ~f:failwith "extract_xmatch_cases: found unsupported proof term %s"
        (String.take 1000 ([%show: Proof_term.t] trm)) in
  loop n [] trm |> snd |> List.rev


let rec wrap_with_invariant_check (pre: Proof_term.sym_heap) ~then_ =
  match pre with
  | [] -> then_ ()
  | `Invariant expr :: t ->
    AH.Exp.sequence (encode_expr expr) (wrap_with_invariant_check t ~then_)

(** [find_next_program_binding_name trm] when given a proof term,
   calculates the next lambda that binds a variable with an
   OCaml-representable type.

   Sometimes symbolic execution steps in a proof use lambda subterms
   to name the values they instantiate, and in these cases, this
   function is useful for "peeking" into the proof term to work out an
   appropriate name. *)
let rec find_next_program_binding_name (trm: Proof_term.t) =
  match trm with
  | Proof_term.Lambda (name, `Ty _, _) -> name
  | Proof_term.Lambda (_, _, rest) -> 
    find_next_program_binding_name rest
  | Proof_term.HimplTrans (_, _, l1, l2) ->
    begin match  contains_symexec l1, contains_symexec l2 with
    | true, false -> find_next_program_binding_name l1
    | false, true -> find_next_program_binding_name l2
    | true, true -> failwith "found impossible situation - HimplTrans with symbolic execution on both branches...."
    | false, false -> raise Not_found
    end
  | _ -> raise Not_found
  
let rec extract ?replacing (trm: Proof_term.t) =
  debug (fun f -> f "extract %s@." (Proof_term.tag trm));
  let extract trm = extract ?replacing trm in
  match trm with
  | Proof_term.XLetVal { pre; binding_ty; let_binding=(var, _); eq_binding; value; proof } ->
    wrap_with_invariant_check pre ~then_:begin fun () ->
      AH.Exp.let_ AT.Nonrecursive [
        AH.Vb.mk (pvar var) (encode_expr value)
      ] (extract proof)
    end
  | Proof_term.XMatch {
    value;
    pre;
    proof
  } ->
    let cases = extract_xmatch_cases (List.length value) proof
                |> List.group_by ~hash:(fun (v, _, _) -> Hash.poly v) ~eq:(fun (v, _, _) (v', _, _) -> Equal.poly v v') in
    if not Int.(List.length cases = 1) then
      Format.ksprintf ~f:failwith "found unsupported match expression on multiple values?";
    let cases = List.hd cases in
    let match_vl : Lang.Expr.t = List.hd cases |> fun (vl, _, _) -> vl in
    wrap_with_invariant_check pre ~then_:begin fun () ->
      AH.Exp.match_ (encode_expr match_vl)
        (List.map (fun (_, pat, rest) ->
           AH.Exp.case (encode_expr_as_pat pat)
             (extract rest)
         ) cases)
    end
  | Proof_term.HimplTrans (_, _, l1, l2) ->
    begin match  contains_symexec l1, contains_symexec l2 with
    | true, false -> extract l1
    | false, true -> extract l2
    | true, true -> failwith "found impossible situation - HimplTrans with symbolic execution on both branches...."
    | false, false -> AH.Exp.construct (loc (lid "()")) None
    end
  | Proof_term.Lambda (_, _, rest) -> extract rest
  | Proof_term.XLetTrmCont {
    pre; binding_ty; value_code;
    proof=Proof_term.XApp { proof } (* TODO: make this more elegant.... *)
  } ->
    let var = find_next_program_binding_name proof in
    wrap_with_invariant_check pre ~then_:begin fun () ->
      AH.Exp.let_ AT.Nonrecursive [
        AH.Vb.mk (pvar var) (encode_expr value_code)
      ] (extract proof)
    end

  | Proof_term.XApp { application; pre; fun_pre; proof_fun=AccRect { prop_type; proof=proof_fun; vl; args }; proof } ->
    if contains_symexec proof then
      wrap_with_invariant_check pre ~then_:begin fun () ->
        AH.Exp.sequence
          (extract_recursive_function ~application ~prop_type ~proof:proof_fun ~vl ~args)
          (extract proof)
      end
    else
      wrap_with_invariant_check pre ~then_:begin fun () ->
        extract_recursive_function ~application ~prop_type ~proof:proof_fun ~vl ~args
      end 
  | Proof_term.XApp { application=_; pre; fun_pre=_; proof_fun=CharacteristicFormulae {proof=proof_fun; _}; proof } ->
    (* idea is that when we have a auxiliary helper, we don't emit the
       application, but instead leave it to the proof by the helper. *)
    if contains_symexec proof then
      wrap_with_invariant_check pre ~then_:begin fun () ->
        AH.Exp.sequence
          (extract proof_fun)
          (extract proof)
      end
    else
      wrap_with_invariant_check pre ~then_:begin fun () ->
        extract proof_fun
      end 
  | Proof_term.XApp { application=_; pre; fun_pre=_; proof_fun=AuxVarApp (_, _, proof_fun); proof } ->
    (* idea is that when we have a auxiliary helper, we don't emit the
       application, but instead leave it to the proof by the helper. *)
    if contains_symexec proof then
      wrap_with_invariant_check pre ~then_:begin fun () ->
        AH.Exp.sequence
          (extract proof_fun)
          (extract proof)
      end
    else
      wrap_with_invariant_check pre ~then_:begin fun () ->
        extract proof_fun
      end 
  | Proof_term.XApp { application=(f, args); pre; fun_pre; proof_fun; proof } ->
    let expr =
      if Option.exists (String.equal f) replacing
      then begin match proof_fun with
        | Proof_term.VarApp (_, params) ->
          let args = List.filter_map (function `Expr e -> Some e |`ProofTerm _ -> None ) params in
          encode_expr (`App ("loop", args))
        | _ ->
          Format.ksprintf ~f:failwith "found non-var app application of recursive call.... %s"
            (String.take 1000 ([%show: Proof_term.t] trm))
      end
      else encode_expr (`App (f, args)) in
    if contains_symexec proof then
      wrap_with_invariant_check pre ~then_:begin fun () ->
        AH.Exp.sequence expr (extract proof)
      end
    else
      wrap_with_invariant_check pre ~then_:begin fun () ->
        expr
      end
  | Proof_term.XVal { pre; value_ty; value } ->
    wrap_with_invariant_check pre ~then_:begin fun () ->
      encode_expr value
    end
  | Proof_term.XDone _ ->
    (* encode_expr (`Constructor ("()", [])) *)
    AH.Exp.apply (var "failwith") [AT.Nolabel, str_const "invalid assumptions"]
  | Proof_term.AuxVarApp (_, _, proof) ->
    extract proof
  | Proof_term.XLetFun { pre; proof } ->
    extract proof
  | Proof_term.CharacteristicFormulae { args; pre; proof } -> extract proof

  | Proof_term.VarApp _ 
  | Proof_term.Refl 
  | Proof_term.HimplHandR (_, _, _) ->
    AH.Exp.unreachable ()
  | Proof_term.XIfVal { pre; cond; if_true; if_false } ->
    wrap_with_invariant_check pre ~then_:begin fun () ->
      AH.Exp.ifthenelse (encode_expr cond)
        (extract if_true)
        (Some (extract if_false))
    end
  | Proof_term.CaseBool { cond; if_true; if_false } ->
    AH.Exp.ifthenelse (encode_expr cond)
      (extract if_true)
      (Some (extract if_false))
  | Proof_term.CaseADT {vl; cases} ->
    let encode_case (name, args, rest) =
      AH.Exp.case (encode_expr_as_pat (`Constructor (name, List.map (fun (v, _) -> `Var v) args)))
        (extract rest) in
    AH.Exp.match_ (encode_expr vl)
      (List.map encode_case cases)
  | Proof_term.CaseFalse ->
    AH.Exp.assert_ (encode_expr (`Constructor ("false", [])))
  | _ ->
    Format.ksprintf ~f:failwith "found unsupported proof term %s" (String.take 1000 ([%show: Proof_term.t] trm))
and extract_recursive_function
      ~application:(f, _)
      ~prop_type
      ~proof:{ x; ty_x; h_acc; ty_h_acc; ih_x; ty_ih_x; proof }
      ~vl
      ~args =
  let params = ty_ih_x.params |> List.filter_map (function (v, `Ty _) -> Some v | _ -> None) |> List.tl in

  AH.Exp.let_ AT.Recursive [
    AH.Vb.mk
      (pvar "loop")
      (fun_ (pvar x :: List.map pvar params) (extract ~replacing:f proof))
  ] @@

  AH.Exp.apply (var "loop")
    (List.filter_map
       (function `ProofTerm _ -> None
               | `Expr e -> Some (AT.Nolabel, encode_expr e))
       (`Expr vl :: args)
    )

let pp_ast = Format.to_string Pprintast.expression
