[@@@warning "-23"]
open Containers
module AH = Ast_helper
module AT = Asttypes

let () = Printexc.register_printer (function Failure e -> Some e | _ -> None)

(* let failwith = Format.ksprintf ~f:failwith *)

let extract_xmatch_cases n trm =
  let rec extract_eq trm =
    match trm with
    | Proof_term.Lambda (_, `Eq (_, `Var var, vl), rest) ->
      (var, vl, rest)
    | Proof_term.Lambda (_, _, rest) ->
      extract_eq rest
    | _ -> Format.ksprintf ~f:failwith "extract_eq: found unsupported proof term %s" (String.take 1000 ([%show: Proof_term.t] trm)) in
  let rec loop n acc trm =
    match trm with
    | Proof_term.HimplHandR (inv, l, r) ->
      let acc =
        let vl = extract_eq l in
        vl :: acc in
      let n = n - 1 in
      if n > 0
      then loop n acc r
      else n, acc
    | Proof_term.Lambda (_, _, rest) ->
      loop n acc rest
    | Proof_term.Refl -> n, acc
    | Proof_term.HimplTrans (_, _, l1, l2) ->
      let n, acc = loop n acc l1 in
      if n > 0
      then loop n acc l2
      else n, acc
    | _ ->
      Format.ksprintf ~f:failwith "extract_xmatch_cases: found unsupported proof term %s" (String.take 1000 ([%show: Proof_term.t] trm)) in
  loop n [] trm |> snd |> List.rev 

let loc v = Location.{txt=v; loc=none}

let pvar s = AH.Pat.var (loc s)
let lid s = Longident.Lident s

let const v = AH.Exp.constant v
let pconst v = AH.Pat.constant v
let str_const v = const (Parsetree.Pconst_string (v, Location.none, None))
let int_const v = const (Parsetree.Pconst_integer (string_of_int v, None))
let pstr_const v = pconst (Parsetree.Pconst_string (v, Location.none, None))
let pint_const v = pconst (Parsetree.Pconst_integer (string_of_int v, None))


let var v = AH.Exp.ident (loc (lid v))

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
  | s -> lowercase s

let extract_sym s = String.drop (String.length "symbol_") s
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
  | `Constructor (f, args) ->
    AH.Pat.construct (loc (lid f)) (Some (AH.Pat.tuple @@ List.map encode_expr_as_pat args))
  | `App (_, _)
  | `Lambda (_, _) ->
    Format.ksprintf ~f:failwith "found use of unsupported expression %s in pattern context" (Lang.Expr.show expr)

let rec encode_expr (expr: Lang.Expr.t) : Parsetree.expression =
  match expr with
  | `Tuple vls ->
    AH.Exp.tuple (List.map encode_expr vls)
  | `Var v when String.prefix ~pre:"symbol_" v ->
    AH.Exp.apply
      (AH.Exp.ident (loc sym_of_raw))
      [Nolabel, AH.Exp.constant (Pconst_integer (extract_sym v, None))]
  | `Var v -> var v
  | `App (f, args) ->
    AH.Exp.apply (var (normalize f)) (List.map (fun e -> (AT.Nolabel, encode_expr e)) args)
  | `Lambda (args, body) ->
    let args = List.map (function `Tuple params -> AH.Pat.tuple (List.map Fun.(pvar % fst) params)
                                | `Var (v, _) -> pvar v) args in
    fun_ args (encode_expr body)
  | `Int n -> int_const n
  | `Constructor (f, []) ->
    AH.Exp.construct (loc (lid f)) None
  | `Constructor (f, args) ->
    AH.Exp.construct (loc (lid f)) (Some (AH.Exp.tuple @@ List.map encode_expr args))

let rec contains_symexec (trm: Proof_term.t) : bool =
  match trm with
  | Proof_term.HimplHandR (_, l1, l2)
  | Proof_term.HimplTrans (_, _, l1, l2) ->
    contains_symexec l1 || contains_symexec l2
  | Proof_term.Lambda (_, _, rest) ->
    contains_symexec rest
  | Proof_term.VarApp _ -> failwith "lol"
  | Proof_term.CharacteristicFormulae { args; pre; proof } -> contains_symexec proof
  | Proof_term.AccRect { proof={ proof; _ }; _ } -> contains_symexec proof
  | Proof_term.Refl -> false
  | Proof_term.XLetVal _ 
  | Proof_term.XLetTrmCont _
  | Proof_term.XMatch _ 
  | Proof_term.XApp _ 
  | Proof_term.XVal _ 
  | Proof_term.XDone _ -> true


let rec wrap_with_invariant_check (pre: Proof_term.sym_heap) ~then_ =
  match pre with
  | [] -> then_ ()
  | `Invariant expr :: t ->
    AH.Exp.sequence (encode_expr expr) (wrap_with_invariant_check t ~then_)

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
                |> List.group_by ~hash:(fun (v, _, _) -> Hash.string v) ~eq:(fun (v, _, _) (v', _, _) -> String.equal v v') in
    if not Int.(List.length cases = 1) then
      Format.ksprintf ~f:failwith "found unsupported match expression on multiple values?";
    let cases = List.hd cases in
    let match_vl : Lang.Expr.t = List.hd cases |> fun (vl, _, _) -> `Var vl in
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
  | Proof_term.XApp { application=(f, args); pre; fun_pre; proof_fun; proof } ->
    let expr =
      if Option.exists (String.equal f) replacing
      then begin match proof_fun with
        | Proof_term.VarApp (_, params) ->
          let args = List.filter_map (function `Expr e -> Some e |`ProofTerm _ -> None ) params in
          encode_expr (`App ("loop", args))
        | _ ->
          Format.ksprintf ~f:failwith "found non-var app application of recursive call.... %s" (String.take 1000 ([%show: Proof_term.t] trm))
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
    AH.Exp.apply (var "failwith") [AT.Nolabel, str_const "invalid assumptions"]
  | Proof_term.CharacteristicFormulae { args; pre; proof } -> extract proof
  | Proof_term.VarApp _ 
  | Proof_term.Refl 
  | Proof_term.HimplHandR (_, _, _) ->
    AH.Exp.unreachable ()
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
