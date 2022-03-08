[@@@warning "-8-9-11-26-27-39"]

open Containers


module Proof = Proof_parser.Proof
module Command = Proof_parser.Command

module StringMap = Map.Make(String)
type 'a str_map = 'a StringMap.t
let pp_str_map f fmt vl = StringMap.pp String.pp f fmt vl
let equal_str_map f f1 f2 = StringMap.equal f f1 f2

type proof_context = {
  coq_context: Proof.pure_expression list;
  pure_facts: Program.Expr.expr list;
  pure: Proof.pure_expression list;
  spatial: Proof.pure_expression str_map
} [@@deriving show, eq]

let of_context (pre: Proof.sep_spec) =
  let pure, spatial =
    List.partition_filter_map (function Proof.Pure pure ->  `Left pure
                                      | Proof.Spatial (PointsTo (spat, vl)) -> `Right (spat,vl)) pre in
  let spatial = StringMap.of_list spatial in
  {pure_facts=[];coq_context=[];pure;spatial}

let true_proof = ref []
let ___debug_pop n = true_proof := List.drop n !true_proof
let ___debug_next_command () = List.hd !true_proof

let is_pure_fn : Program.Statements.slc list -> bool = List.for_all (function `Expr _ -> true |`ArrayAssign _ -> false)

let fresh_fn ctx = "f"

let func fn = Proof.Explicit (fn, (Proof.Type ["func"]))

let rec vars : Program.Statements.pattern -> 'a = function
    Program.Statements.Var var -> [var]
  | Program.Statements.Tuple elts -> List.concat_map vars elts
  | Program.Statements.Constructor (_, args) -> List.concat_map vars args
  | Program.Statements.Wildcard -> []

let rec instantiate_pat : Program.Statements.pattern -> Proof.pure_expression = function
  | Program.Statements.Var v -> Proof.Var v
  | Program.Statements.Tuple pat -> Proof.Tuple (List.map instantiate_pat pat)

let rec convert_to_pure_expression: Program.Expr.expr -> Proof.pure_expression = function
  | Program.Expr.TupleExpr elts -> Proof.Tuple (List.map convert_to_pure_expression elts)
  | Program.Expr.Var v -> Proof.Var v
  | Program.Expr.ListExpr lexp -> convert_list_to_pure_expression lexp
  | Program.Expr.IntExpr iexp -> convert_int_expression_to_pure_expression iexp
and convert_int_expression_to_pure_expression =  function
  | Program.Expr.Int i -> Proof.Int i
  | Program.Expr.IntVar v -> Proof.Var v
  | Program.Expr.Add (l, r) -> Proof.Add (convert_int_expression_to_pure_expression l, convert_int_expression_to_pure_expression r)
and convert_list_to_pure_expression = function
  | Program.Expr.ListVar v -> Proof.Var v
  | Program.Expr.AppList ("cons", [h; t]) -> Proof.Cons (convert_to_pure_expression h, convert_to_pure_expression t)
  | Program.Expr.Nil -> Proof.Var "nil"
  | elt -> failwith @@ "got unknown pattern: " ^ [%derive.show: Program.Expr.list_expr] elt

let poly_type = Proof.Type ["A"]

let lookup_fun (ctx: proof_context) (ls: Program.Expr.expr) = Proof.Var "s"

let convert_pure_lambda: Program.Statements.pattern -> string -> Program.Expr.expr -> Proof.pure_expression =
  fun acc_pat vl_pat body ->
  let params, rest =
    match acc_pat with
    | Program.Statements.Var v -> [Proof.Ident v; Proof.Explicit (vl_pat, poly_type)], Fun.id
    | Program.Statements.Tuple [Var l; Var r] ->
      let rest body = Proof.DestructurePair (l, r, "pair", body) in
      [Proof.Ident "pair"; Proof.Explicit (vl_pat, poly_type)], rest in
  Proof.Lambda (params, Proof.FunctionalSpec (rest (convert_to_pure_expression body)))




let rec generate (ctx: proof_context) (new_program: Program.Statements.t list) =
  let handle_comment ctx text =
    let text = String.trim text in
    match () with
    | _ when String.prefix ~pre:"xpull " text ->
      let [name;app] = String.drop (String.length "xpull ") text
                       |> String.split_on_char ','
                       |> List.map String.trim in
      let dispatcher = "[intros " ^ name ^ "; apply " ^ app ^ " in " ^ name ^ "]" in
      let rule = Proof.Xpull [dispatcher] in
      let [lemma], pure = List.take_drop 1 ctx.pure in
      let ctx = {ctx with pure; coq_context = lemma :: ctx.coq_context } in
      (ctx, [rule])
    (* | _ when String.prefix ~pre:"destruct_with " text ->
     *   let [rewrite_rule; ops] = String.split ~by:"==>" text
     *                             |> List.map String.trim in
     *   let ops = String.split_on_char ';' ops |> List.map Program_parser.parse_expr in
     *   {ctx with pure_facts=ops @ ctx.pure_facts} *)
    | _ -> failwith @@ "don't know how to handle Comment: " ^ text in
  match new_program with
  | [] -> []
  | h::t -> match h with
    | `Comment text ->
      let ctx, steps = handle_comment ctx text in
      ___debug_pop (List.length steps);
      let rest = generate ctx t in
      steps @ rest
    | `Fold ((out_pat, acc_pat, vl_pat, body, init, ls) as args) ->
      print_endline @@ [%derive.show: Program.Statements.pattern * Program.Statements.pattern * string *
Program.Statements.slc list * Program.Expr.expr * Program.Expr.expr] args;

      if is_pure_fn body then begin
        let fn = fresh_fn ctx in
        let acc_vars = vars acc_pat in
        let Some (`Expr body) = List.last_opt body in
        let let_step =
          let acc_params = List.map (fun v -> Proof.Ident v) acc_vars in
          let vl_param = [Proof.Explicit (vl_pat, poly_type)] in
          let f_app = (fn, [instantiate_pat acc_pat; Proof.Var vl_pat] ) in
          Proof.Xlet (Some (func fn, acc_params @ vl_param, f_app, convert_to_pure_expression body), [ "auto" ], ["{ xgo*. }"]) in
        ___debug_pop 1;
        let fold_step =
          Proof.Xapp (
            Some (Proof.Predicate ("fold_spec", [
              Proof.Var "_"; Proof.Var "_"; Proof.Var "_"; Proof.Var "_"; convert_to_pure_expression ls; Proof.Var "f0__";
              convert_to_pure_expression init; lookup_fun ctx ls;
              convert_pure_lambda acc_pat vl_pat body
            ])),
            ["auto"],
            ["{ admit. }"; "{ admit. }"]) in
        ___debug_pop 1;

        let rest = generate ctx t in
        let_step :: fold_step :: rest
      end
    else failwith "don't know how to handle Fold"
    | `MatchDeferred _ -> failwith "don't know how to handle MatchDeferred"
    | `Length _ -> failwith "don't know how to handle Length"
    | `AllocArray _ -> failwith "don't know how to handle AllocArray"
    | `MatchPure _ -> failwith "don't know how to handle MatchPure"
    | `ListFold _ -> failwith "don't know how to handle ListFold"

    | `Iteri _ -> failwith "don't know how to handle Iteri"
    | `Expr _ -> failwith "don't know how to handle Expr"
    | `EmpArray -> failwith "don't know how to handle EmpArray"
    | `ArrayAssign _ -> failwith "don't know how to handle ArrayAssign"
    | `LetPure _ -> failwith "don't know how to handle LetPure"


let update_proof 
  (formal_params: Proof.param list) 
  (pre: Proof.sep_spec)
  (post: Proof.param * Proof.sep_spec)
  (new_program: Program.Statements.func) =
  let ctx = of_context pre in
  let (fn_name, args, body) = new_program in
  ___debug_pop 1;
  try generate ctx body with
  | exn ->
    print_endline "FAILED: you should generate:";
    print_endline @@ [%derive.show: Proof.proof_step] (___debug_next_command ());
    raise exn
  

let proof_repair (old_proof: Proof.t) (new_program: Program.Statements.func) : Proof.t =
  let formal_params = old_proof.formal_params in
  let spec = old_proof.spec in
  let pre = old_proof.pre in
  let post = old_proof.post in
  let proof = Proof.Xcf :: update_proof formal_params pre post new_program in
  {
    directives = [Command.Comment "TODO: FOR USER TO ADD SOMETHING HERE"];
    name=old_proof.name;
    formal_params;
    spec;
    pre;
    post;
    proof;
  }


let () =
  let [program] = IO.with_in "../../resources/seq_to_array/updated.ml" Program_parser.parse_channel in
  print_endline @@ [%derive.show: Program.Statements.func] program;
  let old_proof = IO.with_in "../../resources/seq_to_array/proof_original.v" Proof_parser.parse_channel in

  let proof = IO.with_in "../../resources/seq_to_array/proof_updated.v" Proof_parser.parse_channel in
  true_proof := proof.proof;
  print_endline @@ [%derive.show: Proof.t ] proof;

  (* print_endline @@ [%derive.show: Proof.t ] proof; *)

  (* let proof = proof_repair old_proof program in
   * print_endline @@ [%derive.show: Proof.t ] proof; *)

  ()
