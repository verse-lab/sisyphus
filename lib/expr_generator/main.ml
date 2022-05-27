open Containers

module TypeMap = Expr_generator.Expgen.TypeMap

let steps =
  let proof_str = IO.with_in "../../resources/seq_to_array/Verify_seq_to_array_old.v" IO.read_all in
  let dir = "../../_build/default/resources/seq_to_array" in
  let module Ctx =
    Coq.Proof.Make(struct
      let verbose = false
      let libs = [
        Coq.Coqlib.make
          ~path:(Fpath.of_string dir |> Result.get_exn)
          "Proofs"
      ]
    end) in

  let parsed_script = Proof_parser.Parser.parse (module Ctx) proof_str in
  print_endline @@ Proof_spec.Script.show_steps parsed_script.proof;
  parsed_script.proof


let env : Expr_generator.Expgen.env =
  let open Lang.Type in
  let tA = Var "A" in
  function
  | "++" -> [List tA; List tA], List tA
  | "make" -> [Int; tA], List tA
  | "length" -> [List tA], Int
  | "drop" -> [Int; List tA], List tA
  | "-" -> [Int; Int], Int
  | "+" -> [Int; Int], Int
  | _ -> failwith "env typing unknown"


let get_ctx steps ~from_id ~to_id ~env ~ints ~vars ~funcs : Expr_generator.Expgen.ctx =
  let consts, funcs = Expr_generator.Typemap_utils.get_consts_and_funcs steps ~from_id ~to_id ~env ~ints ~vars ~funcs in
  let pats = Expr_generator.Typemap_utils.get_pats steps ~from_id ~to_id ~env in
  { consts; pats; funcs}

let () =
  let open Lang.Type in
  let ints = [(Int, [`Int 1])] in
  let vars: (string * Lang.Type.t) list = [("l", List (Var "A")); ("init", Var "A"); ("i", Int)] in
  let funcs = Lang.Type.[
      Int, [("-", [Int; Int]);  ("+", [Int; Int])]
    ] in

  let ctx = get_ctx steps ~from_id:0 ~to_id:10 ~env ~ints ~vars ~funcs in
  let max_fuel = 3 in
  let fuel = max_fuel in
  let exps = Expr_generator.Expgen.gen_exp ctx env ~max_fuel ~fuel (List (Var "A")) in

  (* Generate expressions for heap assertion*)
  print_endline "Results for Heap Assertion";
  print_endline @@ string_of_int @@ List.length exps;

  let expr: Lang.Expr.t = `App ("++", [
      `App ("make", [
          `App ("+", [`Var "i"; `Int 1])
        ; `Var "init"
        ])
    ; `App ("drop", [
          `App ("+", [`Var "i"; `Int 1])
         ; `Var "l"
        ])
    ]) in

  print_endline @@ string_of_bool @@ List.exists (fun x -> Lang.Expr.equal expr x) exps;


  (* Generate expressions for pure invariant*)
  print_endline "Results for Pure Invariant";
  List.iter (fun (vname, ty) ->
      let exps = Expr_generator.Expgen.gen_exp ctx env ~max_fuel ~fuel ty in
      print_endline @@ vname ^ ": " ^ string_of_int (List.length exps);
    ) vars;
  ()
