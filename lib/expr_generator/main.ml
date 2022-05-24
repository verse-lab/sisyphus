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


let handle_constants () =
  let consts = Expr_generator.Collector.collect_constants 3 10 steps in
  List.iter (fun x -> print_endline @@ Expr_generator.Collector.Constants.show x) consts;
  consts

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


let extend_env env fname ty: Expr_generator.Expgen.env =
  fun str ->
  try env str with
  | Failure _  when String.equal fname str -> ty

let handle_pats env =
  let pats = Expr_generator.Patgen.pat_gen env steps in
  List.iter (fun x -> print_endline @@ Expr_generator.Expgen.show_tag_pat x) pats;
  pats

let handle_funcs env consts =
  let open Expr_generator.Expgen in
  let add_to_map map = function
    | `Func fname ->
      let input_types, ret_type = env fname in
      let ty = fname, input_types in
      TypeMap.update ret_type (function Some ls -> Some (ty :: ls) | None -> Some [ty]) map
    | _ -> map
  in

  let init = TypeMap.of_list Lang.Type.[
      Int, [("-", [Int; Int]);  ("+", [Int; Int])]
    ]
  in
  let map: (string * Lang.Type.t list) list TypeMap.t = List.fold_left add_to_map init consts in
  List.iter (fun (ty, funcs) ->
      print_endline @@ "--" ^ Lang.Type.show ty;
      let print_funcs (fname, inputs) =
        print_endline @@ fname ^ ": " ^ (List.fold_on_map ~f:Lang.Type.show ~reduce:(^) "" inputs);
      in
      List.iter print_funcs funcs;
    )
    (TypeMap.to_list map);

  map

let update_binding env ty vl =
  TypeMap.update ty
    (fun v ->
       Option.value ~default:[] v
       |> List.cons vl
       |> Option.some)
    env


let add_ps_consts consts ty_map =
  let add_type type_map = function
    | `Int i  as e  ->
      TypeMap.update (Int) (function Some  ls -> Some (e :: ls) | None -> Some [e]) type_map
    | _ -> type_map
  in
  List.fold_left add_type ty_map consts

let () =
  let open Lang.Type in

  let vars: (string * Lang.Type.t) list = [("l", List (Var "A")); ("init", Var "A"); ("i", Int)] in 
  let consts = TypeMap.of_list [(Int, [`Int 1])] in
  let consts_in_script = handle_constants () in
  let consts = List.fold_left
      (fun acc x ->
         match x with
           `Int i -> update_binding acc Int (`Int i)
         | _ -> acc
      ) consts
      consts_in_script
  in
  let consts = List.fold_left (fun acc (vname, ty) ->
      update_binding acc ty (`Var vname)
    ) consts vars
  in

  (* let show_const = function | `Int i -> string_of_int i | `Var str -> str in *)
  (* let show_consts = List.fold_on_map ~f:show_const ~reduce:(fun a x -> a ^ x ^ ", ") "" in *)
  (* List.iter (fun (k, v) -> print_endline @@ Lang.Type.show k ^ ": " ^ show_consts v) (Expr_generator.Expgen.TypeMap.to_list consts); *)

  let pats = handle_pats env in
  let pats = Expr_generator.Patgen.get_pat_type_map env pats in
  (* List.iter (fun (k, v) -> print_endline @@ Lang.Type.show k; List.iter (fun x -> print_endline @@ Expr_generator.Patgen.show_pat x) v) (Expr_generator.Expgen.TypeMap.to_list pats); *)

  let funcs = handle_funcs env consts_in_script in

  let ctx : Expr_generator.Expgen.ctx = { consts; pats; funcs } in
  let max_fuel = 3 in
  let fuel = max_fuel in
  let exps = Expr_generator.Expgen.gen_exp ctx env ~max_fuel ~fuel (List (Var "A")) in

  print_endline "Results";
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
  List.iter (fun x -> print_endline @@ Lang.Expr.show x ^ "\n") exps;

  ()
