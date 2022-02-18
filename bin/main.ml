[@@@warning "-33"]
open Verification
open Containers
open Expr

let bool_functions = [  ]
let int_functions = [  ]
let list_functions = [
  "append", [ListTy;ListTy];
  "repeat", [IntTy; VarTy];
]

let base_vars = ["last"]
let base_bool_expressions = []
let base_int_expressions = [
  Int 2;
  Add (IntVar "i", Int 1);
  AppInt ("length", [ListExpr (ListVar "ls")])
  ; AppInt ("length", [ListExpr (ListVar "t")]);
]
let base_list_expressions = [AppList ("rev", [ListExpr (AppList ("cons", [Var "last"; ListExpr (ListVar "t")]))]); ListVar "t"; ]



let () =

  let bogus_p =
    let length var = AppInt ("length", [ListExpr (ListVar var)]) in
    let (-) l r = Sub (l, r) in
    let (=) l r = BoolExpr (IntEq (IntVar l, r)) in
    "i" = length "t" - length "ls" - length "t" in
  let bogus_e =
    let length var = AppInt ("length", [ListExpr (ListVar var)]) in
    let (++) l r = AppList ("append", [ListExpr l; ListExpr r]) in
    let repeat len vl = AppList ("repeat", [IntExpr len; Var vl]) in
    let i v = Int v in
    let (+) l r = Add (l, r) in
    ListExpr ((repeat (length "ls" + i 2) "last") ++ (repeat (i 2) "last" ++ repeat (length "t") "last")) in

  print_endline @@ Format.sprintf "P(t,i) := %a" (fun fmt vl -> Expr.pp fmt vl) bogus_p;
  print_endline @@ Format.sprintf "E(t,i) := %a" (fun fmt vl -> Expr.pp fmt vl) bogus_e;

  print_endline @@ Printf.sprintf "bogus pre-outcome: %b\n" (Verification.do_test_pure bogus_p);
  print_endline @@ Printf.sprintf "bogus outcome: %b\n" (Verification.do_test bogus_p bogus_e);

  let target_p_inner = Sub (Sub (AppInt ("length", [ListExpr (ListVar "ls")]),
                                                        AppInt ("length", [ListExpr (ListVar "t")])),
                                                   Int 2) in
  let target_p = BoolExpr (IntEq (IntVar "i", target_p_inner)) in
  let target_e = (AppList ("append", [
                   ListExpr (AppList ("repeat", [
                     IntExpr (Add ((IntVar "i"), (Int 1)));
                     Var "last"
                   ]));
                   ListExpr (AppList ("rev", [
                     ListExpr (AppList ("cons", [
                       Var "last";
                       ListExpr (ListVar "t")
                     ]))
                   ]));
                 ])) in

  assert (Verification.do_test target_p (ListExpr target_e));
  assert (Verification.do_test target_p (ListExpr target_e));
  print_endline @@ Printf.sprintf "target outcome: %b\n" (Verification.do_test target_p (ListExpr target_e));

  let init_step =
    Fun.iterate 2
      (Gen.generate_step_fixed_bools ~list_functions ~bool_functions ~int_functions)
      (base_int_expressions, base_list_expressions, base_bool_expressions, base_vars) in

  let lazy_ints, lazy_lists, _, _ =
    Gen.generate_lazy_step_fixed_bools ~list_functions ~bool_functions ~int_functions
      init_step in
  let lazy_ints = lazy_ints |> Seq.filter (fun exp -> not (Expr.contains_int_expr "i" exp) && Expr.contains_int_expr "t" exp) in

  let pos = ref 0 in
  print_endline "checking that the search space contains the pure:";
  assert (Seq.exists (fun e -> incr pos; Expr.equal_int_expr target_p_inner e) lazy_ints);
  print_endline @@ Printf.sprintf "\t - yes (%d)!" !pos;
  pos := 0;
  print_endline "checking that the search space contains the spatial:";
  assert (Seq.exists (fun e -> incr pos; Expr.equal_list_expr target_e e) lazy_lists);
  print_endline @@ Printf.sprintf "\t - yes (%d)!" !pos;

  let found_count = ref 0 in
  let ps =
    lazy_ints
    |> Seq.map (fun exp -> BoolExpr (IntEq (IntVar "i", exp)))
    |> Seq.filter Verification.do_test_pure in
    
  let es = Seq.map (fun exp -> ListExpr exp) lazy_lists
         |> Seq.filter (fun exp -> Expr.contains "i" exp || Expr.contains "t" exp) in
  Seq.flat_map (fun pure -> Seq.map (fun spatial -> (pure, spatial)) es) ps
  |> Seq.filter (fun (ps, es) -> Verification.do_test ps es)
  |> Seq.iteri (fun i (ps,es) ->
    incr found_count;
    print_endline @@ Format.sprintf "found candidate (%dth iteration):\n\tP(t,i) := %a\n\tE(t,i) := %a\n" i
      (fun fmt vl -> Expr.pp fmt vl) ps
      (fun fmt vl -> Expr.pp fmt vl) es
  );
  print_endline @@ Printf.sprintf "found %d candidates\n" !found_count;
