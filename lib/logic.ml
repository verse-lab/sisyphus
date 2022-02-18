let ctx = Z3.mk_context ["model", "false"; "proof", "false"; "timeout", "1000"]
let solver =  Z3.Solver.mk_solver ctx None
let () =
  begin try
    Z3.Solver.set_parameters solver (
      let params = Z3.Params.mk_params ctx in
      Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout") 1000;
      params
    )
  with Failure (str) -> print_endline str
  end

let (!!) = Z3.Symbol.mk_string ctx
let sort name = Z3.Sort.mk_uninterpreted_s ctx name
let int = Z3.Arithmetic.Integer.mk_sort ctx
let (+) a b = Z3.Arithmetic.mk_add ctx [ a; b ]
let (-) a b = Z3.Arithmetic.mk_sub ctx [ a; b ]
let (=) a b = Z3.Boolean.mk_eq ctx a b
let (<>) a b = Z3.Boolean.mk_distinct ctx [a; b]
let ( not ) = Z3.Boolean.mk_not ctx
let ( && ) a b = Z3.Boolean.mk_and ctx [a; b]
let ( || ) a b = Z3.Boolean.mk_or ctx [a; b]
let (>=) a b = Z3.Arithmetic.mk_ge ctx a b
let (>) a b = Z3.Arithmetic.mk_gt ctx a b
let (<) a b = Z3.Arithmetic.mk_lt ctx a b
let (<=) a b = Z3.Arithmetic.mk_le ctx a b
let ite cond ift iff = Z3.Boolean.mk_ite ctx cond ift iff
let bool_false = Z3.Boolean.mk_false ctx
let bool_true = Z3.Boolean.mk_true ctx

let (!*) i = Z3.Arithmetic.Integer.mk_numeral_i ctx i
let (==>) a b = Z3.Boolean.mk_implies ctx a b
let declare n s = Z3.Expr.mk_const_s ctx n s
let declare_fun fn args res = Z3.FuncDecl.mk_func_decl_s ctx fn args res

let w_context f =
  let res = 
    Z3.Solver.push solver;
    f () in
  Z3.Solver.pop solver 1;
  res

let assert_ l = Z3.Solver.add solver [l]

let check assumptions expr =
  Z3.Solver.push solver;
  w_context @@
  begin fun () ->
    match
      Z3.Solver.add solver assumptions;
      (* let query_str = 
       *   let assumptions_str = Z3.Solver.to_string solver in
       *   let goal_str = Z3.Expr.to_string expr in
       *   Printf.sprintf "(set-option :timeout 100)\n%s\n(assert %s)\n(check-sat)"  assumptions_str goal_str in
       * let z3_out =
       *   OS.Cmd.run_io (Cmd.of_list ["z3"; "-smt2"; "-in"]) (OS.Cmd.in_string query_str)
       *   |> OS.Cmd.to_string
       *   |> function Ok "unsat" -> Some false
       *             | Ok "sat" -> Some true
       *             | Ok "unknown" -> (\* print_endline query_str;  *\)None
       *             | Ok str -> print_endline ("unknown z3 output " ^ str); None
       *             | Error `Msg err -> failwith err in *)
      let result =  Z3.Solver.check solver [expr] in
      result
    with
    | Z3.Solver.UNSATISFIABLE -> Some false
    | Z3.Solver.UNKNOWN -> None
    | Z3.Solver.SATISFIABLE -> Some true
  end

let prove assumptions goal = Option.map Bool.not (check assumptions (not goal))

module With = struct
  type _ t =
    [] : Z3.Expr.expr t
  | (::) : ((string * Z3.Sort.sort) * 'b t) -> (Z3.Expr.expr -> 'b) t
end

module Quantifiers = struct

  open With

  type f = {forall: 'a . 'a t * 'a * Z3.Expr.expr list -> Z3.Expr.expr * Z3.Expr.expr list}

  let forall' {forall}  =
    fun (type a) (vars: a t) (body: a) (exprs) : (Z3.Expr.expr * Z3.Expr.expr list) ->
    match vars, body with
    | ([]: a t), (body: a) -> body, exprs
    | ((::) ((name, ty), rest) : a t), (body: a) ->
      let expr = Z3.Expr.mk_const_s ctx name ty in
      let body = body expr in
      forall (rest, body, expr :: exprs)

  let rec forall : 'a . 'a t * 'a * Z3.Expr.expr list -> Z3.Expr.expr * Z3.Expr.expr list =
    fun (type a) ((vars, body, exprs): a t * a * Z3.Expr.expr list) ->
    forall' {forall} vars body exprs

  let forall vars body =
    let body, vars = forall (vars, body, []) in
    Z3.Quantifier.expr_of_quantifier @@
    Z3.Quantifier.mk_forall_const ctx (List.rev vars) body None [] [] None None

end

let a = sort "a"

module List = struct

  let t = Z3.Z3List.mk_list_s ctx "list" a

  let nil = Z3.Z3List.nil t 
  let cons h tl = Z3.Expr.mk_app ctx (Z3.Z3List.get_cons_decl t) [h; tl]

  let rec of_list = function [] -> nil | h :: t -> cons h (of_list t)

  let tail = Z3.Z3List.get_tail_decl t
  let tail ls = Z3.Expr.mk_app ctx tail [ls]
  let head = Z3.Z3List.get_head_decl t
  let head ls = Z3.Expr.mk_app ctx head [ls]

  let rcons = declare_fun "rcons" [t; a] t
  let rcons ls vl  = Z3.Expr.mk_app ctx rcons  [ls; vl]
  let () =
    (* definition *)
    assert_ @@ Quantifiers.forall With.["ls", t; "vl", a] (fun ls vl ->
      ite (ls = nil)
        (rcons ls vl = cons vl nil)
        (rcons ls vl = cons (head ls) (rcons (tail ls) vl))
    )

  let length = declare_fun "length" [t] int
  let length ls  = Z3.Expr.mk_app ctx length  [ls]
  let () =
    (* definition *)
    assert_ @@ Quantifiers.forall With.["ls", t] (fun ls ->
      ite (ls = nil)
        (length ls = !* 0)
        (length ls = (!* 1 + length (tail ls)))
    );
    (* length_cons *)
    assert_ @@ Quantifiers.forall With.["vl", a; "ls", t] (fun vl ls ->
      (length (cons vl ls) = (!* 1 + length ls))
    );
    (* length_last *)
    assert_ @@ Quantifiers.forall With.["vl", a; "ls", t] (fun vl ls ->
      (length (rcons ls vl) = (!* 1 + length ls))
    );
    (* length_nil *)
    assert_ @@ (length nil = !* 0);
    (* custom? *)
    assert_ @@ Quantifiers.forall With.["ls", t] (fun ls ->
      (length ls = !* 0) ==> (ls = nil)
    );
    (* custom? *)
    assert_ @@ Quantifiers.forall With.["ls", t] (fun ls ->
      (length ls) >= !* 0
    )


  let append = declare_fun "append" [t; t] t
  let append l r  = Z3.Expr.mk_app ctx append  [l; r]
  let () =
    (* definition *)
    assert_ @@ Quantifiers.forall With.["l", t; "r", t] (fun l r ->
      ite (l = nil)
        (append l r = r)
        (append l r = cons (head l) (append (tail l) r))
    );
    (* length_app *)
    assert_ @@ Quantifiers.forall With.["l", t; "r", t] (fun l r ->
      length (append l r) = (length l + length r)
    );
    (* app_nil_l *)
    assert_ @@ Quantifiers.forall With.["l", t] (fun l ->
      append nil l = l
    );
    (* app_nil_r *)
    assert_ @@ Quantifiers.forall With.["l", t] (fun l ->
      append l nil = l
    );
    (* app_last_l *)
    assert_ @@ Quantifiers.forall With.["x", a; "l1", t; "l2", t] (fun x l1 l2 ->
      append (rcons l1 x) l2 = append l1 (cons x l2)
    );
    (* app_cons_r *)
    assert_ @@ Quantifiers.forall With.["x", a; "l1", t; "l2", t] (fun x l1 l2 ->
      append (cons x l1) l2 = cons x (append l1 l2)
    )

  let repeat = declare_fun "repeat" [int; a] t
  let repeat len vl  = Z3.Expr.mk_app ctx repeat  [len; vl]
  let () =
    (* definition *)
    assert_ @@ Quantifiers.forall With.["len", int; "vl", a] (fun len vl ->
      ite (len <= !* 0)
        (repeat len vl = nil)
        (repeat len vl = cons vl (repeat (len - !* 1) vl))
    );
    (* make_zero *)
    assert_ @@ Quantifiers.forall With.["v", a] (fun v ->
      repeat (!* 0) v = nil
    );
    (* make_succ_r *)
    assert_ @@ Quantifiers.forall With.["n", int; "v", a] (fun n v ->
      (n >= !* 0) ==> (repeat (n + !* 1) v = rcons (repeat n v) v)

    );
    (* make_succ_l *)
    assert_ @@ Quantifiers.forall With.["n", int; "v", a] (fun n v ->
      (n >= !* 0) ==> (repeat (n + !* 1) v = cons v (repeat n v))
    );
    (* repeat length *)
    assert_ @@ Quantifiers.forall With.["n", int; "v", a] (fun n v ->
      (n >= !* 0) ==> (length (repeat n v) = n)
    )


  let rev = declare_fun "rev" [t] t
  let rev ls  = Z3.Expr.mk_app ctx rev [ls]
  let () =
    (* nil_eq_rev_inv *)
    assert_ @@ Quantifiers.forall With.["ls", t] (fun ls ->
      (nil = rev ls) ==> (ls = nil)
    );
    (* length_rev *)
    assert_ @@ Quantifiers.forall With.["ls", t] (fun ls ->
      length (rev ls) = length ls
    );
    (* case_rev_split *)
    assert_ @@ Quantifiers.forall With.["xs", t; "v", a; "l", t; "r", t] (fun xs v l r ->
      (rev xs = append l (cons v r)) ==> (xs = append (rev r) (cons v (rev l)))
    );
    (* custom?  *)
    assert_ @@ Quantifiers.forall With.["xs", t; "v", a] (fun xs v ->
      (cons v (rev xs)) = rev (rcons xs v) 
    )




  let drop = declare_fun "drop" [int; t] t
  let drop n ls = Z3.Expr.mk_app ctx drop [n; ls]
  let () =
    (* definition *)
    assert_ @@ Quantifiers.forall With.["vl", int; "ls", t] (fun vl ls ->
      ite (vl <= !* 0)
        (drop vl ls = ls)
        (ite (ls = nil)
           (drop vl ls = nil)
           (drop vl ls = drop (vl - !* 1) (tail ls))
        )
    );
    (* drop_app_length *)
    assert_ @@ Quantifiers.forall With.["l", t; "l_", t] (fun l l' ->
      drop (length l) (append l l') = l'
    );
    (* drop_zero *)
    assert_ @@ Quantifiers.forall With.["l", t] (fun l ->
      drop (!* 0) l = l
    );
    (* drop_last *)
    assert_ @@ Quantifiers.forall With.["xs", t; "rst", t; "lst", a] (fun xs rst lst ->
      (rev xs = cons lst rst) ==>
      (drop (length xs - !* 1) xs = cons lst nil)
    )

  let update = declare_fun "update" [t; int; a] t
  let update ls ind vl = Z3.Expr.mk_app ctx update [ls; ind; vl]
  let () =
    (* definition *)
    assert_ @@ Quantifiers.forall With.["ls", t; "ind", int; "vl", a] (fun ls ind vl ->
      ite (ind <= !* 0)
        (ite (ls = nil)
           (update ls ind vl = nil)
           (update ls ind vl = cons vl (tail ls))
        )
        (ite (ls = nil)
           (update ls ind vl = nil)
           (update ls ind vl = cons (head ls) (update (tail ls) (ind - !* 1) vl))
        )
    );
    (* update_app_l *)
    assert_ @@ Quantifiers.forall With.["l1", t; "i", int; "l2", t; "v", a] (fun l1 i l2 v ->
      (!* 0 <= i && i < length l1) ==> (update (append l1 l2) i v = append (update l1 i v) l2)
    );
    (* update_middle *)
    assert_ @@ Quantifiers.forall With.["i", int; "l1", t; "l2", t; "v", a; "w", a] (fun i l1 l2 v w ->
      (i = length l1) ==> (update (append l1 (cons w l2)) i v = append (rcons l1 v) l2)
    )

end
