open Containers

module S = struct

  let debug_log = Lwd.var []

  let debug =
    Lwd.bind (Lwd.get debug_log) (fun vars -> Nottui_widgets.vbox (List.map (fun v -> Lwd.return @@ (Nottui_widgets.string v)) vars))

  let init =
    let prog =
      let txt = IO.with_in "../../resources/seq_to_array/updated.ml" IO.read_all in
      Logic.Sanitizer.parse_str txt in
    Logic.Proof.{
      types=["A"; "B"];
      variables=StringMap.of_list [
        "x", Logic.Type.List (Var "A");
        "y", Logic.Type.List (Var "B");
        "z", Logic.Type.Product [Int; Int; List (Var "B")];
      ];
      relations=StringMap.of_list [
        "H1", ("Lseq", [`Var "l"; `Var "y"])
      ];
      equalities=StringMap.of_list [
        "Hlseq", (Logic.Sanitizer.parse_expr_str "(len,ls)",
                  Logic.Sanitizer.parse_expr_str "(List.length l,List.rev ls)")
      ];
      specifications=StringMap.of_list [
        "Hf", ("f", Logic.Sanitizer.parse_lambda_str "(fun i x -> a.(i) <- x; i + 1)")
      ];
      pre = Heap.Assertion.{phi=Heap'.ExprSet.empty; sigma=Heap'.Heap.empty};
      res_param = ("res", Int);
      post = Heap.Assertion.{phi=Heap'.ExprSet.empty; sigma=Heap'.Heap.empty};
      state= `Init prog
    }


  let update =
    let debug v = Lwd.set debug_log (v :: Lwd.peek debug_log) in
    function
    | "xcf" -> fun (ctx: 'a Logic.Proof.ctx) ->
      debug "got xcf";
      begin match ctx.state with
      | `Init prog -> Some {ctx with state= `Step prog.body}
      |  _ -> None
      end
    | s -> debug @@ "got " ^ s; fun _ ->  None

end

module E = Interactive.Engine.Make(S)

let () =
  E.run ()
