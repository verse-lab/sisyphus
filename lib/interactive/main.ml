open Containers

module S = struct

  let debug_log = Lwd.var []

  let debug =
    let scroll_state = Lwd.var Nottui_widgets.default_scroll_state in
    Lwd.bind (Lwd.get debug_log)  ~f:(fun vars ->
      Nottui_widgets.vscroll_area ~state:(Lwd.get scroll_state)
        ~change:(fun _ st -> Lwd.set scroll_state st) @@
      Lwd_utils.pack Nottui.Ui.pack_z
      [Nottui_widgets.vlist (List.map (fun v -> Lwd.return @@ (Nottui_widgets.string v)) vars)])

  let other_ctxs = Lwd.var []

  let proof_steps = Lwd.var []

  let init =
    let proof = IO.with_in "../../resources/seq_to_array/proof_updated_simplified.v" Proof_parser.parse_channel in
    let spec = Logic.Proof_sanitizer.convert_spec proof.spec in
    let proof = Logic.Proof_sanitizer.convert_proof proof.proof in
    let prog =
      let txt = IO.with_in "../../resources/seq_to_array/updated.ml" IO.read_all in
      Logic.Sanitizer.parse_str txt in

    Lwd.set proof_steps proof;

    Logic.Proof.{
      types=spec.types;
      variables=StringMap.of_list spec.params;
      relations=StringMap.of_list [];
      equalities=StringMap.of_list [];
      specifications=StringMap.of_list [];
      pre = spec.pre;
      res_param = spec.res_param;
      post = spec.post;
      state= `Init prog
    }


  let update =
    let debug v = Lwd.set debug_log (v :: Lwd.peek debug_log) in
    function
    | "xcf" -> fun (ctx: 'a Logic.Proof.ctx) ->
      begin match ctx.state with
      | `Init prog -> Some {ctx with state= `Step prog.body}
      |  _ -> None
      end
    | "next" -> fun ctx ->
      begin match Lwd.peek proof_steps with
      | [] -> None
      | h :: rest ->
        match Logic.Eval.apply_step h ctx with
        | v ->
          Lwd.set proof_steps rest;
          Some v
        | exception e ->
          debug (Printf.sprintf "rule %s failed" (Logic.Proof.show_step h));
          debug (Printf.sprintf "reason: %s" (Printexc.to_string e));
          None
      end
    | "display" -> fun _ ->
      debug begin match Lwd.peek proof_steps with
        | [] -> "NO MORE RULES"
        | h :: _ -> Logic.Proof.show_step h
      end;
      None
    | "swap" -> fun ctx ->
      begin match Lwd.peek other_ctxs with
      | [] -> None
      | h :: t ->
        debug (Printf.sprintf "%d other goals" (List.length t + 1));
        Lwd.set other_ctxs (t @ [ctx]);
        Some h
      end
    | _ -> fun _ ->  None

end

module E = Interactive.Engine.Make(S)

let () =
  E.run ()
