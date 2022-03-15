open Common
open Nottui

module Make (S: sig

    val debug: ui Lwd.t

    val init: E.t Logic.Proof.ctx

    val update: string -> E.t Logic.Proof.ctx -> E.t Logic.Proof.ctx option

  end) = struct

  let proof_state = Lwd.var S.init

  let on_command command =
    match S.update command (Lwd.peek proof_state) with
    | None -> ()
    | Some state' -> Lwd.set proof_state state'

  let repl = Components.repl ~init:["(* Initialised Sisyphus-Proof Repair v.0.1... *)"] ~on_command ()

  let ui =
    let ctx = Lwd.get proof_state in
    W.v_pane 
      (W.v_pane
         (Proof.ctx_display ctx)
         (W.h_pane (Proof.proof_goal ctx) repl))
      S.debug

  let run () =
    Ui_loop.run ui

end
