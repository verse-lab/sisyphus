open Containers
open Common

let repl ?(init=["(* Initialised Sisyphus-Proof Repair v.0.1... *)"]) ?(on_command=fun _ -> ()) () =
  let log = Lwd.var init in
  let+ logv = Lwd.get log in
  let display = Lwd.var "" in
  let on_change (v, i) =
    let displayv = Lwd.peek display in
    Lwd.set display @@
    if i = 0 && String.length displayv > 0
    then String.sub displayv 0 (String.length displayv - 1)
    else  (displayv ^ v) in
  let on_submit (str, _) =
    let command = Lwd.peek display ^ str in
    on_command command;
    Lwd.set log (command :: logv) in
  let text = List.map string logv in
  let+ display = Lwd.get display in
  (W.vbox @@
   (W.hbox [string "> "; string display; (W.edit_field (Lwd.return ("", 100)) ~on_change ~on_submit)]) ::
   text
  )
