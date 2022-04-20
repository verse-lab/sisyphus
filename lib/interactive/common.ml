open Containers
module Ty = Logic.Type
module E = Logic.Expr
module P = Logic.Proof
module A = Notty.A
module W = Nottui_widgets
module Prog = Logic.Program

module StringMap = Map.Make(String)

let (let+) x f = Lwd.bind x ~f 

let string ?attr s = Lwd.pure (W.string ?attr s)
let highlighted_name: string option Lwd.var = Lwd.var None

let display_highlightable ?(attr=A.empty) v =
  let set_highlighted v () = Lwd.set highlighted_name (Some v) in
  let+ highlighted_ty = Lwd.get highlighted_name in
  let is_highlighted =
    Option.exists (String.equal v) highlighted_ty in
  let attr =
    if is_highlighted
    then A.(st reverse ++ attr)
    else attr in
  Lwd.return @@ W.button ~attr (Printf.sprintf "%s" v)
                  (set_highlighted v)
