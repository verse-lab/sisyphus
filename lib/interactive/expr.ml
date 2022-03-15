open Nottui
open Containers
open Common

let param_display : E.param -> ui Lwd.t = function
  | `Tuple args ->
    W.hbox (string "(" :: (List.map display_highlightable args
                            |> List.intersperse (string " ")) @ [string ")"])
  |`Var v -> display_highlightable v

let rec expr_display ?(needs_params=false) : E.t -> ui Lwd.t = fun (e: E.t) ->
  match e with
  | `App ("(+)", [l;r]) ->
    W.hbox ((if needs_params then [string "("] else []) @
             [expr_display ~needs_params:false l; string " + "; expr_display ~needs_params:true r]  @
              (if needs_params then [string ")"] else []))
  | `App ("(-)", [l;r]) ->
    W.hbox ((if needs_params then [string "("] else []) @
             [expr_display ~needs_params:false l; string " - "; expr_display ~needs_params:true r]  @
              (if needs_params then [string ")"] else []))
  | `App (fn, args) ->
    W.hbox ((if needs_params then [string "("] else []) @
             [display_highlightable fn; string " "] @
            (List.map (expr_display ~needs_params:true) args
             |> List.intersperse (string " ")) @
              (if needs_params then [string ")"] else []))
  | `Constructor (cons, []) -> display_highlightable cons
  | `Constructor ("::", [h;t]) ->
    W.hbox ((if needs_params then [string "("] else []) @
            [expr_display ~needs_params:false h; string " :: ";
             expr_display ~needs_params:true t] @
            (if needs_params then [string ")"] else []) )
  | `Constructor (cons, args) ->
    W.hbox ([display_highlightable cons; string "("] @
            (List.map (expr_display ~needs_params:false) args
             |> List.intersperse (string ", ")) @
            [string ")"])
  | `Tuple args ->
    W.hbox (string "(" ::
            (List.map (expr_display ~needs_params:false) args
             |> List.intersperse (string ", ")) @
            [string ")"])
  | `Int i -> string ~attr:A.(fg magenta) (Int.to_string i)
  | `Lambda (params, body) ->
    W.hbox (
      (if needs_params then [string "("] else []) @
      string "fun " :: (List.map param_display params
                              |> List.intersperse (string " ")) @
      [string " -> "; expr_display ~needs_params:false body] @
      (if needs_params then [string ")"] else [])
    )
  | `Var v -> display_highlightable v
