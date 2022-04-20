open Containers
open Common

let rec type_display (typ: Logic.Type.t) =
  match typ with
  | Unit -> display_highlightable "()"
  | Var v -> display_highlightable ~attr:A.(st bold) v
  | Int -> display_highlightable  "int"
  | Loc -> display_highlightable "loc"
  | Func -> display_highlightable "func"
  | Ref ty -> 
    let ref = display_highlightable ~attr:A.(fg cyan) "ref" in
    let ty = type_display ty in
    W.hbox [ref; string " "; ty]
  | Array ty -> 
    let array = display_highlightable ~attr:A.(fg cyan) "array" in
    let ty = type_display ty in
    W.hbox [array; string " "; ty]
  | List ty ->
    let list = display_highlightable ~attr:A.(fg cyan) "list" in
    let ty = type_display ty in
    W.hbox [list; string " "; ty]
  | Product tys ->
    let prods = List.map type_display tys in
    let elts = string "(" ::
               List.intersperse (string " * ") prods
               @ [string ")"] in
    W.hbox elts
  | ADT (name, args) ->
    let args = List.map type_display args in
    let name = display_highlightable name in 
    W.hbox (name :: string " " :: args)
