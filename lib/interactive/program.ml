open Containers
open Common
open Nottui

let rec stmt_display ~indent:ind : E.t Prog.stmt -> ui Lwd.t =
  let indent' = string (String.make ind ' ') in
  function
  | `Match (exp, cases) ->
    W.vbox (
      W.hbox [indent'; string "match "; Expr.expr_display exp; string " with"] ::
      (List.map (case_display ~indent:(ind + 2)) cases)
    )
  | `LetLambda (v, lambda, rest) ->
    W.vbox [
      W.hbox [indent'; string "let "; display_highlightable v;
              string " = ";
              W.vbox [lambda_display lambda;
                      string " in "; ]];
      stmt_display ~indent:ind rest
    ]
  | `LetExp (param, exp, rest) ->
    W.vbox [
      W.hbox [indent'; string "let "; Expr.param_display param;
              string " = ";
              W.hbox [Expr.expr_display exp; string " in "] ];
      stmt_display ~indent:ind rest
    ]
  | `EmptyArray -> W.hbox [indent'; string "[| |]"]
  | `Value v -> W.hbox [indent'; Expr.expr_display v ]
  | `Write (arr, i, vl, rest) ->
    W.vbox [
      W.hbox [indent'; display_highlightable arr;
              string ".(";
              display_highlightable i;
              string ") <- ";
              Expr.expr_display vl; string ";"];
      stmt_display ~indent:ind rest
    ]
and case_display ~indent =
  let indent' = string (String.make indent ' ') in
  function
  | (cons, [], body) ->
    W.vbox (
      W.hbox (indent' :: string "| " :: string cons :: [string " -> "] ) ::
      [stmt_display ~indent:(indent + 2) body]
    )
  | (cons, args, body) ->
    W.vbox (
      W.hbox (indent' :: string "| " :: string cons :: string "(" ::
              (List.map display_highlightable args
               |> List.intersperse (string ", ")) @ [string ") -> "]
             ) ::
      [stmt_display ~indent:(indent + 2) body]
    )
and lambda_display : E.t Prog.lambda -> ui Lwd.t =
  function
  | `Lambda (params, body) ->
    W.vbox [
      W.hbox (string "fun " ::
              (List.map Expr.param_display params
               |> List.intersperse (string " ")) @
              [string " -> "] );
      stmt_display ~indent:2 body
    ]
