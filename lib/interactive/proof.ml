open Containers
open Common

let types v = Lwd.map (fun (v: 'a P.ctx) -> v.types) v
let variables v = Lwd.map (fun (v: 'a P.ctx) -> StringMap.to_list v.variables) v
let relations v = Lwd.map (fun (v: 'a P.ctx) -> StringMap.to_list v.relations) v
let equalities v = Lwd.map (fun (v: 'a P.ctx) -> StringMap.to_list v.equalities) v
let specifications v = Lwd.map (fun (v: 'a P.ctx) -> StringMap.to_list v.specifications) v
let pre v = Lwd.map (fun (v: 'a P.ctx) -> v.pre) v
let res_param v = Lwd.map (fun (v: 'a P.ctx) -> v.res_param) v
let post v = Lwd.map (fun (v: 'a P.ctx) -> v.post) v
let state v : [`Init of E.t Prog.t | `Step of E.t Prog.stmt ] Lwd.t = Lwd.map (fun (v: 'a P.ctx) -> v.state) v

let heaplet_display (P.Heap.Heaplet.PointsTo (var, e): P.Heap'.Heaplet.t) =
  W.hbox [display_highlightable var; string " ~> "; Expr.expr_display ~needs_params:true e]

let heap_display ?(res_param=[]) (heap: P.Heap'.Assertion.t) =
  match List.is_empty  (P.Heap'.Assertion.phi heap), List.is_empty (P.Heap'.Assertion.sigma heap) with
  | true, true -> W.hbox (string "{" :: res_param @ [ string "emp"; string "}"])
  | false, true ->
    W.hbox (string "{" :: res_param @
            (P.Heap'.Assertion.phi heap
             |> List.map Expr.expr_display
             |> List.intersperse (string " /\\ ") ) @
            [ string "; emp"; string "}"])
  | true, false ->
    W.hbox (string "{" :: res_param @
            (P.Heap'.Assertion.sigma heap
             |> List.map heaplet_display
             |> List.intersperse (string " * ")
            ) @
            [ string "}"])

  | _ ->
    W.hbox (string "{" :: res_param @
            (P.Heap'.Assertion.phi heap
             |> List.map Expr.expr_display
             |> List.intersperse (string " /\\ ") ) @
            string ";" ::
            (P.Heap'.Assertion.sigma heap
             |> List.map heaplet_display
             |> List.intersperse (string " * ")
            ) @
            [ string "}"])
let res_param_display (var, ty) =
  W.hbox [string "fun ("; display_highlightable var; string ": "; Type.type_display ty; string ") => "]


let quantified_type_display typ =
  W.hbox [
    display_highlightable ~attr:A.(st bold) typ;
    Lwd.return @@ W.string ": ";
    Lwd.return @@ W.string ~attr:A.(fg blue ++ st bold) "Type";
  ]
let variable_display (var, typ) =
  W.hbox [display_highlightable var; string ": "; Type.type_display typ]

let relation_display (name, args) =
  W.hbox ([string ~attr:A.(fg yellow ++ st bold) name; string " "] @
          (List.map (Expr.expr_display ~needs_params:true) args
           |> List.intersperse (string " ")))

let relation_display (hyp, relation) =
  W.hbox [display_highlightable hyp; string ": "; relation_display relation]

let equality_display (l, r) =
  W.hbox ([Expr.expr_display l; string " = "; Expr.expr_display r])
let equality_display (hyp, relation) =
  W.hbox [display_highlightable hyp; string ": "; equality_display relation]

let spec_display (hyp, (fn, def)) =
  W.hbox [display_highlightable hyp; string ": "; display_highlightable fn; string " = ";
          Program.lambda_display def]

let ctx_display ctx =
  let+ types = Lwd.map (List.map quantified_type_display) (types ctx) in
  let+ variables = Lwd.map (List.map variable_display) (variables ctx) in
  let+ relations = Lwd.map (List.map relation_display) (relations ctx) in
  let+ equalities = Lwd.map (List.map equality_display) (equalities ctx) in
  let+ specifications = Lwd.map (List.map spec_display) (specifications ctx) in
  W.h_pane (W.vbox (List.concat [
         types;
         variables;
         relations;
         equalities
       ])) (W.vbox specifications)

let program_state_display program =
  match program with
  | `Init prog -> 
    string (Prog.show E.print prog)
  | `Step stmt ->
    Program.stmt_display ~indent:2 stmt

let proof_goal ctx =
  let program = Lwd.bind (state ctx) program_state_display in
  let pre = Lwd.bind (pre ctx) heap_display in
  let post =
    let+ res_param = res_param ctx in
    let res_param = [res_param_display res_param] in
    Lwd.bind (post ctx) (heap_display ~res_param) in
  W.vbox [
    pre;
    program;
    post
  ]
