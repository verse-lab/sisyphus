


let apply_step: Proof.step ->  Expr.t Proof.ctx -> Expr.t Proof.ctx = fun step ctx ->
  match step with
  | `Xcf ->
    let[@warning "-8"] (`Init prog : [ `Init of Expr.t Program.t | `Step of 'a Program.stmt ]) = ctx.state in
    {ctx with state= `Step prog.body}
  | _ -> failwith "not implemented yet, lol"
