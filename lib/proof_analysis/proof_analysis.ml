
type t = |
  
let analyse (trm: Constr.t) : t =
  match Constr.kind trm with
  | Constr.App (trm, [| o1; o2; o3 |]) ->
    failwith "lollll"
  | _ -> 
    failwith ("lol " ^ Proof_utils.Debug.tag trm)
  
