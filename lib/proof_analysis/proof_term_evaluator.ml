open Containers

(** [eval ctx expr] evaluates a reified computation into a wrapped
    existential type, using an evaluation context provided by [ctx]. *) 
let rec eval ctx : Lang.Expr.t -> Sisyphus_tracing.Wrap.t =
  let open Sisyphus_tracing.Wrap in
  function[@warning "-8"]
  | `Tuple [a;b] ->
    wrap (unwrap (eval ctx a), unwrap (eval ctx b)) 
  | `Tuple [a;b;c] ->
    wrap (unwrap (eval ctx a),
          unwrap (eval ctx b),
          unwrap (eval ctx c))
  | `Tuple [a;b;c;d] ->
    wrap (unwrap (eval ctx a),
          unwrap (eval ctx b),
          unwrap (eval ctx c),
          unwrap (eval ctx d))
  | `Var v -> ctx v
  | `App ("!", [l]) ->
    wrap (! (unwrap (eval ctx l)))
  | `App ("Array.to_list", [l]) ->
    wrap (Array.to_list (unwrap (eval ctx l)))
  | `App ("=", [l;r]) ->
    wrap (Equal.poly (unwrap (eval ctx l)) (unwrap (eval ctx r)))
  | `App (("+" | "(+)"), [l;r]) ->
    wrap ((unwrap (eval ctx l)) + (unwrap (eval ctx r)))
  | `App (("-" | "(-)"), [l;r]) ->
    wrap ((unwrap (eval ctx l)) - (unwrap (eval ctx r)))
  | `App (("*" | "( * )"), [l;r]) ->
    wrap ((unwrap (eval ctx l)) * (unwrap (eval ctx r)))
  | `App (("TLC.LibList.concat" | "concat"), [l]) ->
    wrap (List.concat (unwrap (eval ctx l)))
  | `App (("TLC.LibList.length" | "TLC.LibListZ.length" | "length"), [l]) ->
    wrap (List.length (unwrap (eval ctx l)))
  | `App (("TLC.LibList.app" | "app" | "++"), [l;r]) ->
    wrap (unwrap (eval ctx l) @ (unwrap (eval ctx r)))
  | `App (("TLC.LibList.combine" | "combine"), [l;r]) ->
    wrap (List.combine (unwrap (eval ctx l)) (unwrap (eval ctx r)))
  | `App (("TLC.LibList.drop" | "TLC.LibListZ.drop" | "drop"), [l;r]) ->
    wrap (List.drop (unwrap (eval ctx l)) (unwrap (eval ctx r)))
  | `App (("TLC.LibList.map" | "map"), [f;ls]) ->
    wrap (List.map (unwrap (eval ctx f)) (unwrap (eval ctx ls)))
  | `App (("TLC.LibList.rev" | "rev"), [ls]) ->
    wrap (List.rev (unwrap (eval ctx ls)))
  | `App (("TLC.LibList.split" | "split"), [ls]) ->
    wrap (List.split (unwrap (eval ctx ls)))
  | `App (("TLC.LibList.take" | "TLC.LibListZ.take" | "take"), [n; ls]) ->
    wrap (List.take (unwrap (eval ctx n)) (unwrap (eval ctx ls)))
  | `App (("TLC.LibList.sum" | "TLC.LibListZ.sum" | "sum"), [ls]) ->
    wrap (List.fold_left (+) 0 (unwrap (eval ctx ls)))
  | `App (("TLC.LibOrder.ge" | "ge"), [l; r]) ->
    wrap ((unwrap (eval ctx l)) >= (unwrap (eval ctx r)))
  | `App (("TLC.LibOrder.le" | "le"), [l; r]) ->
    wrap ((unwrap (eval ctx l)) <= (unwrap (eval ctx r)))
  | `App (("TLC.LibOrder.lt" | "lt"), [l; r]) ->
    wrap ((unwrap (eval ctx l)) < (unwrap (eval ctx r)))
  | `App (("Coq.ZArith.BinInt.Z.max" | "max"), [l; r]) ->
    wrap (max (unwrap (eval ctx l)) (unwrap (eval ctx r)))
  | `App (("Coq.ZArith.BinInt.Z.min" | "min"), [l; r]) ->
    wrap (min (unwrap (eval ctx l)) (unwrap (eval ctx r)))
  | `App (("TLC.LibList.make" | "TLC.LibListZ.make" | "make"), [n; vl]) ->
    let n = (unwrap (eval ctx n)) in
    let vl = (unwrap (eval ctx vl)) in
    let ls = if n <= 0 then [] else List.init n (fun _ -> vl) in
    wrap ls
  | `Lambda _ -> failwith "lambdas in invariants not supported"
  | `Int n -> wrap n
  | `Constructor (("true"), []) ->
    wrap true
  | `Constructor (("false"), []) ->
    wrap false
  | `Constructor (("::" | "cons"), [hd;tl]) ->
    wrap ((unwrap (eval ctx hd)) :: (unwrap (eval ctx tl)))
  | `Constructor (("[]" | "nil"), []) ->
    wrap ([])
