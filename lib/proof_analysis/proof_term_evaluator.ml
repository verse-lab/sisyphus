open Containers

(** [eval ctx expr] evaluates a reified computation into a wrapped
    existential type, using an evaluation context provided by [ctx]. *) 
let rec eval ctx : Lang.Expr.t -> Sisyphus_tracing.Wrap.t =
  let open Sisyphus_tracing.Wrap in
  function
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
  | `App ("&&", [l;r]) ->
    wrap ((unwrap (eval ctx l)) && (unwrap (eval ctx r)))
  | `App ("||", [l;r]) ->
    wrap ((unwrap (eval ctx l)) || (unwrap (eval ctx r)))
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
  | `App ("list_findi", [f; ls]) ->
    let rec findi i f ls =
      match ls with
      | [] -> None
      | h :: t ->
        if f i h then Some (i, h)
        else findi (i + 1) f t in
    wrap (findi 0 (unwrap (eval ctx f)) (unwrap (eval ctx ls)))
  | `App ("list_findi_map", [f; ls]) ->
    let rec findi_map i f ls =
      match ls with
      | [] -> None
      | h :: t ->
        match f h with
        | Some v -> Some (i, v)
        | None -> findi_map (i + 1) f t in
    wrap (findi_map 0 (unwrap (eval ctx f)) (unwrap (eval ctx ls)))
  | `App ("list_find_mapi", [f; ls]) ->
    let rec find_mapi i f ls =
      match ls with
      | [] -> None
      | h :: t ->
        match f i h with
        | Some v -> Some v
        | None -> find_mapi (i + 1) f t in
    wrap (find_mapi 0 (unwrap (eval ctx f)) (unwrap (eval ctx ls)))
  | `App ("list_find_map", [f; ls]) ->
    let rec find_map f ls =
      match ls with
      | [] -> None
      | h :: t ->
        match f h with
        | Some v -> Some v
        | None -> find_map f t in
    wrap (find_map (unwrap (eval ctx f)) (unwrap (eval ctx ls)))
  | `App ("filter_not", [fp; ls]) ->
    let rec filter_not fp ls =
      match ls with
      | [] -> []
      | h :: t ->
        if fp h
        then filter_not fp t
        else h :: filter_not fp t in
    wrap (filter_not (unwrap (eval ctx fp)) (unwrap (eval ctx ls)))

  | expr ->
    Format.ksprintf ~f:failwith "proof_analysis/proof_term_evaluator.ml:%d: unsupported expression %a" __LINE__
      Lang.Expr.pp expr

