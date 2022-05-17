let is_const_named name const =
  Constr.isConst const &&
  String.(
    (fst @@ Constr.destConst const)
    |> Names.Constant.label
    |> Names.Label.to_string = name
  )
let is_hempty const = is_const_named "hempty" const
let is_hstar const = is_const_named "hstar" const
let is_hpure const = is_const_named "hpure" const
let is_wptag const = is_const_named "Wptag" const
let is_wp_gen_let_trm const = is_const_named "Wpgen_let_trm" const
let is_wp_gen_app const = is_const_named "Wpgen_app" const

let extract_cfml_goal goal =
  let[@warning "-8"] himpl, [pre; post] = Constr.decompose_app goal in
  assert begin
    String.equal
      "himpl"
      (fst (Constr.destConst himpl)
       |> Names.Constant.label
       |> Names.Label.to_string)
  end;
  let destruct_heap pre =
    let rec loop acc pre =
      match Constr.kind pre with
      | Constr.Const (_, _) when is_hempty pre -> acc
      | Constr.App (fname, [|heaplet; rest|]) when is_hstar fname ->
        begin match Constr.kind heaplet with
        | Constr.App (fname, _) when is_hpure fname ->
          loop (`Pure heaplet :: acc) rest             
        | _ ->
          loop (`Impure heaplet :: acc) rest 
        end
      | _ ->
        (`Impure pre :: acc) in
    loop [] pre in
  let pre =
    match Constr.kind pre with
    | Constr.Const (_, _) when is_hempty pre -> `Empty
    | Constr.App (fname, _) when is_hstar fname ->
      begin match destruct_heap pre with
      | heap -> `NonEmpty heap
      | exception _ -> failwith ("unexpected pre-heap structure: " ^ (Proof_debug.constr_to_string pre))
      end
    | Constr.App (fname, _) when is_hpure fname ->
      `NonEmpty ([`Pure pre])
    | _ -> `NonEmpty ([`Impure pre])
  in
  (pre, post)

let extract_x_app_fun pre =
  let extract_app_enforce name f n pre =
    match Constr.kind pre with
    | Constr.App (fname, args) when f fname ->
      args.(n)
    | _ ->
      Format.eprintf "failed because unknown structure for %s: %s\n" name (Proof_debug.constr_to_string pre);
      failwith "" in
  try
    pre
    |> extract_app_enforce "wptag" is_wptag 0
    |> extract_app_enforce "xlet" is_wp_gen_let_trm 0
    |> extract_app_enforce "wptag" is_wptag 0
    |> extract_app_enforce "xapp" is_wp_gen_app 2
    |> Constr.destConst
    |> fst
  with
    Failure _ -> failwith ("extract_f_app failed because unsupported context: " ^ (Proof_debug.constr_to_string pre))

let extract_spec pre =
  let extract_spec pre =
    let rec loop acc pre = 
      if Constr.isProd pre
      then
        let ({Context.binder_name; _}, ty, pre)  = Constr.destProd pre in
        loop ((binder_name, ty) :: acc) pre
      else List.rev acc, pre in
    loop [] pre in
  let rec split acc ls =
    match ls with
    | [] -> (List.rev acc,[])
    | ((name, _) as h) :: t when Names.Name.is_anonymous name ->
      (List.rev acc, h::t)
    | h :: t -> split (h :: acc) t in
  let params, body = extract_spec pre in
  let params, invariants = split [] params in
  (params, invariants, body)

