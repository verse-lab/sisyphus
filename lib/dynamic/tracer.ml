open Containers

module type SYMBOL = sig
  type t
  val tname : string
  val prelude: string
  val pp: Format.formatter -> t -> unit
  val equal: t -> t -> bool
  val fresh: unit -> t
end

module Make(Symbol: SYMBOL) = struct

  type value = [
    | `Int of int
    | `Value of Symbol.t
    | `List of value list
    | `Tuple of value list
    | `Constructor of string * value list
  ] [@@deriving eq, show]

  type heaplet = [
      `PointsTo of value
    | `Array of value list
  ] [@@deriving eq, show]

  type state = int * (string * value) list * (string * heaplet) list
  [@@deriving show, eq]

  type trace = state list
  [@@deriving show, eq]

  (* Lang.Program *)
  let rec sample_arg_for_ty env : Lang.Type.t -> string Random.random_gen =
    let open Random in
    function[@warning "-8"]
    | Lang.Type.Unit -> pure "()"
    | Lang.Type.Var _ -> pure @@ Format.sprintf "%a" Symbol.pp (Symbol.fresh ())
    | Lang.Type.Int -> let* i = Random.int 10 in pure @@ Printf.sprintf "%d" i
    | Lang.Type.List ty ->
      let* sz = Random.pick_array [|1; 3; 4; 5; 8; 10; 20|] in
      let* contents = List.init sz (fun _ -> sample_arg_for_ty env ty) |> list_seq in
      pure (Printf.sprintf "[%s]" (String.concat "; " contents))
    | Lang.Type.Array ty ->
      let* sz = Random.pick_array [|1; 3; 4; 5; 8; 10; 20|] in
      let* contents = List.init sz (fun _ -> sample_arg_for_ty env ty) |> list_seq in
      pure (Printf.sprintf "[|%s|]" (String.concat "; " contents))
    | Lang.Type.Product tys ->
      let* contents = List.map (fun ty -> sample_arg_for_ty env ty) tys |> list_seq in
      pure (Printf.sprintf "(%s)" (String.concat ", " contents))
    | Lang.Type.Ref ty ->
      let* contents = sample_arg_for_ty env ty in
      pure @@ Printf.sprintf "(ref (%s))" contents
    | Lang.Type.ADT (name, [ty]) ->
      let conv_fun = List.assoc ~eq:String.equal name env in
      let* sz = Random.pick_array [|1; 3; 4; 5; 8; 10; 20|] in
      let* contents = List.init sz (fun _ -> sample_arg_for_ty env ty) |> list_seq in
      pure @@ Printf.sprintf "(%s [%s])" conv_fun (String.concat "; " contents)

  let generate_random_args env (args: (string * Lang.Type.t) list) =
    let args =
      Random.run
        (List.map (fun (_,ty) -> sample_arg_for_ty env ty) args |> Random.list_seq) in
    String.concat " " args

  let encode ?prelude:(prelude'="") (prog: Lang.Expr.t Lang.Program.t) input =
    let id =
      let ind = ref 0 in
      fun () -> incr ind; !ind in
    let buf = Buffer.create 100 in
    let output str = Buffer.add_string buf str; Buffer.add_string buf "\n" in
    let fmt str = Format.ksprintf ~f:(fun str -> Buffer.add_string buf str;
                                       Buffer.add_string buf "\n") str in

    output prelude;
    output prelude';
    output prog.prelude;
    fmt "let %s %a = "
      prog.name
      (List.pp ~pp_start:(fun _ _ -> ())
         ~pp_stop:(fun _ _ -> ())
         ~pp_sep:(fun fmt () -> Format.pp_print_space fmt ())
         Lang.Expr.pp_typed_param)
      (List.map (fun v -> `Var v) prog.args);

    let rec build_enc (v: Lang.Type.t) =
      match v with
      | Lang.Type.Unit -> None
      | Lang.Type.Ref _ -> None
      | Lang.Type.Array _ -> None
      | Lang.Type.Var _ -> Some "__enc_symbol"
      | Lang.Type.Int -> Some "__enc_int"
      | Lang.Type.Func -> None
      | Lang.Type.Loc -> None
      | Lang.Type.List ty ->
        Option.map
          (fun enc -> Printf.sprintf "(__enc_list %s)" enc)
          (build_enc ty)
      | Lang.Type.ADT (_adt, _tys) ->
        None
        (* List.map build_enc tys
         * |> List.all_some
         * |> Option.map (fun tys ->
         *   Printf.sprintf "(__enc_%s %s)"
         *     adt
         *     (String.concat " " tys)
         * ) *)
      | Lang.Type.Product tys ->
        List.map build_enc tys
        |> List.all_some
        |> Option.map @@ fun tys ->
        Printf.sprintf "(fun (%s) -> `Tuple [%s])"
          (List.mapi (fun i _ -> Printf.sprintf "v%d" i) tys
           |> String.concat ", ") 
          (List.mapi (fun i ty -> Printf.sprintf "%s v%d" ty i) tys
           |> String.concat "; ") in

    let print_env (env: (string * Lang.Type.t) list) =
      List.filter_map (fun (name, ty) ->
        build_enc ty |> Option.map (fun enc ->
          Printf.sprintf {|"%s", %s %s|}
            name enc name)
      ) env |> String.concat "; " in

    let print_heap env =
      List.filter_map (function
        | v, Lang.Type.Array ty ->
          (build_enc ty) |> Option.map @@ fun enc ->
          (Printf.sprintf {|"%s", `Array (List.map (%s) (Array.to_list %s))|} v enc v)
        | v, Lang.Type.Ref ty ->
          (build_enc ty) |> Option.map @@ fun enc ->
          (Printf.sprintf {|"%s", `PointsTo ((%s) (! %s))|} v enc v)
        | _ -> None
      ) env |> String.concat "; " in

    let add_param (param: Lang.Expr.typed_param) env =
      match param with
      | `Tuple args -> env @ args
      | `Var arg -> env @ [arg] in

    let rec loop ~observe env (body: Lang.Expr.t Lang.Program.stmt) =
      match body with
      | `Value vl ->
        let id = id () in
        let heap = print_heap env in
        let env = print_env env in
        if observe then begin
        fmt {|
          __observe %d [%s] [%s];
        |} id env heap 
        end;
        fmt {|
          %a
        |} Lang.Expr.pp vl;
        if observe then begin
          fmt {|
          __observe %d [%s] [%s];
        |} id env heap
        end;
      | `EmptyArray ->
        let id = id () in
        let heap = print_heap env in
        let env = print_env env in
        if observe then begin
          fmt {|
          __observe %d [%s] [%s];
        |} id env heap
        end;
        fmt {|
          [| |]
        |} ;
        if observe then begin
          fmt {|
          __observe %d [%s] [%s];
        |} id env heap
        end;
      | `LetExp (`Var (_, Lang.Type.Unit), expr, body) ->
        let () =
          let id = id () in
          let heap = print_heap env in
          let env = print_env env in
          if observe then begin
          fmt {|
          __observe %d [%s] [%s];
        |} id env heap
          end;
          fmt {|
          let _ = %a in
        |} 
            Lang.Expr.pp expr in
        loop ~observe env body
      | `LetExp (args, expr, body) ->
        let () =
          let id = id () in
          let heap = print_heap env in
          let env = print_env env in
          if observe then begin
            fmt {|
          __observe %d [%s] [%s];
|} id env heap
          end;
          fmt {|
          let %a = %a in
        |} 
            Lang.Expr.pp_typed_param args
            Lang.Expr.pp expr in
        let env = add_param args env in
        loop ~observe env body
      | `LetLambda (var, `Lambda (params, lambody), body) ->
        let () = 
          fmt {|
          let %s = fun %a -> 
          |} var
            (List.pp ~pp_start:(fun _ _ -> ())
               ~pp_stop:(fun _ _ -> ())
               ~pp_sep:(fun fmt () -> Format.pp_print_space fmt ())
               Lang.Expr.pp_typed_param) params;
          let env =
            List.fold_left (fun env param -> add_param param env)
              env params in
          loop ~observe:false env lambody;
          fmt {| in |} in
        let env = env @ [var, Func] in
        loop ~observe env body
      | `Match (exp, cases) ->
        let () =
          let id = id () in
          let heap = print_heap env in
          let env = print_env env in
          if observe then begin
            fmt {|
          __observe %d [%s] [%s];
        |}  id env heap 
          end;
          fmt {|
          match %a with
        |}  Lang.Expr.pp exp in
        List.iter (fun (cons, params, body) ->
          begin
            let params = List.map (fun v -> `Var v) params in
            let pp_params =
              (List.pp ~pp_start:(fun _ _ -> ())
                 ~pp_stop:(fun _ _ -> ())
                 ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ", ")
                 Lang.Expr.pp_typed_param) in
            match cons, params with
            | _, [] ->
          fmt {|
            | %s ->
|} cons;
            | "::", [h; t] ->
          fmt {|
            | (%a) :: (%a) ->
|}        Lang.Expr.pp_typed_param h
          Lang.Expr.pp_typed_param t
            | cons, _ :: _ ->
          fmt {|
            | %s (%a) ->
|} cons pp_params  params;
          end;
          let env = env @ params in
          loop ~observe env body
        ) cases
      | `Write (arr, offs, vl, body) ->
        let () =
          let id = id () in
          let heap = print_heap env in
          let env = print_env env in
          if observe then begin
            fmt {|
          __observe %d [%s] [%s];
        |} id env heap
          end;
          fmt {|
            %s.(%s) <- %a;
        |} arr offs
            Lang.Expr.pp vl in
        loop ~observe env body
    in
    loop ~observe:true prog.args prog.body;

    fmt "\nlet () = ignore (%s %s); __marshal ()"
      prog.name input;
    
    Buffer.contents buf

  let generate_trace str : state list =
    let open Bos in
    OS.Cmd.run_io Cmd.(v "ocaml" % "-stdin") (OS.Cmd.in_string str)
    |> OS.Cmd.out_string |> Result.get_exn |> fst |> Fun.flip Marshal.from_string 0


  let trace ?prelude prog input =
    encode ?prelude prog input
    |> generate_trace 

  let bitrace (prog1: Lang.Expr.t Lang.Program.t) (prog2: Lang.Expr.t Lang.Program.t) =
    assert Equal.(poly prog1.args prog2.args);
    assert Equal.(poly prog1.converters prog2.converters);

    let input = generate_random_args prog1.converters prog1.args in
    let trace1 = trace prog1 input in
    let trace2 = trace prog2 input in
    (trace1, trace2)

end

module Symbol = struct
  type t = Symbol of string

  let prelude = {|
    type symbol = Symbol of string
    let __enc_symbol v = Symbol v
|}

  let tname = "symbol"

  let pp fmt (Symbol s) = Format.fprintf fmt {| (Symbol "%s") |} s
  let equal (Symbol s1) (Symbol s2)  = String.equal s1 s2
  let fresh =
    let id = ref 0 in
    fun () -> incr id; Symbol (Printf.sprintf "symbol_%d" !id)

end

include Make(Symbol)
