open Containers
open Program.Expr

let gen_function_args (ints, lists, bools, vars) args =
  List.map (function IntTy -> List.map (fun v -> IntExpr v) ints
                   | ListTy -> List.map (fun v -> ListExpr v) lists
                   | BoolTy -> List.map (fun v -> BoolExpr v) bools
                   | VarTy -> List.map (fun v -> Var v) vars) args
  |> List.cartesian_product
  |> Seq.of_list

let generate_ints ?(int_functions=[])  (ints, lists, bools, vars) =
  let new_ariths =
    let ints = (Seq.of_list ints) in
    Seq.flat_map (fun i1 ->
      Seq.flat_map (fun i2 ->
        Seq.of_list [Add (i1, i2); Sub (i1, i2)]
      ) ints
    ) ints in
  let new_funs =
    Seq.flat_map (fun (name,args) ->
      gen_function_args (ints, lists, bools, vars) args
      |> Seq.map (fun args -> AppInt (name, args))
    ) (Seq.of_list int_functions) in
  Seq.interleave new_ariths new_funs

let generate_lists ?(list_functions=[])  (ints, lists, bools, vars) =
  Seq.flat_map (fun (name,args) ->
    gen_function_args (ints, lists, bools, vars) args
    |> Seq.map (fun args -> AppList (name, args))
  ) (Seq.of_list list_functions)

let generate_bool ?(bool_functions=[]) (ints, lists, bools, vars) =
  let new_ariths =
    let ints = (Seq.of_list ints) in
    Seq.flat_map (fun i1 ->
      Seq.flat_map (fun i2 ->
        Seq.of_list [
          Lt (i1, i2);
          Le (i1, i2); 
          Gt (i1, i2); 
          Ge (i1, i2); 
          IntEq (i1, i2)
        ]
      ) ints
    ) ints in
  let new_lists =
    let lists = (Seq.of_list lists) in
    Seq.flat_map (fun i1 -> Seq.flat_map (fun i2 -> Seq.of_list [ ListEq (i1, i2) ] ) lists ) lists in
  let new_funs =
    Seq.flat_map (fun (name,args) ->
      gen_function_args (ints, lists, bools, vars) args
      |> Seq.map (fun args -> AppBool (name, args))
    ) (Seq.of_list bool_functions) in
  Seq.interleave
    (Seq.interleave new_ariths new_lists)
    new_funs

let generate_lazy_step_fixed_bools ?int_functions ?list_functions ?bool_functions:_ ((ints, lists, bools, vars) as state) =
  (Seq.append (Seq.of_list ints) @@ generate_ints ?int_functions state,
   Seq.append (Seq.of_list lists) @@ generate_lists ?list_functions state,
   bools, vars)

let generate_lazy_step ?int_functions ?list_functions  ?bool_functions ((ints, lists, bools, vars) as state) =
  (Seq.append (Seq.of_list ints) @@ generate_ints ?int_functions state,
   Seq.append (Seq.of_list lists) @@ generate_lists ?list_functions state,
   Seq.append (Seq.of_list bools) @@ generate_bool ?bool_functions state, vars)

let generate_step_fixed_bools  ?int_functions ?list_functions  ?bool_functions state =
  let (ints, lists, bools, vars) = generate_lazy_step_fixed_bools  ?int_functions ?list_functions  ?bool_functions state in
  (Seq.to_list ints, Seq.to_list lists, bools, vars)

let generate_step  ?int_functions ?list_functions  ?bool_functions state =
  let (ints, lists, bools, vars) = generate_lazy_step  ?int_functions ?list_functions  ?bool_functions state in
  (Seq.to_list ints, Seq.to_list lists, Seq.to_list bools, vars)
