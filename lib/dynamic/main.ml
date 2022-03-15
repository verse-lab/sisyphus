open Containers

let print_env ((sym, vl): (string * Dynamic.Tracer.value)) =
  Printf.sprintf "%s -> %s"  sym (Dynamic.Tracer.show_value vl)
let print_heap ((sym, vl): (string * Dynamic.Tracer.heaplet)) =
  Printf.sprintf "%s -> %s"  sym (Dynamic.Tracer.show_heaplet vl)

let print_state ((i, env, heap): Dynamic.Tracer.state) =
  print_endline @@ Format.sprintf {|
pos %d:
    env:
	%s
    heap:
	%s
|} i (List.map print_env env |> String.concat "\n\t")
    (List.map print_heap heap |> String.concat "\n\t")

let () =
  let program = IO.with_in "../../resources/seq_to_array/original.ml" IO.read_all in
  let prog = Logic.Sanitizer.parse_str program in
  (* |> Logic.Program.show Logic.Expr.print
   * |> print_endline *)


  Dynamic.Tracer.trace prog
  |> List.iter print_state
