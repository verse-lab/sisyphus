[@@@warning "-26"]
open Containers
open Dynamic.Utils

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
  let prog1 =
    IO.with_in "../../resources/seq_to_array/original.ml" IO.read_all
    |> Lang.Sanitizer.parse_str in
  let prog2 =
    IO.with_in "../../resources/seq_to_array/updated.ml" IO.read_all
    |> Lang.Sanitizer.parse_str in


  (* IO.with_out "/tmp/original.ml" (Fun.flip IO.write_line
   *                                   (Dynamic.Tracer.encode prog1 "_"));
   * IO.with_out "/tmp/updated.ml" (Fun.flip IO.write_line
   *                                  (Dynamic.Tracer.encode prog2 "_")); *)

  let trace1, trace2 = Dynamic.Tracer.bitrace prog1 prog2 in

  let matches = Dynamic.Matcher.build trace1 trace2 in
  let print_top_k top_k =
    IntMap.to_iter top_k (fun (lpos, rpos) ->
      Format.printf "%d:\n\t[%a]\n" lpos
        (* (Option.pp (Lang.Program.pp_stmt_line Lang.Expr.print))
         * (Lang.Program.lookup_statement lpos prog1) *)
        (List.pp ~pp_sep:(fun fmt () -> Format.fprintf fmt ";\n\t" ) (fun fmt (rpos, score) ->
           Format.fprintf fmt "%d, %.2f"
             rpos score
             (* (Option.pp (Lang.Program.pp_stmt_line Lang.Expr.print))
              * (Lang.Program.lookup_statement rpos prog2) *)
         )) rpos
    ) in
  print_endline "matches from left to right";
  let top_k = Dynamic.Matcher.top_k 3 `Left matches in
  print_top_k top_k;

  print_endline "matches from right to left";
  let top_k = Dynamic.Matcher.top_k 3 `Right matches in
  print_top_k top_k;


  ()
