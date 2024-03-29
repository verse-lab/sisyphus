[@@@warning "-26-33-27"]
open Containers
module IntMap = Map.Make(Int)

let () =
  let matcher =
    let old_program =
      IO.with_in "../../resources/seq_to_array/seq_to_array_old.ml" IO.read_all
      |> Lang.Sanitizer.parse_str in
    let new_program =
      IO.with_in "../../resources/seq_to_array/seq_to_array_new.ml" IO.read_all
      |> Lang.Sanitizer.parse_str in
  Dynamic.build_alignment
    ~deps:["../../resources/seq_to_array/common.ml"]
    ~old_program
    ~new_program () in
  let mapping = Dynamic.Matcher.top_k ~k:4 `Right matcher in

  let (st,ed) = Dynamic.Matcher.find_aligned_range `Right matcher (5,6) in

  Format.printf "pair (%d,%d)\n" st ed;

  IntMap.iter (fun l r ->
    Format.printf "for program point %d:\n" l;
    List.iter (fun (r, score) ->
      Format.printf "\t- %d: %f\n" r score;
    ) r;
  ) mapping;
  ()
