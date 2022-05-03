[@@@warning "-26-33-27"]
open Containers
module IntMap = Map.Make(Int)

let () =
  let matcher =
  Dynamic.build_alignment
    ~deps:["../../resources/seq_to_array/common.ml"]
    ~old_program:"../../resources/seq_to_array/seq_to_array_old.ml"
    ~new_program:"../../resources/seq_to_array/seq_to_array_new.ml" () in
  let mapping = Dynamic.Matcher.top_k 3 `Left matcher in


  IntMap.iter (fun l r ->
    Format.printf "for program point %d:\n" l;
    List.iter (fun (r, score) ->
      Format.printf "\t- %d: %f\n" r score;
    ) r;
  ) mapping;
  ()
