# Dynamic
This module provides a API for dynamically constructing program
alignments between OCaml programs. Internally the module leverages the
OCaml compiler pipeline to compile and dynamically trace reified OCaml
programs.

The main interface to the API is through `Dynamic.build_alignment`:

```ocaml
let matcher =
  Dynamic.build_alignment
    ~deps:["../../resources/seq_to_array/common.ml"]
    ~old_program
    ~new_program () in

let mapping = Dynamic.Matcher.top_k ~k:4 `Right matcher in

let (st,ed) = Dynamic.Matcher.find_aligned_range `Right matcher (5,6) in

Format.printf "pair (%d,%d)\n" st ed
```
