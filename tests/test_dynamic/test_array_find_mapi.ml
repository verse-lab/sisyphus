open Containers

module T = Testing_utils.Make (struct let name = "array_find_mapi" end)



let () = T.add_test "array_find_mapi can be traced without error" (fun () ->
  let prog_old =
    IO.with_in "../../resources/find_mapi/find_mapi_old.ml" IO.read_all
    |> Lang.Sanitizer.parse_str in
  let prog_new =
    IO.with_in "../../resources/find_mapi/find_mapi_new.ml" IO.read_all
    |> Lang.Sanitizer.parse_str in

  let _matcher = Dynamic.build_alignment ~deps:[
    "../../resources/common/sseq.ml";
    "../../resources/common/combinators.ml";
    "../../resources/common/opt.ml"
  ] ~old_program:prog_old ~new_program:prog_new () in

  Alcotest.(check unit) "program can be without exception" () ()
)

let () = T.add_test "array_find_mapi tracing works as expected" (fun () ->
  let prog_old =
    IO.with_in "../../resources/find_mapi/find_mapi_old.ml" IO.read_all
    |> Lang.Sanitizer.parse_str in
  let prog_new =
    IO.with_in "../../resources/find_mapi/find_mapi_new.ml" IO.read_all
    |> Lang.Sanitizer.parse_str in

  let matcher = Dynamic.build_alignment ~deps:[
    "../../resources/common/sseq.ml";
    "../../resources/common/combinators.ml";
    "../../resources/common/opt.ml"
  ]
    ~old_program:prog_old ~new_program:prog_new () in

  let matches = Dynamic.Matcher.find_aligned_range `Right matcher (0,1)  in

  Alcotest.(check (pair int int)) "aligned range is as large as possible" (0,2)
    matches
)

let () = T.run ()
