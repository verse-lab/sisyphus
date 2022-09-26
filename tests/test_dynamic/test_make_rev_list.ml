open Containers

module T = Testing_utils.Make (struct let name = "make_rev_list" end)



let () = T.add_test "make_rev_list can be traced without error" (fun () ->
  let prog_old =
    IO.with_in "../../resources/make_rev_list/make_rev_list_old.ml" IO.read_all
    |> Lang.Sanitizer.parse_str in
  let prog_new =
    IO.with_in "../../resources/make_rev_list/make_rev_list_new.ml" IO.read_all
    |> Lang.Sanitizer.parse_str in

  let _matcher = Dynamic.build_alignment ~deps:["../../resources/make_rev_list/common.ml"]
                   ~old_program:prog_old ~new_program:prog_new () in
 
  Alcotest.(check unit) "program can be without exception" () ()
)


let () = T.run ()
