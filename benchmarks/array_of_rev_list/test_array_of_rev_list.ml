module T = Benchmark_utils.Make (struct let name = "array_of_rev_list" end)

let () =
  T.add_test "array_of_rev_list"
    (Benchmark_utils.sisyphus_runs_on
       ~path:"../../resources/array_of_rev_list"
       ~coq_name:"ProofsArrayOfRevList"
       ~common_path:"../../resources/common"
       ~common_coq_name:"Common")

let () =
  Benchmark_utils.run "array_of_rev_list_test"
