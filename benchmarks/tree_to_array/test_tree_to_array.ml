module T = Benchmark_utils.Make (struct let name = "tree_to_array" end)

let () =
  T.add_test "tree_to_array"
    (Benchmark_utils.sisyphus_runs_on
       ~path:"../../resources/tree_to_array"
       ~coq_name:"ProofsTreeToArray"
       ~common_path:"../../resources/common"
       ~common_coq_name:"Common")

let () =
    Benchmark_utils.run "tree_to_array_test"
