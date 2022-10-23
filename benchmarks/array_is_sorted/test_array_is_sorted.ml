module T = Benchmark_utils.Make (struct let name = "array_is_sorted" end)

let () =
  T.add_test "array_is_sorted"
    (Benchmark_utils.sisyphus_runs_on
       ~path:"../../resources/array_is_sorted"
       ~coq_name:"ProofsArrayIsSorted"
       ~common_path:"../../resources/common"
       ~common_coq_name:"Common")

let () =
  Benchmark_utils.run "array_is_sorted_test"
