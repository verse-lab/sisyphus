module T = Benchmark_utils.Make (struct let name = "stack_filter" end)

let () =
  T.add_test "stack_filter"
    (Benchmark_utils.sisyphus_runs_on
       ~path:"../../resources/stack_filter"
       ~coq_name:"ProofsStackFilter"
       ~common_path:"../../resources/common"
       ~common_coq_name:"Common")

let () =
    Benchmark_utils.run "stack_filter_test"
