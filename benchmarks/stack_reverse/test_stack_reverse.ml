module T = Benchmark_utils.Make (struct let name = "stack_reverse" end)

let () =
  T.add_test "stack_reverse"
    (Benchmark_utils.sisyphus_runs_on
       ~path:"../../resources/stack_reverse"
       ~coq_name:"ProofsStackReverse"
       ~common_path:"../../resources/common"
       ~common_coq_name:"Common")

let () =
    Benchmark_utils.run "stack_reverse_test"
