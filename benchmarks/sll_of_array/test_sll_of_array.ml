module T = Benchmark_utils.Make (struct let name = "sll_of_array" end)

let () =
  T.add_test "sll_of_array"
    (Benchmark_utils.sisyphus_runs_on
       ~path:"../../resources/sll_of_array"
       ~coq_name:"ProofsSllOfArray"
       ~common_path:"../../resources/common"
       ~common_coq_name:"Common")


let () =
    Benchmark_utils.run "sll_of_array_test"
