module T = Benchmark_utils.Make (struct let name = "sll_partition" end)

let () =
  T.add_test "sll_partition"
    (Benchmark_utils.sisyphus_runs_on
       ~path:"../../resources/sll_partition"
       ~coq_name:"ProofsSllPartition"
       ~common_path:"../../resources/common"
       ~common_coq_name:"Common")


let () =
    Benchmark_utils.run "sll_partition_test"
