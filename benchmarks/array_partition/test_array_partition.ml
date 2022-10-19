module T = Benchmark_utils.Make (struct let name = "array_partition" end)

let () =
  T.add_test "array_partition"
    (Benchmark_utils.sisyphus_runs_on
       ~path:"../../resources/array_partition"
       ~coq_name:"ProofsArrayPartition"
       ~common_path:"../../resources/common"
       ~common_coq_name:"Common")

let () =
  Benchmark_utils.run "array_partition_test"
