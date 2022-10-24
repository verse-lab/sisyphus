module T = Benchmark_utils.Make (struct let name = "array_map2" end)

let () =
  T.add_test "array_map2_mapi"
    (Benchmark_utils.sisyphus_runs_on
       ~path:"../../resources/array_map2"
       ~coq_name:"ProofsArrayMap2"
       ~common_path:"../../resources/common"
       ~common_coq_name:"Common")

let () =
  Benchmark_utils.run "array_map2_test"
