module T = Benchmark_utils.Make (struct let name = "array_exists" end)

let () =
  T.add_test "array_exists"
    (Benchmark_utils.sisyphus_runs_on
       ~path:"../../resources/array_exists"
       ~coq_name:"ProofsArrayExists"
       ~common_path:"../../resources/common"
       ~common_coq_name:"Common")

let () =
  Benchmark_utils.run "array_exists_test"
