module T = Benchmark_utils.Make (struct let name = "array_findi" end)

let () =
  T.add_test "array_findi"
    (Benchmark_utils.sisyphus_runs_on
       ~path:"../../resources/array_findi"
       ~coq_name:"ProofsArrayFindi"
       ~common_path:"../../resources/common"
       ~common_coq_name:"Common")


let () =
    Benchmark_utils.run "array_findi_test"
