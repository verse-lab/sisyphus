module T = Benchmark_utils.Make (struct let name = "array_find_mapi" end)

let () =
  T.add_test "array_find_mapi"
    (Benchmark_utils.sisyphus_runs_on
       ~path:"../../resources/find_mapi"
       ~coq_name:"ProofsFindMapi"
       ~common_path:"../../resources/common"
       ~common_coq_name:"Common")

let () =
  Benchmark_utils.run "array_find_mapi_test"
