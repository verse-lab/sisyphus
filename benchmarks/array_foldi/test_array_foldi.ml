module T = Benchmark_utils.Make (struct let name = "array_foldi" end)

let () =
  T.add_test "array_foldi"
    (Benchmark_utils.sisyphus_runs_on
       ~path:"../../resources/array_foldi"
       ~coq_name:"ProofsArrayFoldi"
       ~common_path:"../../resources/common"
       ~common_coq_name:"Common")


let () =
    Benchmark_utils.run "array_foldi_test"
