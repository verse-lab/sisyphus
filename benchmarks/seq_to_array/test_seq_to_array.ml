module T = Benchmark_utils.Make (struct let name = "seq_to_array" end)

let () =
  T.add_test "seq_to_array"
    (Benchmark_utils.sisyphus_runs_on
       ~path:"../../resources/seq_to_array"
       ~coq_name:"Proofs"
       ~common_path:"../../resources/common"
       ~common_coq_name:"Common")


let () =
    Benchmark_utils.run "seq_to_array_test"
