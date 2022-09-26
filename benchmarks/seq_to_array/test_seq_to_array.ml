module T = Benchmark_utils.Make (struct let name = "seq_to_array" end)

let () =
  T.add_test "seq_to_array"
    (Benchmark_utils.sisyphus_runs_on
       ~path:"../../resources/seq_to_array"
       ~coq_name:"Proofs")

let () =
    Benchmark_utils.run "seq_to_array_test"
