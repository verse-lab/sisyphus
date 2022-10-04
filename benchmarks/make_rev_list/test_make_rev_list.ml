module T = Benchmark_utils.Make (struct let name = "make_rev_list" end)

let () =
  T.add_test "make_rev_list"
    (Benchmark_utils.sisyphus_runs_on
       ~path:"../../resources/make_rev_list"
       ~coq_name:"ProofsMakeRevList")

let () =
  Benchmark_utils.run "make_rev_list_test"
