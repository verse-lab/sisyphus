(* seq to array *)
(* module TSeq = Benchmark_utils.Make (struct let name = "seq_to_array" end) *)

(* let () = *)
(*   TSeq.add_test "seq_to_array" *)
(*     (Benchmark_utils.sisyphus_runs_on *)
(*        ~path:"../../resources/seq_to_array" *)
(*        ~coq_name:"Proofs" *)
(*        ~common_path:"../../resources/common" *)
(*        ~common_coq_name:"Common") *)


(* let () = *)
(*   Benchmark_utils.run "seq_to_array_test" *)

(* make rev list *)
module TMake = Benchmark_utils.Make (struct let name = "make_rev_list" end)

let () =
  TMake.add_test "make_rev_list"
    (Benchmark_utils.sisyphus_runs_on
       ~path:"../../resources/make_rev_list"
       ~coq_name:"ProofsMakeRevList"
       ~common_path:"../../resources/common"
       ~common_coq_name:"Common")

let () =
  Benchmark_utils.run "make_rev_list_test"
