open Containers
open Proof_spec.Script

let () =
  let proof_str = IO.with_in "../../resources/seq_to_array/Verify_seq_to_array_old.v" IO.read_all in
  let dir = "../../_build/default/resources/seq_to_array" in
  let module Ctx =
    Coq.Proof.Make(struct
      let verbose = false
      let libs = [
        Coq.Coqlib.make
          ~path:(Fpath.of_string dir |> Result.get_exn)
          "Proofs"
      ]
    end) in

  let parsed_script = Proof_parser.Parser.parse (module Ctx) proof_str in
  pp_parsed_script parsed_script;
  ()
