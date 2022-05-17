open Containers
open Proof_spec.Script

let () =
  let proof_str = IO.with_in "../../resources/seq_to_array/Verify_seq_to_array_old.v" IO.read_all in
  let dir = "../../_build/default/resources/seq_to_array" in

  let parsed_script = Proof_parser.Parser.parse proof_str dir in
  pp_parsed_script parsed_script;
  ()
