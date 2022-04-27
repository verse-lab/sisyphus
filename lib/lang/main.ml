open Containers

let (|>>) x v i = v x i



let () =
  let proof = 
  IO.with_in "../../resources/seq_to_array/proof_updated_simplified.v" IO.read_all
  |> Proof_parser.parse_str in
  proof.spec
  |> Proof.Sanitizer.convert_spec
  |> Format.to_string Proof.Script.pp_spec
  |> print_endline;

  proof.proof |> Proof.Sanitizer.convert_proof
  |> List.iter (fun step -> print_endline @@ Proof.Script.show_step step)

