open Containers

let (|>>) x v i = v x i



let () =
  let proof = 
  IO.with_in "../../resources/seq_to_array/proof_updated_simplified.v" IO.read_all
  |> Proof_parser.parse_str in
  proof.spec
  |> Logic.Proof_sanitizer.convert_spec
  |> Format.to_string Logic.Proof.pp_spec
  |> print_endline;

  proof.proof |> Logic.Proof_sanitizer.convert_proof
  |> List.iter (fun step -> print_endline @@ Logic.Proof.show_step step)

