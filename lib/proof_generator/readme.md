# Proof Generator

This library defines the main interface of Sisyphus, defining a
function to generate an updated proof script given a pair of modified
programs.

```ocaml
...
let new_proof_contents =
    Proof_generator.Generator.generate
       ~logical_mappings:old_program.logical_mappings 
       ctx new_program in
let new_proof =
    (new_proof_base ^ "\n" ^ new_proof_contents) in
...
```
