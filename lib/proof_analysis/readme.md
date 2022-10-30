# Proof analysis
This module defines an extraction mechanism to convert a partially
evaluated Coq proof term into an executable OCaml test specification:

```ocaml
(* construct a evaluatable test specification for the invariant *)
let testf =
  let coq_env = Proof_context.env t in
  let inv_spec = Pair.map String.lowercase_ascii (List.map fst) inv_ty in
  Proof_analysis.analyse coq_env lambda_env higher_order_functions obs pre_heap inv_spec reduced in
```
