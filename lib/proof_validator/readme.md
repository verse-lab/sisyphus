# Proof validator

This library encapsulates an automated decision procedure to check the
validity of candidate invariants by sending them to Z3.

The main interface to the library is through `Proof_validator.build_validator`:

```ocaml
let validator = Proof_validator.build_validator data in
validator (target_pure, target_expr)
```


