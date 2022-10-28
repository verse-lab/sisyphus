# Proof Reduction

This module vendors several files from Coq's internal reduction
mechanism, extending them to support reducing through opaque proof
terms.

```ocaml
...
let evd = Evd.from_env env in
let (evd, reduced) =
    Proof_reduction.reduce ~filter
      env evd (Evd.MiniEConstr.of_constr term) in
let trm = (EConstr.to_constr evd reduced) in
...
```
