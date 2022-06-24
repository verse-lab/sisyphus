# Coq
This module provides an simplified API to programatically call Coq from OCaml.

The main interface to the module is through the functions in  `Coq.Proof`:

```ocaml
let module Ctx = Coq.Proof.make [] in

Ctx.add "Lemma add1: 1 + 1 = 2.";
Ctx.add "Proof.";
Ctx.add "   auto.";
Ctx.add "Qed.";
Ctx.exec ();
```
