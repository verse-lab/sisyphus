# Proof parser

This module defines a helper function to parse proof scripts into the
internal representation provided by `Proof_spec`. Internally, this
module delegates to the Coq API to do its parsing (done through
`Coq`).

The main interface to this module is through `Proof_parser.Parser.parse`:

```ocaml
let module Ctx =
  Coq.Proof.Make(struct
    let verbose = false
    let libs = [ .. ]
  end) in

let parsed_script = Proof_parser.Parser.parse (module Ctx) proof_str in

...

```
