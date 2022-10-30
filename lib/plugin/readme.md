# Plugin
This module defines a Coq plugin for testing out the ultimate reduction algorithm in a Coq module.

To use it, for a Coq project in the `resources/**/` directory, update
the `_CoqProject` to have the following:

```bash
-I ../../_build/default/lib/proof_reduction
-I ../../_build/default/lib/plugin

../../lib/plugin/printreduced.ml
```

Then, in your Coq script, add the following declarations:

```coq
Declare ML Module "proof_reduction".
Declare ML Module "printreduced".
```

Then in your proof script, you can use the `print_reduced` tactic or
the `PrintReduced` command.
