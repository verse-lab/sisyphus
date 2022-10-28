# Configuration

This module defines a centralised store of configuration parameters to
customise the behaviour of Sisyphus, and for debugging purposes.


```ocaml
(* initialise the configuration module *)
let _ = Configuration.initialize () in 

...

(* Dump output to a user-specified dump directory (SIS_DUMP_DIR):  *)
let _ = 
    Configuration.dump_output "filename" 
        (fun f -> f "hello world %d" 10) in

...
```
