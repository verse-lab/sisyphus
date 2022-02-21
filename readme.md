# OCaml Proof/Program Repair by Program Synthesis

Doing some experiments.

```
.
├── bin                         main entry point (does nothing atm)
├── lib
│   ├── program                 definition of simplfiied OCaml AST
│   ├── parser                  parses OCaml AST -> our Internal format
│   ├── proof_parser            parsing Coq proof scripts
│   ├── synthesis               bottom-up enumerative synthesis of OCaml expressions
│   └── verification            SMT-based validation of loop invariants
├── readme.md
├── resources
├── test 
└── verification.opam

18 directories, 48 files

```
