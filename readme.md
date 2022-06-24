<p align="center"><img width="70%" src="https://github.com/verse-lab/proof-repair/raw/master/sisyphus-logo.png" alt="sisyphus-logo" /></p>
<h1 align="center">Sisyphus: Proof Repair at Scale</h1>

Idea: Repair proofs of programs after refactoring.

## Project structure
```
.
├── bin                               End user interface (CLI) to tool
├── lib    
│   ├── proof_generator               Sisyphus Proof Generation Engine
|   |
│   ├── lang                          Simplified OCaml AST definition
│   ├── proof_spec                    Simplified encoding of Proof scripts        
|   |
│   ├── coq                           Simplified API to Coq
|   |
│   ├── expr_generator                Enumerative synthesis of invariants
|   |
│   ├── dynamic                       Program alignment of OCaml programs
|   |
│   ├── proof_parser                  Parsing proof scripts to internal representation 
|   |
│   ├── proof_validator               SMT-based checker of candidate invariants 
|   |
│   ├── proof_reduction               Vendored version of Coq reduction engine
│   └── plugin                        Coq Plugin for Ultimate Reduction
|
├── resources                         Example programs for proof-repair 
|
├── test                              Integration tests for Sisyphus
|
├── LICENSE
├── readme.md
├── dune-project
└── sisyphus.opam

39 directories, 21 files
```

## Requirements

| Packages       | Version  | Notes                                     |
|:---------------|:---------|:------------------------------------------|
| cmdliner       | 1.0.4    | important otherwise coq-serapi will crash |
| coq            | 8.15.1   |                                           |
| coq-serapi     |          |                                           |
| coq-cfml       | 20220112 |                                           |
| coq-cfml-basis | 20220112 |                                           |
| cfml           | 20220112 |                                           |
| containers     | 3.7      |                                           |
| nottui         | 0.2      |                                           |
| iter           | 1.4      |                                           |
| bos            | 0.2.1    |                                           |
| alcotest       | 1.5.0    |                                           |
| z3             | 4.8.14   |                                           |
| sedlex         | 2.5      |                                           |
| ppx_blob       | 0.7.2    |                                           |

## Setup

Setting up the project is mostly automated by the opam file.

Simply create a new local opam switch, and opam will handle installing all the dependencies:
```
opam switch create . 4.12.0
```

Note: you will need the coq-released repo installed and set as a default for fresh-switches, otherwise you will get a complaint about unknown packages cfml:
```
opam repo add coq-released https://coq.inria.fr/opam/released --all --set-default
```


## High level approach

Input: A program P, and a proof Q, and a refactored program P'.

Algorithm:

1. Generate a proof template Q' (with holes) from P'.
   - *Justification:* Proof structures closely follow the program structure.
2. Use dynamic execution traces to identify equivalent program points between P and P'.
   - *Justification:* Formally proving program equivalence in general is a difficult problem, we approximate it cheaply dynamically
3. From equivalent program points, determine equivalent /proof/ points between Q and Q'.
   - *Justification:* While sound equivalences between proofs is a very theoretical subject (HTT), we can extend our cheap approximate dynamic equivalences to cheap approximate equivalences between proofs.
4. Fill in the holes in Q' using enumerative synthesis, seeded from expressions found in equivalent points in Q.
   - *Justification:* Proofs may make use of completely different expressions and theorems than the programs they verify, however the proofs of two functionally equivalent programs are likely to make use of similar invariants etc.
