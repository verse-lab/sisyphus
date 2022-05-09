<p align="center"><img width="70%" src="https://github.com/verse-lab/proof-repair/raw/master/sisyphus-logo.png" alt="sisyphus-logo" /></p>
<h1 align="center">Sisyphus: Proof Repair at Scale</h1>


Idea: Repair proofs of programs after refactoring.


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

## Project structure
```
.
├── bin/                        End user interface (CLI) to tool
├── lib/
│   ├── archived/               Old code to synthesise and generate proof patches
│   ├── dynamic/                Dynamic trace-based program equivalence generator
│   ├── interactive/            Interactive REPL for stepping through proofs
│   ├── logic/                  Unified encoding of proof and program expressions
│   └── proof_parser/           Parser for a specific subset of Coq Proofs
|
├── test/                       Integration tests of all main components
|
├── resources/                  Common resources used by the tool
└── readme.md

12 directories, 15 files
```

## Requirements

| Packages         |    Version | Notes                                       |
| :--------------- | :--------- | :------------------------------------------ |
| cmdliner         |      1.0.4 | important otherwise coq-serapi will crash   |
| coq              |     8.15.1 |                                             |
| coq-serapi       |            |                                             |
| coq-cfml         |   20220112 |                                             |
| coq-cfml-basis   |   20220112 |                                             |
| cfml             |   20220112 |                                             |
| containers       |        3.7 |                                             |
| nottui           |        0.2 |                                             |
| iter             |        1.4 |                                             |
| bos              |      0.2.1 |                                             |
| alcotest         |      1.5.0 |                                             |
| z3               |     4.8.14 |                                             |
| sedlex           |        2.5 |                                             |
| ppx_blob         |            |                                             |

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
