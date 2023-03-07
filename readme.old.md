# README
(Note: this is the readme of the project, if you are looking for the artefact readme, see `readme.md`)

Idea: Repair proofs of programs after refactoring.

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

## Building and Running Benchmarks

Once you have installed Sisyphus, to build the project, simply call dune:

```
dune build
```

Then, to run the benchmarks:

```
dune runtest
```

To run a particular benchmark, simply run:

```
dune runtest ./benchmarks/<name-of-benchmark>
```

To update the build rules (for example, when you update resources/common, or add a new example):

```
dune build @gen-build-rules --auto-promote
```

Note: when running the benchmarks, you may also want to enable the
`SIS_FAST_BENCHMARK=1` in your environment, to avoid the benchmarks
building the common directory repeatedly on each test.

## Project structure
```
.
|-- LICENSE
|-- readme.md
|-- dune-project
|-- benchmarks
|-- resources
|-- bin
|-- lib
|   |-- dune
|   |-- coq
|   |-- dynamic
|   |-- expr_generator
|   |-- lang
|   |-- plugin
|   |-- proof_analysis
|   |-- proof_generator
|   |-- proof_parser
|   |-- proof_reduction
|   |-- proof_spec
|   |-- proof_utils
|   |-- configuration
|   `-- utils
|-- scripts
`-- sisyphus.opam
```

Most of the magic happens in the `./lib` directory:

| Directory       | Description                                                           |
|-----------------|-----------------------------------------------------------------------|
| coq             | Safe wrapper over Coq API                                             |
| dynamic         | Dynamic execution and tracing of OCaml programs                       |
| expr_generator  | Enumerative synthesis of expressions                                  |
| lang            | Simplified OCaml AST and types                                        |
| plugin          | Coq Plugin to perform Ultimate-reduction                              |
| proof_analysis  | Performs analysis of Coq proof terms (proof reduction etc.)           |
| proof_generator | Synthesises new proof scripts for a program                           |
| proof_parser    | Parses old proof scripts using the Coq API                            |
| proof_reduction | Vendored copy of Coq reduction code extended to do Ultimate-reduction |
| proof_spec      | Simplified encoding of CFML specifications                            |
| proof_utils     | Collection of utilities for manipulating Coq objects from OCaml       |
| configuration   | Generic configuration, preferences and logging options for the tool   |
| utils           | Generic utilities used throughout the project                         |


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


