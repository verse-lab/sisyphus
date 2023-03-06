# Sisyphus

- [Sisyphus](#sisyphus)
  - [Artefact Instructions](#artefact-instructions)
    - [Setting up (Docker)](#setting-up-docker)
    - [Running Sisyphus and individual benchmarks (kick-the-tires)](#running-sisyphus-and-individual-benchmarks-kick-the-tires)
    - [Running all benchmarks and viewing repaired proofs](#running-all-benchmarks-and-viewing-repaired-proofs)
    - [Viewing the results table](#viewing-the-results-table)
    - [Calculating source code stats](#calculating-source-code-stats)
  - [Extending Sisyphus](#extending-sisyphus)
    - [Documentation](#documentation)
    - [Adding new benchmarks](#adding-new-benchmarks)
    - [Navigating the project](#navigating-the-project)
- [Old README](#old-readme)
  - [Setup](#setup)
  - [Building and Running Benchmarks](#building-and-running-benchmarks)
  - [Project structure](#project-structure)
  - [Requirements](#requirements)

## Artefact Instructions

Sisyphus is a functional, reusable and modular project for automated
repair of Coq proofs. 

We have taken care to make sure that Sisyphus' results are fully
reproducible, providing a self-contained Docker file to automate
setting up the development environment.

The rest of this guide will instruct the reader how to build and
produce the results presented in the paper using the Dockerfile.

### Setting up (Docker)

To build the docker image from our provided docker-file, simply run:

```bash
$ docker build -t sisyphus .

Sending build context to Docker daemon  ...
Step 1/15 : From ocaml/opam:debian-11-Ocaml-4.12
...
Successfully built 3940cd4a560a
Successfully tagged sisyphus:latest
```

This command will build a new docker image for Sisyphus, downloading
any required system dependencies and OCaml packages, and building
Sisyphus. This process will take approximately 10 minutes on a 
commodity laptop.

Once the image has been built, you can launch a container using the
image:

```bash
$ docker run --rm -it sisyphus bash

opam@7da388f79f20:~$ ls
LICENSE  _build  benchmarks  bin  dune-project  lib  opam-repository  readme.md  resources  scripts  sisyphus.opam  tests
```

To make sure all subsequent commands run correctly, make sure to run the
following before proceeding:

```
$ eval $(opam env)
```

The subsequent steps of this guide will assume that you are operating
inside this container and will show how to run Sisyphus and produce
the benchmark results.


### Running Sisyphus and individual benchmarks (kick-the-tires)

Once in the docker container, the main Sisyphus binary is available
through the source file `bin/main.ml`, which provides a nice
fully-documented CLI interface to the tool and any parameters it
expects:

```bash
dune exec -- ./bin/main.exe --help
NAME
       sisyphus

SYNOPSIS
       sisyphus [OPTION]... OLD_PROGRAM NEW_PROGRAM COQ_DIR COQ_LIB_NAME
       COQ_OLD_PROOF COQ_NEW_PROOF_STUB COQ_OUT_FILE

       COQ_DIR (required)
           COQ_DIR is the path to the root of the coq library under which the
           proof lives.

       COQ_LIB_NAME (required)
           COQ_LIB_NAME is the name of the coq library in which the proof
           should live.
```

Our testing harness provides a simple interface for actually running Sisyphus on each one of the programs in our evaluation (found under `resources/`):

```bash
$ dune runtest ./benchmarks/<program-name>/
```

Running the above command will create a new temporary directory, copy
over the original files from `resources/`, then run Sisyphus on these
files to produce a repaired proof, and finally check that the
resulting project, with the repaired proof, now compiles.

For example:
```bash
$ dune runtest ./benchmarks/tree_to_array

ASSERT Sisyphus builds project
  [OK]          tree_to_array          0   tree_to_array.

Test Successful in 139.899s. 1 test run.
```

The temporary directory is cleaned up after the test completes -- we
will see how to view the produced repaired proofs in the command for
running all benchmarks in the next section.

### Running all benchmarks and viewing repaired proofs

We provide an executable under `benchmarks/table/table.ml` that runs
all the benchmarks and collects the stats for the tables in the paper.

First, we must create a temporary directory for the repair outputs to be placed:

```bash
$ mkdir /tmp/repaired
```

Once that is done, we can now run all the benchmarks using the following command:

```bash
$ dune exec -- ./benchmarks/table/table.exe -dir=/tmp/repaired
...
```

This command takes around an hour as the benchmark Coq project must be
built and compiled before each repair can proceed.

Once it has completed, the `/tmp/repaired/` directory should now be
populated with both the repaired projects (under each directory), and
stats for each benchmark (in `<benchmark-name>.csv`).

```bash
opam@c3afcc4630be:~$ ls /tmp/repaired/
array_exists               array_foldi                array_of_rev_list_stats.txt  make_rev_list            sll_of_array_stats.txt   stack_reverse
array_exists_stats.txt     array_foldi_stats.txt      array_partition              make_rev_list_stats.txt  sll_partition            stack_reverse_stats.txt
array_find_mapi_stats.txt  array_is_sorted            array_partition_stats.txt    seq_to_array             sll_partition_stats.txt  stats.csv
array_findi                array_is_sorted_stats.txt  common                       seq_to_array_stats.txt   stack_filter             tree_to_array
array_findi_stats.txt      array_of_rev_list          find_mapi                    sll_of_array             stack_filter_stats.txt   tree_to_array_stats.txt
```

The file `stats.csv` contains a single table with the aggregation of
all results of all benchmarks, and contains the data that corresponds
to the results in the table.

The `common` directory contains the common OCaml files and Coq library that is used by all the benchmarks. Utility functions for each datastructure are defined in dedicated OCaml files (e.g. `arr.ml`, `lst.ml`) along with their Coq proofs (e.g. `Verify_arr.v`, `Verify_lst.v`). The directory also includes the `Tactics.v` library that wraps CFML tactics into more convenient forms, and `Solver.v` which provides user-supplied tactics to dispatch left-over obligations. Note that `Solver.v` can be customized to provide more powerful tactics to solve __all__ obligations. 

Each of the directories contains old and repaired versions of the program and proofs, along with some compiled object files. For example, the `array_exists` example consists of the old OCaml program (`array_exists_old.ml`) and its corresponding proof (`Verify_array_exists_old.v`), along the new program (`array_exists_new.ml`) and its Sisyphus-generated proof (`Verify_array_exists_new.v`). A `_CoqProject` file is also provided to allow easier use with ProofGeneral.

```bash
opam@c3afcc4630be:~$ ls /tmp/repaired/array_exists
array_exists_old.ml  array_exists_new.ml Verify_array_exists_old.v Verify_array_exists_new.v _CoqProject
...
```

### Viewing the results table

We provide a helper script under `scripts/gen_table.py` that pretty
prints the statistics and can be used to cross reference the data in
our paper.

```
$ python3 ./scripts/gen_table.py /tmp/repaired/stats.csv 

    \begin{center}
     \begin{tabular}[t]{lccccccccccccc}
       \toprule
      Example & Data Structures & Refactoring & For/While & HOF & Heap & Pure & Total & # Admits (# Obligations) & Synthesis & Reduction & Pruning & Solver & Total \\
      ...
```

Naturally, as these record raw clock times, there will be some
variation between machines and on multiple runs, but the overall
trends and orders of magnitude between the different components of
Sisyphus will remain the same.

### Calculating source code stats

Near section 5, we present a table of the rounded sizes in terms of
LoC of each component of Sisyphus.

```
$ find ./lib/  -name '*.ml' | grep -v 'main.ml'| xargs cat | wc -l
18783
```

The directories correspond to the sections in the paper as follows:

 - Proof Skeleton Generation (3.1) -- `lib/proof_generator, lib/proof_spec`
 - Program Alignment (3.2) -- `lib/dynamic`
 - Expression Generator (3.3) -- `lib/expr_generator, ./lib/lang`
 - Reduction (4.1) -- `lib/proof_reduction`
 - Proof driven test-extraction for CFML (4.2, 4.3) -- `lib/proof_analysis (sans lib/proof_analysis/proof_analysis.ml)`
 - Reflection & extraction for CFML -- `lib/proof_analysis/proof_analysis.ml` and `lib/proof_utils/proof_cfml.ml`
 - Miscellanea -- `lib/configuration/`, `lib/utils`, `lib/coq`, `lib/proof_parser`, `lib/proof_utils/ (sans lib/proof_utils/proof_cfml.ml)`


Because Sisyphus' implementation doesn't cleanly partition into the
division used in the paper for clarity (for example, different parts
of `lib/proof_analysis`, sometimes within the same file, correspond to
our general proof-driven testing procedure, and other parts correspond
to our CFML embedding), the LoC by sub-directories won't exactly match
the decomposition in the paper, but the broad pattern will hold.

## Extending Sisyphus
Sisyphus is not just a write-once static artefact, but instead is
built to be easy to extend and build upon for future researchers: its
key interfaces are documented using `odoc`, and its readme comes with
detailed instructions on navigating and building on the project.

### Documentation

To build the documentation, run the following from within the docker
container:
```
$ opam install odoc

$ dune build @doc
```

The build documentation is available under
`_build/defualt/_doc/_html`.

To view it locally, *without closing your docker container*, run the
following on a different terminal on your *host* machine (i.e not inside the container).

First, use `docker container list` to get the id of the docker container:
```
$ docker container list

CONTAINER ID   IMAGE                       COMMAND                  CREATED       STATUS      PORTS          NAMES
...
c3afcc4630be   sisyphus:latest             "opam exec -- bash"      3 hours ago   Up 3 hours                 sisyphus
```

Copy the built documentation to your host:
```
$ docker container cp c3afcc4630be:/home/opam/_build/default/_doc/_html ./html
```

Open in your browser:
```
$ firefox ./html/index.html
```

Sisyphus adheres to the standard conventions of OCaml, so most of the
time the meanings of its APIs are explanatory from its name and types,
but for non-trivial interfaces, we provide more detailed documentation
on their usage. For example, have a look at:

- The documentation for the global `Configuration` module
- The documentation for the abstraction over Coq's API `Coq.Proof.PROOF`
- The documentation for our expression generator `Expr_generator`
- The documentation for `Proof_reduction`


### Adding new benchmarks

To add a new benchmark named `my_benchmark`, do the following:

1. Add a new directory under `resources` with the following files:
   - `my_benchmark_old.ml` -- the old version of the program
   - `my_benchmark_new.ml` -- the new version of the program
   - `Verify_my_benchmark_old.v` -- the old version of the proof
   - `Verify_my_benchmark_new.v` -- the new proof stub, which contains only the specification copied from the old proof
   - `dune` -- a dune file that specifies the dependencies of the example (see `resources/array_exists/dune` for an example)
   - NOTE the folowing:
     - the name of the directory should be the same as the name of the example
     - all OCaml programs must annotate all types explicitly and should be written in SSA-style
  
2. Run `dune build @gen-build-rules --auto-promote` to ensure the new example is built correctly with the common dependencies.
  
3. Add a new directory named `benchmarks/my_benchmark`.

4. Add a new file `benchmarks/my_benchmark/test_my_benchmark.ml` with the following
   contents (see `benchmarks/array_exists/test_array_exists.ml` for another example)):

    ```ocaml
    module T = Benchmark_utils.Make (struct let name = "my_benchmark" end)

    let () =
    T.add_test "my_benchmark"
      (Benchmark_utils.sisyphus_runs_on
          ~path:"../../resources/my_benchmark"
          ~coq_name:"ProofsMyBenchmark"
          ~common_path:"../../resources/common"
          ~common_coq_name:"Common")

    let () =
    Benchmark_utils.run "my_benchmark_test"
    ```   

5. Run `dune runtest benchmarks/my_benchmark` to assert that Sisyphus generates a proof for the new benchmark.

### Navigating the project

Finally, we include the original README for the project below, which
describes how a prospective user/developer hoping to build on top of
Sisyphus could build the project and where to look to start extending
it.

Old README
=======================================================


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


