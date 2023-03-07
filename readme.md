# Sisyphus
<p align="center"><img width="70%" src="./sisyphus-logo.png" alt="sisyphus-logo" /></p>
<h1 align="center">Sisyphus: Proof Repair at Scale</h1>


- [Sisyphus](#sisyphus)
  - [Artefact Instructions](#artefact-instructions)
    - [Getting Started](#getting-started)
      - [Setting up Docker](#setting-up-docker)
      - [Running Sisyphus and individual benchmarks (kick-the-tires)](#running-sisyphus-and-individual-benchmarks-kick-the-tires)
    - [Step-by-step Instructions](#step-by-step-instructions)
      - [(a): Calculating source code stats](#a-calculating-source-code-stats)
      - [(b): Running all benchmarks and viewing repaired proofs](#b-running-all-benchmarks-and-viewing-repaired-proofs)
      - [(c): Viewing the table of times](#c-viewing-the-table-of-times)
  - [Extending Sisyphus](#extending-sisyphus)
    - [Documentation](#documentation)
    - [Adding new benchmarks](#adding-new-benchmarks)
    - [Navigating the project](#navigating-the-project)

## Artefact Instructions

Sisyphus is a functional, reusable, and extensible framework for
automated repair of Coq proofs.

We have taken care to make sure that Sisyphus' results are fully
reproducible, providing a self-contained Docker file to automate
setting up the development environment.

The rest of this guide will instruct the reader how to build and
produce the results presented in the paper using the Dockerfile.

### Getting Started
#### Setting up Docker

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

#### Running Sisyphus and individual benchmarks (kick-the-tires)

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

### Step-by-step Instructions
The Sisyphus paper contains 3 tables:

- (a) Page 17: Table describing source code statistics
- (b) Page 18: Table describing the number of obligations/effort to complete the proof
- (c) Page 19: Table describing execution times of the artefact 

Our artefact will reproduce the following claims:

- (a): the distribution of source code in our development 
- (b): the number of admits remaining in repaired proofs
- (c): the trends of execution times in the paper

Our artefact cannot reproduce the following claims:

- (b): effort in time taken to complete the proofs -- these times were
  recorded by the developers, and would require a developer to be
  familiar with the frameworks and tooling that we use (Coq, CFML, our
  user_solve tactic).

The subsequent sections describe how to reproduce each table using our
artefact.

#### (a): Calculating source code stats
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

#### (b): Running all benchmarks and viewing repaired proofs

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

Note: If the docker daemon does not have enough memory, the repair
process can sometimes be killed by the linux OOM killer because it
runs out of space. As such, if you find that tasks are failing due to being
SIGKILL-ed, try running again, or increase the memory allocated to
your docker container (we recommend ~8gb)

Once it has completed, the `/tmp/repaired/` directory should now be
populated with both the repaired projects (under each directory), and
stats for each benchmark (in `<benchmark-name>.csv`).

```bash
$ ls --group-directories-first -1 /tmp/repaired/

array_exists/
array_findi/
array_foldi/
array_is_sorted/
array_of_rev_list/
array_partition/
common/
find_mapi/
make_rev_list/
seq_to_array/
sll_of_array/
sll_partition/
stack_filter/
stack_reverse/
tree_to_array/
array_exists_stats.txt
array_find_mapi_stats.txt
array_findi_stats.txt
array_foldi_stats.txt
array_is_sorted_stats.txt
array_of_rev_list_stats.txt
array_partition_stats.txt
make_rev_list_stats.txt
seq_to_array_stats.txt
sll_of_array_stats.txt
sll_partition_stats.txt
stack_filter_stats.txt
stack_reverse_stats.txt
stats.csv
tree_to_array_stats.txt
```

The file `stats.csv` contains a single table with the aggregation of
all results of all benchmarks, and contains the data that corresponds
to the results in (c), which we will discuss in the next section.

You can inspect the resulting directory to view the old and new
programs and the repaired proofs to confirm that the columns in the
table are accurate (i.e that the number of admits for the generated
proof artefacts is correct).

To this end, we briefly describe any important directories you may
want to look at.

- The `common` directory contains the common OCaml files and Coq
  library that is used by all the benchmarks.

  Inside `common`, we provide utility functions for each datastructure
  in dedicated OCaml files (e.g. `arr.ml`, `lst.ml`) along with proofs
  of their correctness in Coq (e.g. `Verify_arr.v`, `Verify_lst.v`).
  
  The `Tactics.v` and `Solver.v` define any tactics and the user
  tactic we use in our experiments.

- Each of the remaining directories correspond to one of the
  benchmarks (for example: `array_exists/`), and contains the old and
  new version of the benchmark program, the old proof and the repaired
  new proof.
  
  As an example, look at the `array_exists` folder:

```bash
$ ls -1 /tmp/repaired/array_exists | grep -v -G '\(.*vo.*\|.*_stub\|.*glob\)'
Array_exists_new_ml.v
Array_exists_old_ml.v
Dummy.v
Verify_array_exists_new.v
Verify_array_exists_old.v
_CoqProject
array_exists_new.ml
array_exists_old.ml
```

  The directory consists of the old OCaml program
  (`array_exists_old.ml`) and its corresponding proof
  (`Verify_array_exists_old.v`), along the new program
  (`array_exists_new.ml`) and its Sisyphus-generated proof
  (`Verify_array_exists_new.v`).
  
  A `_CoqProject` file is also provided to allow easier use with ProofGeneral.
  
  You can cat the `Verify_array_exists_new.v` file to view the proof with its new invariant:
  ```
Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_combinators.

From Common Require Import Tactics Utils Solver Verify_opt.

From ProofsArrayExists Require Import Array_exists_new_ml.

Lemma array_exists_spec :
  forall (A : Type) `{EA : Enc A} (a : array A) (f : func) (l : list A) (fp: A -> bool),
    (forall (a: A),
        SPEC_PURE (f a)
         POST (fun b => \[b = fp a])
    ) ->
  SPEC (array_exists a f)
  PRE (a ~> Array l)
  POST (fun (b : bool) => \[b = List.existsb fp l] \* a ~> Array l).
Proof using (All).
xcf.
xapp.
xletopaque tmp Htmp.
xapp (Common.Verify_combinators.until_upto_spec (unit) (0) ((TLC.LibListZ.length (l))) (tmp) (fun (arg0: int) (arg1: (option (unit))) => \[ (arg1 = (opt_of_bool ((existsb (fp) ((take (arg0) 
(l))))))) ] )).
...
  ```
  In the table in the paper, we report 2 admitted obligations, and the corresponding repaired 
  proof should contain 2 uses of the `admit` tactic.

Note: Our tool conservatively always ends proof scripts with
`Admitted`, even when the proof itself may be complete and can be
completed with `Qed.`. 

#### (c): Viewing the table of times

We provide a helper script under `scripts/gen_table.py` that pretty
prints the run-time statistics generated in the previous section and
can be used to cross reference the results presented in the
corresponding table in our paper.

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

To add a new benchmark, you will need 4 things:
   - an old version of the program
   - a new version of the program
   - an old version of the proof 
   - and a new proof stub, which contains only the specification copied from the old proof

We will illustrate this process by adding a new benchmark
`my_benchmark` implementing a custom array allocation function:
  - old version of the program (`my_benchmark_old.ml`):
  ```ocaml
  (* file: my_benchmark_old.ml *)
  let my_benchmark (v: unit) =
    let (a: int array) = Array.make 0 0 in
    a
  ```
  - new version of the program (`my_benchmark_new.ml`):
  ```ocaml
  (* file: my_benchmark_new.ml *)
  let my_benchmark (v: unit) = [|  |]
  ```
  - an old version of the proof (`Verify_my_benchmark_old.v`):
  ```ocaml
  (* file: Verify_my_benchmark_old.v *)
  Set Implicit Arguments.
  From CFML Require Import WPLib Stdlib.
  From TLC Require Import LibListZ.

  From Common Require Import Tactics Utils Solver.

  From ProofsMyBenchmark Require Import My_benchmark_old_ml.

  Lemma my_benchmark_spec :
    SPEC (my_benchmark tt)
    PRE \[]
    POST (fun a : loc => a ~> Array (@nil int)).
  Proof using (All).
     xcf.
     xalloc arr data Hdata.
     xvals. { sis_generic_solver. }
  Qed.
  ```
  - and the new proof stub (`Verify_my_benchmark_new.v`):
  ```ocaml
  (* file: Verify_my_benchmark_new.v *)
  Set Implicit Arguments.
  From CFML Require Import WPLib Stdlib.
  From TLC Require Import LibListZ.

  From Common Require Import Tactics Utils Solver.

  From ProofsMyBenchmark Require Import My_benchmark_new_ml.

  Lemma my_benchmark_spec :
    SPEC (my_benchmark tt)
    PRE \[]
    POST (fun a : loc => a ~> Array (@nil int)).
  Proof using (All).
  Admitted.
  ```

To add `my_benchmark` to Sisyphus, do the following (run all commands from the project root):

1. Add a new directory `my_benchmark` under `resources` with files as
   described above:
   - `my_benchmark_old.ml` 
   - `my_benchmark_new.ml` 
   - `Verify_my_benchmark_old.v`
   - `Verify_my_benchmark_new.v`

2. Add a dune file `resources/my_benchmark/dune`. 

   The file should have the following contents, describing how to
   build the `my_benchmark` OCaml library, how to produce a Coq
   library representing the `my_benchmark` library and how to compile
   the resulting proofs:

   ```
   (* file: dune *)
   (library (name my_benchmark)
     (libraries common))

   (coq.theory
    (name ProofsMyBenchmark)
    (modules
      My_benchmark_old_ml Verify_my_benchmark_old
      My_benchmark_new_ml Verify_my_benchmark_new
      Dummy)
    (libraries sisyphus.plugin)
    (flags -R resources/common Common)
   )

   (include build-rules.sexp)
   (rule (with-stdout-to build-rules.sexp.gen (run ../../scripts/gen_build_rules.sh)))
   (rule (alias gen-build-rules) (action (diff build-rules.sexp build-rules.sexp.gen)))


   (env
     (dev
       (flags (:standard -w -32 -w -27))))
   ```
   - The structure of the dune file follows a standard form and can
     easily be adapted from the other benchmarks (see
     `resources/array_exists/dune` as an example).
   - Also note the folowing:
     - the name of the directory should be the same as the name of the example
     - all OCaml programs must annotate all types explicitly and
       should be written in SSA-style

3. Add an empty file `resources/my_benchmark/build-rules.sexp` which
   will be populated by the next step:

   ```bash
   $ touch resources/my_benchmark/build-rules.sexp
   ```
  
4. Run `dune build @gen-build-rules --auto-promote` to populate the
   `build-rules.sexp` file with appropriate information.

5. Test that the new benchmarks library compiles with `dune build`
  
6. Add a new directory named `benchmarks/my_benchmark`.

7. Add a new file `benchmarks/my_benchmark/test_my_benchmark.ml` with the following
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
8. Add a dune file `benchmarks/my_benchmark/dune` to inform dune of the new test:

   ```dune
   (tests
    (names test_my_benchmark)
    (libraries alcotest bos containers benchmark_utils)
    (deps ../../bin/main.exe (glob_files_rec ../../resources/*.{ml,v}) (glob_files_rec ../../resources/_CoqProject))
    (preprocess (pps ppx_deriving.std)))
   ```

9. Run `dune runtest benchmarks/my_benchmark` to assert that Sisyphus
   generates a proof for the new benchmark.

   ```bash
   $ dune runtest ./benchmarks/my_benchmark

   ...

   ASSERT Sisyphus builds project
     [OK]          my_benchmark          0   my_benchmark.

   Test Successful in 91.235s. 1 test run.
   ```
(Even though our program was fairly simple, running the benchmark through the harness 
takes a bit of time as it requires Coq to re-compile all the common libraries).

#### Viewing Repaired Proof
Running the above push-button benchmark will create a new temporary
directory, copy over the original files from `resources/`, then run
Sisyphus on these files to produce a repaired proof, and finally check
that the resulting project, with the repaired proof compiles.

As the benchmarks are set up to clean any intermediate files,
including the temporary directory, after they complete, it is not
possible to view the repaired proof using this method.

If you wish to see the repaired files for an individual benchmark then
the process is a little more challenging, as we must run the tool
ourselves:

1. Build the resources directory.

```
$ dune build resources
```

2. Modify
   `_build/default/resources/my_benchmark/Verify_my_benchmark_new.v`
   and remove `Admitted.` (This is done automatically by the
   test-harness)
   
```
$ chmod u+rw _build/default/resources/my_benchmark/Verify_my_benchmark_new.v
$ nano _build/default/resources/my_benchmark/Verify_my_benchmark_new.v
# remove "Admitted." line
```

3. Run the `./bin/main.exe` passing in appropriate arguments:

```
dune exec ./bin/main.exe -- -c Common:./_build/default/resources/common \
    ./_build/default/resources/my_benchmark/my_benchmark_old.ml \
    ./_build/default/resources/my_benchmark/my_benchmark_new.ml \
    ./_build/default/resources/my_benchmark/ ProofsMyBenchmark  \
    Verify_my_benchmark_old.v Verify_my_benchmark_new.v \
    result.v
```
4. The repaired proof will be under `_build/default/resources/my_benchmark/result.v`:

```
$ cat _build/default/resources/my_benchmark/result.v

  Set Implicit Arguments.
  From CFML Require Import WPLib Stdlib.
  From TLC Require Import LibListZ.

  From Common Require Import Tactics Utils Solver.

  From ProofsMyBenchmark Require Import My_benchmark_new_ml.

  Lemma my_benchmark_spec :
    SPEC (my_benchmark tt)
    PRE \[]
    POST (fun a : loc => a ~> Array (@nil int)).
  Proof using (All).
  xcf.
  xvalemptyarr.
  Admitted.
```

Note: The above proof is complete and the `Admitted` could be replaced
by `Qed`, but our tool conservatively always outputs `Admitted`.

### Navigating the project

Finally, we include the original README for the project in
`readme.old.md`, which describes how a prospective user/developer hoping
to build on top of Sisyphus could build the project and where to look
to start extending it.

