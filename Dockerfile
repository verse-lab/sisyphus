From ocaml/opam:debian-11-ocaml-4.12

COPY --chown=opam ./sisyphus.opam.locked .
COPY --chown=opam ./sisyphus.opam .

# install system deps
RUN sudo apt update && sudo apt install -y libgmp-dev python3

# install files
RUN opam repo add coq-released https://coq.inria.fr/opam/released --all --set-default && \
    opam update && opam upgrade && \
    opam install --deps-only --verbose . -y

# Copy over files
COPY --chown=opam ./bin ./bin
COPY --chown=opam ./lib ./lib
COPY --chown=opam ./tests ./tests
COPY --chown=opam ./scripts ./scripts
COPY --chown=opam ./resources ./resources
COPY --chown=opam ./benchmarks ./benchmarks

COPY --chown=opam ./LICENSE ./LICENSE
COPY --chown=opam ./readme.md ./readme.md
COPY --chown=opam ./dune-project ./dune-project

# let's gooooooo
RUN eval $(opam env) && dune build


