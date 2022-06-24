# Proof Spec

This library defines a reified encoding of a subset of Coq proof
scripts that can be handled by Sisyphus.

The main interface of this module is the `Script.spec` and
`Script.step` datatype, which describe classes of Coq proofs and proof
steps respectively.
