# Lang

This library defines a reified encoding of a subset of OCaml programs
that can be handled by Sisyphus.

The main interface of this module is the `Program.t` and `Expr.t`
datatype, which describe a subset of OCaml programs and expressions
respectively.

The library also provides a facility to extract these reified
representations from Raw OCaml compiler-libs program ASTs using the
`Sanitizer` module (`Sanitizer.convert` in particular).
