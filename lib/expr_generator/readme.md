# Expression Generator
This library encapsulates a type-directed enumerative search procedure
for generating candidate Coq expressions for program invariants.

```ocaml
let max_fuel = 3 in
let fuel = max_fuel in
let exps = 
    Expr_generator.Expgen.gen_exp
        ctx env ~max_fuel ~fuel (List (Var "A"))
```
