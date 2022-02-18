module Expr = Expr
module Eval = Eval
module Gen = Gen

let do_test_pure p =
  Z3.Solver.push Logic.solver;
  let result = Hardcoded.do_test_pure p in
  Z3.Solver.pop Logic.solver 1;
  result

let do_test p e =
  Z3.Solver.push Logic.solver;
  let result = Hardcoded.do_test p e in
  Z3.Solver.pop Logic.solver 1;
  result
