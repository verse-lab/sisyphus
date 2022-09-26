open Containers

let tests = ref []

let run name =
  Alcotest.run name
    (List.map (fun f -> f ()) @@ List.rev !tests)


let program : Lang.Expr.t Lang.Program.t Alcotest.testable =
  Alcotest.testable (Lang.Program.ppr Lang.Expr.pp_raw)
    (Lang.Program.equal Lang.Expr.equal)


module Make (S: sig val name: string end) = struct

  let module_tests = ref [];;

  tests := (fun () -> S.name, List.rev !module_tests) :: !tests

  let add_test name test =
    module_tests := (name, `Quick, test) :: !module_tests

  let add_slow_test name test =
    module_tests := (name, `Slow, test) :: !module_tests

  let run () = run S.name

end
