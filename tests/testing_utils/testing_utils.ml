open Containers

let tests = ref []

let run name =
  Alcotest.run name
    (List.map (fun f -> f ()) @@ List.rev !tests)

type stmt = [
  | `LetExp of Lang.Expr.typed_param * string option * Lang.Expr.t * stmt
  | `LetLambda of string * [ `Lambda of Lang.Expr.typed_param list * stmt ] * stmt
  | `Match of Lang.Expr.t * (string * (string * Lang.Type.t) list * stmt) list
  | `Write of string * string * Lang.Expr.t * stmt
  | `Value of Lang.Expr.t
  | `EmptyArray
] [@@deriving show]

let pp_program fmt (prog: 'a Lang.Program.t) =
  Format.fprintf fmt "@[<2>{ ";
  begin
    Format.fprintf fmt "@[%s =@ " "name";
    Format.fprintf fmt "%S" prog.name;
    Format.fprintf fmt "@];@ "
  end;
  begin
    Ppx_deriving_runtime.Format.fprintf fmt "@[%s =@ [" "args";
    List.pp ~pp_sep:(fun fmt () -> Format.fprintf fmt ";@ ") (fun fmt (a0, a1) ->
      Format.fprintf fmt "(@[";
      ((Format.fprintf fmt "%S") a0;  Format.fprintf fmt
         ",@ ";
       (Lang.Type.pp fmt) a1);
      Format.fprintf fmt "@])"
    ) fmt prog.args;
    Format.fprintf fmt "]@];@ ";
    Ppx_deriving_runtime.Format.fprintf fmt "@[%s =@ " "body";
    pp_stmt fmt prog.body;
    Format.fprintf fmt "@]"
  end;
  Format.fprintf fmt  "@ }@]"
[@@warning "-32"]

let program : Lang.Expr.t Lang.Program.t Alcotest.testable =
  Alcotest.testable (pp_program)
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
