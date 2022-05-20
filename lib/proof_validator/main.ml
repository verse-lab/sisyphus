
let data = Proof_validator.Verification_condition.{
  poly_vars = ["A"];
  env =
    [("l", List (Var "A")); ("s", Func); ("v", Loc); ("tmp", Val);
     ("len", Var "Coq.Numbers.BinNums.Z"); ("ls", List (Var "A")); ("init", Var "A");
     ("rest", List (Var "A")); ("a", Array (Var "A")); ("data", List (Var "A"));
     ("idx", Var "Coq.Numbers.BinNums.Z"); ("tmp0", Val)];
  assumptions =
    [(List (Var "A"), `Var "ls", `Constructor ("::", [`Var "init"; `Var "rest"]));
     (Product [Int; List (Var "A")],
      `Tuple [`Var "len"; `Constructor ("::", [`Var "init"; `Var "rest"])],
      `Tuple [`App ("TLC.LibListZ.length", [`Var "l"]); `App ("TLC.LibList.rev", [`Var "l"])]);
     (List (Var "A"), `Constructor ("::", [`Var "init"; `Var "rest"]), `App ("TLC.LibList.rev", [`Var "l"]));
     (Int, `Var "len", `App ("TLC.LibListZ.length", [`Var "l"]));
     (List (Var "A"), `Var "data", `App ("TLC.LibListZ.make", [`Var "len"; `Var "init"]));
     (Int, `Var "idx", `App ("-", [`Var "len"; `Int 2]))];
  initial = { expr_values = [|`Var "data"|]; param_values = [`Constructor ("[]", []); `Var "idx"] };
  conditions =
    [{ qf =
         [("r", List (Var "A")); ("t", List (Var "A")); ("v", Var "A"); ("acc", Int)];
       param_values = [`Var "t"; `Var "acc"];
       assumptions = [`Eq ((List (Var "A"),
                            `Var "rest",
                            `App ("TLC.LibList.app", [`Var "t"; `Constructor ("::", [`Var "v"; `Var "r"])])))];
       post_param_values = [
         `App ("TLC.LibList.app",
               [`Var "t"; `Constructor ("::", [`Var "v"; `Constructor ("[]", [])])]);
         `App ("-", [`Var "acc"; `Int 1])
       ];
       expr_values = [|fun exp -> `App ("Array.set", [(`App ("CFML.WPArray.Array", [exp])); `Var "acc"; `Var "v"])|] }
    ]
} 
