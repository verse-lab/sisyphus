let vl = let open Lang in
  Proof_term.XLetVal {
    pre = [`Invariant (`App (("I", [`Constructor (("[]", [])); `Int (2)])))];
    binding_ty = (Type.List (Type.Var "A"));
    let_binding = ("x0__", (Type.List (Type.Var "A")));
    eq_binding =
      ("Px0__",
       ("x0__", `Constructor (("::", [`Var ("symbol_10"); `Constructor (("::", [`Var ("symbol_9"); `Constructor (("::", [`Var ("symbol_8"); `Constructor ( ("[]", []))])) ])) ]))));
    value =
      `Constructor (("::", [`Var ("symbol_10"); `Constructor (("::", [`Var ("symbol_9"); `Constructor (("::", [`Var ("symbol_8"); `Constructor (("[]", [])) ])) ])) ]));
    proof =
      Proof_term.XMatch {
        pre = [`Invariant (`App (("I", [`Constructor (("[]", [])); `Int (2)])))];
        proof =
          (Proof_term.HimplHandR (
             [`Invariant (`App (("I", [`Constructor (("[]", [])); `Int (2)])))],
             (Proof_term.Lambda (
                "H", `Eq (((Type.List (Type.Var "A")), `Var ("x0__"), `Constructor (("[]", [])))),
                (Proof_term.HimplTrans (
                   [`Invariant (`App (("I", [`Constructor (("[]", [])); `Int (2)]))) ],
                   [`Invariant (`App (("I", [`Constructor (("[]", [])); `Int (2)]))) ],
                   Proof_term.Refl,
                   (Proof_term.HimplTrans (
                      [`Invariant (`App (("I", [`Constructor (("[]", [])); `Int (2)]))) ],
                      [],
                      (Proof_term.Lambda (
                         "H", `Eq (((Type.List (Type.Var "A")), `Constructor (("[]", [])), `Var ("x0__"))),
                         (Proof_term.Lambda (
                            "C", `Eq (((Type.List (Type.Var "A")), `Constructor (("[]", [])), `Constructor (("::", [`Var ("symbol_10"); `Constructor (("::", [`Var ("symbol_9"); `Constructor ( ("::", [`Var ( "symbol_8"); `Constructor ( ("[]", []))])) ])) ])))),
                            (Proof_term.Lambda (
                               "TEMP", `Eq (((Type.List (Type.Var "A")), `Constructor (("[]", [])), `Constructor (("::", [`Var ("symbol_10"); `Constructor (("::", [`Var ( "symbol_9"); `Constructor ( ("::", [`Var ( "symbol_8"); `Constructor ( ( "[]", [])) ])) ])) ])))),
                               (Proof_term.Lambda (
                                  "_H", `Proof ("Ind(TLC.LibTactics.ltac_Mark,0)"),
                                  Proof_term.XVal {
                                    pre = [`Invariant (`App (("I", [`Constructor (("[]", [])); `Int (2)]))) ];
                                    value_ty = Type.Int; value = `Int (2)
                                  }
                                ))
                             ))
                          ))
                       )),
                      Proof_term.Refl))
                 ))
              )),
             (Proof_term.Lambda (
                "H", `Proof ("(Cst((CFML.WPLifted.Wpgen_negpat))\n (Cst((Coq.Init.Logic.not))\n  (Ind(Coq.Init.Logic.eq,0) (Ind(Coq.Init.Datatypes.list,0) A) #2\n   (Constr(Coq.Init.Datatypes.list,0,1) A))))"),
                (Proof_term.HimplTrans (
                   [`Invariant (`App (("I", [`Constructor (("[]", [])); `Int (2)]))) ],
                   [`Invariant (`App (("I", [`Constructor (("[]", [])); `Int (2)]))) ],
                   Proof_term.Refl,
                   (Proof_term.HimplTrans (
                      [`Invariant (`App (("I", [`Constructor (("[]", [])); `Int (2)]))) ],
                      [],
                      (Proof_term.HimplHandR (
                         [`Invariant (`App (("I", [`Constructor (("[]", [])); `Int (2)]))) ],
                         (Proof_term.Lambda (
                            "a", `Expr (`Var ("A")),
                            (Proof_term.Lambda (
                               "l1", `Ty ((Type.List (Type.Var "A"))),
                               (Proof_term.Lambda (
                                  "H", `Eq (((Type.List (Type.Var "A")), `Var ("x0__"),
                                             `Constructor (("::", [`Var ("a"); `Var ("l1")])))),
                                  (Proof_term.HimplTrans (
                                     [`Invariant (`App (("I", [`Constructor (("[]", [])); `Int (2)]))) ],
                                     [`Invariant (`App (("I", [`Constructor (("[]", [])); `Int (2)]))) ],
                                     Proof_term.Refl,
                                     (Proof_term.HimplTrans (
                                        [`Invariant (`App (("I", [`Constructor ( ("[]", [])); `Int ( 2)]))) ],
                                        [],
                                        (Proof_term.Lambda (
                                           "H", `Eq (((Type.List (Type.Var "A")), `Constructor (("::", [`Var ("a"); `Var ("l1")])), `Var ("x0__"))),
                                           (Proof_term.Lambda (
                                              "C", `Proof ("(Cst((CFML.WPLifted.Wpgen_negpat))\n (Cst((Coq.Init.Logic.not))\n  (Ind(Coq.Init.Logic.eq,0) (Ind(Coq.Init.Datatypes.list,0) A)\n   (Constr(Coq.Init.Datatypes.list,0,2) A symbol_10\n    (Constr(Coq.Init.Datatypes.list,0,2) A symbol_9\n     (Constr(Coq.Init.Datatypes.list,0,2) A symbol_8\n      (Constr(Coq.Init.Datatypes.list,0,1) A))))\n   (Constr(Coq.Init.Datatypes.list,0,1) A))))"),
                                              (Proof_term.Lambda (
                                                 "C0", `Eq (((Type.List (Type.Var "A")), `Constructor (("::", [`Var ( "a"); `Var ( "l1")])), `Constructor (("::", [`Var ( "symbol_10"); `Constructor ( ("::", [`Var ( "symbol_9"); `Constructor ( ( "::", [`Var ( "symbol_8"); `Constructor ( ( "[]", [])) ]))])) ])))),
                                                 (Proof_term.Lambda (
                                                    "TEMP", `Eq (((Type.List (Type.Var "A")), `Constructor (("::", [`Var ( "a"); `Var ( "l1")])), `Constructor (("::", [`Var ( "symbol_10"); `Constructor ( ( "::", [`Var ( "symbol_9"); `Constructor ( ( "::", [`Var ( "symbol_8"); `Constructor ( ( "[]", [])) ]))]))])))),
                                                    (Proof_term.Lambda (
                                                       "_H", `Proof ("Ind(TLC.LibTactics.ltac_Mark,0)"),
                                                       Proof_term.XLetTrmCont {
                                                         pre = [`Invariant (`App ( ("I", [`Constructor ( ("[]", [])); `Int ( 2)]))) ];
                                                         binding_ty = Type.Int;
                                                         value_code = `App (("tmp0", [`Int (2); `Var ("a")]));
                                                         proof =
                                                           Proof_term.XApp {
                                                             pre = [`Invariant (`App ( ("I", [`Constructor ( ( "[]", [])); `Int ( 2)]))) ];
                                                             fun_pre = [`Invariant (`App ( ("I", [`Constructor ( ( "[]", [])); `Int ( 2)]))) ];
                                                             proof_fun = (Proof_term.VarApp ("Hf", [`Expr (`Int (2)); `Expr (`Var ("a")); `Expr (`Constructor ( ("[]", []))); `Expr (`Var ("l1")); `ProofTerm ("`Proof (\"(Cst((Coq.Init.Logic.eq_ind_r)) (Ind(Coq.Init.Datatypes.list,0) A)\\n (Constr(Coq.Init.Datatypes.list,0,2) A symbol_10\\n  (Constr(Coq.Init.Datatypes.list,0,2) A symbol_9\\n   (Constr(Coq.Init.Datatypes.list,0,2) A symbol_8\\n    (Constr(Coq.Init.Datatypes.list,0,1) A))))\\n fun l:(Ind(Coq.Init.Datatypes.list,0) A) =>\\n  (Ind(Coq.Init.Logic.eq,0) (Ind(Coq.Init.Datatypes.list,0) A)\\n   (Cst((TLC.LibList.app)) A (Constr(Coq.Init.Datatypes.list,0,1) A)\\n    (Constr(Coq.Init.Datatypes.list,0,2) A symbol_10\\n     (Constr(Coq.Init.Datatypes.list,0,2) A symbol_9\\n      (Constr(Coq.Init.Datatypes.list,0,2) A symbol_8\\n       (Constr(Coq.Init.Datatypes.list,0,1) A)))))\\n   (Cst((TLC.LibList.app)) A (Constr(Coq.Init.Datatypes.list,0,1) A) #1))\\n (Constr(Coq.Init.Logic.eq,0,1) (Ind(Coq.Init.Datatypes.list,0) A)\\n  (Cst((TLC.LibList.app)) A (Constr(Coq.Init.Datatypes.list,0,1) A)\\n   (Constr(Coq.Init.Datatypes.list,0,2) A symbol_10\\n    (Constr(Coq.Init.Datatypes.list,0,2) A symbol_9\\n     (Constr(Coq.Init.Datatypes.list,0,2) A symbol_8\\n      (Constr(Coq.Init.Datatypes.list,0,1) A))))))\\n (Constr(Coq.Init.Datatypes.list,0,2) A #8 #7) #2)\")") ]));
                                                             proof =
                                                               (Proof_term.HimplTrans (
                                                                  [`Invariant ( `App (("I", [`Constructor ( ("[]", [])); `Int ( 2)]))) ],
                                                                  [`Invariant ( `App (("I", [`Constructor ( ("[]", [])); `Int ( 2)]))) ],
                                                                  Proof_term.Refl,
                                                                  (Proof_term.HimplTrans (
                                                                     [], [],
                                                                     (Proof_term.Lambda (
                                                                        "x", `Ty (Type.Int),
                                                                        (Proof_term.HimplTrans (
                                                                           [`Invariant ( `App ( ("I", [`App ( ( "TLC.LibList.app", [`Constructor ( ( "[]", [])); `Constructor ( ( "::", [`Var ( "a"); `Constructor ( ( "[]", [])) ]))])); `Var ( "x")]))) ],
                                                                           [`Invariant ( `App ( ("I", [`App ( ( "TLC.LibList.app", [`Constructor ( ( "[]", [])); `Constructor ( ( "::", [`Var ( "a"); `Constructor ( ( "[]", [])) ]))])); `Var ( "x")]))) ],
                                                                           Proof_term.Refl,
                                                                           (Proof_term.HimplTrans (
                                                                              [`Invariant ( `App ( ( "I", [`App ( ( "TLC.LibList.app", [`Constructor ( ( "[]", [])); `Constructor ( ( "::", [`Var ( "a"); `Constructor ( ( "[]", [])) ]))])); `Var ( "x")])))],
                                                                              [],
                                                                              Proof_term.XApp {
                                                                                pre =
                                                                                  [`Invariant ( `App ( ( "I", [`App ( ( "TLC.LibList.app", [`Constructor ( ( "[]", [])); `Constructor ( ( "::", [`Var ( "a"); `Constructor ( ( "[]", [])) ]))])); `Var ( "x")])))];
                                                                                fun_pre =
                                                                                  [`Invariant ( `App ( ( "I", [`App ( ( "TLC.LibList.app", [`Constructor ( ( "[]", [])); `Constructor ( ( "::", [`Var ( "a"); `Constructor ( ( "[]", [])) ]))])); `Var ( "x")])))];
                                                                                proof_fun =
                                                                                  Proof_term.AccRect {
                                                                                    prop_type = ( ( "l", ( Type.List (Type.Var "A"))), {
                                                                                      Proof_term.params =
                                                                                        [("t", `Ty ( ( Type.List (Type.Var "A"))));
                                                                                         ("init", `Ty ( Type.Int));
                                                                                         ("_", `Eq ( ( ( Type.List (Type.Var "A")),
                                                                                                       `Constructor ( ( "::", [`Var ( "symbol_10"); `Constructor ( ( "::", [`Var ( "symbol_9"); `Constructor ( ( "::", [`Var ( "symbol_8"); `Constructor ( ( "[]", [])) ]))]))])),
                                                                                                       `App ( ( "TLC.LibList.app", [`Var ( "t"); `Var ( "l")]))))) ];
                                                                                      spec = ( "CFML.Stdlib.List_ml.fold_left", [`Var ( "tmp0"); `Var ( "init"); `Var ( "l")]);
                                                                                      pre = [`Invariant ( `App ( ( "I", [`Var ( "t"); `Var ( "init")]))) ];
                                                                                      post = ( "acc", Type.Int, [ `Invariant ( `App ( ( "I", [`Constructor ( ( "::", [`Var ( "symbol_10"); `Constructor ( ( "::", [`Var ( "symbol_9"); `Constructor ( ( "::", [`Var ( "symbol_8"); `Constructor ( ( "[]", [])) ]))]))])); `Var ( "acc")])))
                                                                                                                ]) });
                                                                                    proof =
                                                                                      { Proof_term.x = "x";
                                                                                        ty_x = ( Type.List (Type.Var "A"));
                                                                                        h_acc = "H";
                                                                                        ty_h_acc = "forall y : list A, list_sub y _UNBOUND_REL_2 -> Acc (list_sub (A:=A)) y";
                                                                                        ih_x = "X0";
                                                                                        ty_ih_x = {
                                                                                          Proof_term.params = [
                                                                                            ("y", `Ty ( ( Type.List (Type.Var "A"))));
                                                                                            ("_", `Proof ( "(Ind(TLC.LibList.list_sub,0) A #1 #3)"));
                                                                                            ("t", `Ty ( ( Type.List (Type.Var "A"))));
                                                                                            ("init", `Ty ( Type.Int));
                                                                                            ("_", `Eq ( ( ( Type.List (Type.Var "A")),
                                                                                                          `Constructor ( ( "::", [`Var ( "symbol_10"); `Constructor ( ( "::", [`Var ( "symbol_9"); `Constructor ( ( "::", [`Var ( "symbol_8"); `Constructor ( ( "[]", [])) ]))]))])),
                                                                                                          `App ( ( "TLC.LibList.app", [`Var ( "t"); `Var ( "y")]))))) ];
                                                                                          spec = ( "CFML.Stdlib.List_ml.fold_left", [`Var ( "tmp0"); `Var ( "init"); `Var ( "y")]);
                                                                                          pre = [`Invariant ( `App ( ( "I", [`Var ( "t"); `Var ( "init")]))) ];
                                                                                          post = ( "acc", Type.Int, [`Invariant ( `App ( ( "I", [`Constructor ( ( "::", [`Var ( "symbol_10"); `Constructor ( ( "::", [`Var ( "symbol_9"); `Constructor ( ( "::", [`Var ( "symbol_8"); `Constructor ( ( "[]", [])) ]))]))])); `Var ( "acc")]))) ])
                                                                                        };
                                                                                        proof = ( Proof_term.Lambda (
                                                                                          "t", `Ty ( ( Type.List (Type.Var "A"))),
                                                                                          (Proof_term.Lambda (
                                                                                             "init", `Ty ( Type.Int),
                                                                                             (Proof_term.Lambda (
                                                                                                "Ht", `Eq ( ( ( Type.List (Type.Var "A")),
                                                                                                              `Constructor ( ( "::", [`Var ( "symbol_10"); `Constructor ( ( "::", [`Var ( "symbol_9"); `Constructor ( ( "::", [`Var ( "symbol_8"); `Constructor ( ( "[]", [])) ]))]))])),
                                                                                                              `App ( ( "TLC.LibList.app", [`Var ( "t"); `Var ( "x")])))),
                                                                                                Proof_term.CharacteristicFormulae {
                                                                                                  args = [`Expr ( `Var ( "A")); `Expr ( `Var ( "EA")); `Ty ( Type.Int); `Proof ( "Cst((CFML.SepLifted.Enc_int))"); `Expr ( `Var ( "tmp0")); `Expr ( `Var ( "init")); `Expr ( `Var ( "x"))];
                                                                                                  pre = [`Invariant ( `App ( ( "I", [`Var ( "t"); `Var ( "init")]))) ];
                                                                                                  proof =
                                                                                                    Proof_term.XLetVal {
                                                                                                      pre = [`Invariant ( `App ( ( "I", [`Var ( "t"); `Var ( "init")]))) ];
                                                                                                      binding_ty = ( Type.List (Type.Var "A"));
                                                                                                      let_binding =
                                                                                                        ( "x0__", ( Type.List (Type.Var "A")));
                                                                                                      eq_binding =
                                                                                                        ( "Px0__", ( "x0__", `Var ( "x")));
                                                                                                      value = `Var ( "x");
                                                                                                      proof =
                                                                                                        Proof_term.XMatch {
                                                                                                          pre = [`Invariant ( `App ( ( "I", [`Var ( "t"); `Var ( "init")]))) ];
                                                                                                          proof =
                                                                                                            ( Proof_term.HimplHandR (
                                                                                                                [`Invariant ( `App ( ( "I", [`Var ( "t"); `Var ( "init")]))) ],
                                                                                                                (Proof_term.Lambda (
                                                                                                                   "H", `Eq ( ( ( Type.List (Type.Var "A")), `Var ( "x0__"), `Constructor ( ( "[]", [])))),
                                                                                                                   (Proof_term.HimplTrans (
                                                                                                                      [`Invariant ( `App ( ( "I", [`Var ( "t"); `Var ( "init")]))) ],
                                                                                                                      [`Invariant ( `App ( ( "I", [`Var ( "t"); `Var ( "init")]))) ],
                                                                                                                      Proof_term.Refl,
                                                                                                                      (Proof_term.HimplTrans (
                                                                                                                         [`Invariant ( `App ( ( "I", [`Var ( "t"); `Var ( "init")]))) ],
                                                                                                                         [],
                                                                                                                         (Proof_term.Lambda (
                                                                                                                            "H", `Eq ( ( ( Type.List (Type.Var "A")), `Constructor ( ( "[]", [])), `Var ( "x0__"))),
                                                                                                                            (Proof_term.Lambda (
                                                                                                                               "C", `Eq ( ( ( Type.List (Type.Var "A")), `Constructor ( ( "[]", [])), `Var ( "x"))),
                                                                                                                               (Proof_term.Lambda (
                                                                                                                                  "TEMP", `Eq ( ( ( Type.List (Type.Var "A")), `Constructor ( ( "[]", [])), `Var ( "x"))),
                                                                                                                                  (Proof_term.Lambda (
                                                                                                                                     "_H", `Proof ( "Ind(TLC.LibTactics.ltac_Mark,0)"),
                                                                                                                                     Proof_term.XVal {
                                                                                                                                       pre =
                                                                                                                                         [`Invariant ( `App ( ( "I", [`Var ( "t"); `Var ( "init")]))) ];
                                                                                                                                       value_ty =
                                                                                                                                         Type.Int;
                                                                                                                                       value =
                                                                                                                                         `Var ( "init")}
                                                                                                                                   )))))))),
                                                                                                                         Proof_term.Refl
                                                                                                                       )))))),
                                                                                                                (Proof_term.Lambda (
                                                                                                                   "H", `Proof ( "(Cst((CFML.WPLifted.Wpgen_negpat))\n (Cst((Coq.Init.Logic.not))\n  (Ind(Coq.Init.Logic.eq,0) (Ind(Coq.Init.Datatypes.list,0) A) #2\n   (Constr(Coq.Init.Datatypes.list,0,1) A))))"),
                                                                                                                   (Proof_term.HimplTrans (
                                                                                                                      [`Invariant ( `App ( ( "I", [`Var ( "t"); `Var ( "init")]))) ],
                                                                                                                      [`Invariant ( `App ( ( "I", [`Var ( "t"); `Var ( "init")]))) ],
                                                                                                                      Proof_term.Refl,
                                                                                                                      (Proof_term.HimplTrans (
                                                                                                                         [`Invariant ( `App ( ( "I", [`Var ( "t"); `Var ( "init")]))) ], [],
                                                                                                                         (Proof_term.HimplHandR (
                                                                                                                            [`Invariant ( `App ( ( "I", [`Var ( "t"); `Var ( "init")]))) ],
                                                                                                                            (Proof_term.Lambda (
                                                                                                                               "a", `Expr ( `Var ( "A")),
                                                                                                                               (Proof_term.Lambda (
                                                                                                                                  "l1", `Ty ( ( Type.List (Type.Var "A"))),
                                                                                                                                  (Proof_term.Lambda (
                                                                                                                                     "H", `Eq ( ( ( Type.List (Type.Var "A")), `Var ( "x0__"), `Constructor ( ( "::", [`Var ( "a"); `Var ( "l1")])))),
                                                                                                                                     (Proof_term.HimplTrans (
                                                                                                                                        [`Invariant ( `App ( ( "I", [`Var ( "t"); `Var ( "init")]))) ],
                                                                                                                                        [`Invariant ( `App ( ( "I", [`Var ( "t"); `Var ( "init")]))) ],
                                                                                                                                        Proof_term.Refl,
                                                                                                                                        (Proof_term.HimplTrans (
                                                                                                                                           [`Invariant ( `App ( ( "I", [`Var ( "t"); `Var ( "init")]))) ], [],
                                                                                                                                           (Proof_term.Lambda (
                                                                                                                                              "H", `Eq ( ( ( Type.List (Type.Var "A")), `Constructor ( ( "::", [`Var ( "a"); `Var ( "l1")])), `Var ( "x0__"))),
                                                                                                                                              (Proof_term.Lambda (
                                                                                                                                                 "C", `Proof ( "(Cst((CFML.WPLifted.Wpgen_negpat))\n (Cst((Coq.Init.Logic.not))\n  (Ind(Coq.Init.Logic.eq,0) (Ind(Coq.Init.Datatypes.list,0) A) #13\n   (Constr(Coq.Init.Datatypes.list,0,1) A))))"),
                                                                                                                                                 (Proof_term.Lambda (
                                                                                                                                                    "C0", `Eq ( ( ( Type.List (Type.Var "A")), `Constructor ( ( "::", [`Var ( "a"); `Var ( "l1")])), `Var ( "x"))),
                                                                                                                                                    (Proof_term.Lambda (
                                                                                                                                                       "TEMP", `Eq ( ( ( Type.List (Type.Var "A")), `Constructor ( ( "::", [`Var ( "a"); `Var ( "l1")])), `Var ( "x"))),
                                                                                                                                                       (Proof_term.Lambda (
                                                                                                                                                          "_H", `Proof ( "Ind(TLC.LibTactics.ltac_Mark,0)"),
                                                                                                                                                          Proof_term.XLetTrmCont {
                                                                                                                                                            pre = [`Invariant ( `App ( ( "I", [`Var ( "t"); `Var ( "init")]))) ];
                                                                                                                                                            binding_ty = Type.Int;
                                                                                                                                                            value_code = `App ( ( "tmp0", [`Var ( "init"); `Var ( "a")]));
                                                                                                                                                            proof = Proof_term.XApp {
                                                                                                                                                              pre = [`Invariant ( `App ( ( "I", [`Var ( "t"); `Var ( "init")]))) ];
                                                                                                                                                              fun_pre = [`Invariant ( `App ( ( "I", [`Var ( "t"); `Var ( "init")]))) ];
                                                                                                                                                              proof_fun = ( Proof_term.VarApp ("Hf", [`Expr ( `Var ( "init")); `Expr ( `Var ( "a")); `Expr ( `Var ( "t")); `Expr ( `Var ( "l1")); `ProofTerm ( "`Proof (\"(Cst((Coq.Init.Logic.eq_ind_r)) (Ind(Coq.Init.Datatypes.list,0) A)\\n (Cst((TLC.LibList.app)) A #14 #17)\\n fun l:(Ind(Coq.Init.Datatypes.list,0) A) =>\\n  (Ind(Coq.Init.Logic.eq,0) (Ind(Coq.Init.Datatypes.list,0) A) #1\\n   (Cst((TLC.LibList.app)) A #15\\n    (Constr(Coq.Init.Datatypes.list,0,2) A #9 #8)))\\n (Cst((Coq.Init.Logic.eq_ind_r)) (Ind(Coq.Init.Datatypes.list,0) A) #17\\n  fun l:(Ind(Coq.Init.Datatypes.list,0) A) =>\\n   (Ind(Coq.Init.Logic.eq,0) (Ind(Coq.Init.Datatypes.list,0) A)\\n    (Cst((TLC.LibList.app)) A #15 #18) (Cst((TLC.LibList.app)) A #15 #1))\\n  (Constr(Coq.Init.Logic.eq,0,1) (Ind(Coq.Init.Datatypes.list,0) A)\\n   (Cst((TLC.LibList.app)) A #14 #17))\\n  (Constr(Coq.Init.Datatypes.list,0,2) A #8 #7) #2)\\n (Constr(Coq.Init.Datatypes.list,0,2) A symbol_10\\n  (Constr(Coq.Init.Datatypes.list,0,2) A symbol_9\\n   (Constr(Coq.Init.Datatypes.list,0,2) A symbol_8\\n    (Constr(Coq.Init.Datatypes.list,0,1) A)))) #12)\")") ]));
                                                                                                                                                              proof =
                                                                                                                                                                ( Proof_term.HimplTrans (
                                                                                                                                                                    [`Invariant ( `App ( ( "I", [`Var ( "t"); `Var ( "init")]))) ],
                                                                                                                                                                    [`Invariant ( `App ( ( "I", [`Var ( "t"); `Var ( "init")]))) ],
                                                                                                                                                                    Proof_term.Refl,
                                                                                                                                                                    (Proof_term.HimplTrans (
                                                                                                                                                                       [], [],
                                                                                                                                                                       (Proof_term.Lambda (
                                                                                                                                                                          "x", `Ty ( Type.Int),
                                                                                                                                                                          (Proof_term.HimplTrans (
                                                                                                                                                                             [`Invariant ( `App ( ( "I", [`App ( ( "TLC.LibList.app", [`Var ( "t"); `Constructor ( ( "::", [`Var ( "a"); `Constructor ( ( "[]", [])) ]))])); `Var ( "x")])))],
                                                                                                                                                                             [`Invariant ( `App ( ( "I", [`App ( ( "TLC.LibList.app", [`Var ( "t"); `Constructor ( ( "::", [`Var ( "a"); `Constructor ( ( "[]", [])) ]))])); `Var ( "x")])))],
                                                                                                                                                                             Proof_term.Refl,
                                                                                                                                                                             (Proof_term.HimplTrans (
                                                                                                                                                                                [`Invariant ( `App ( ( "I", [`App ( ( "TLC.LibList.app", [`Var ( "t"); `Constructor ( ( "::", [`Var ( "a"); `Constructor ( ( "[]", [])) ]))])); `Var ( "x")])))],
                                                                                                                                                                                [],
                                                                                                                                                                                Proof_term.XApp {
                                                                                                                                                                                  pre =
                                                                                                                                                                                    [`Invariant ( `App ( ( "I", [`App ( ( "TLC.LibList.app", [`Var ( "t"); `Constructor ( ( "::", [`Var ( "a"); `Constructor ( ( "[]", [])) ]))])); `Var ( "x")])))];
                                                                                                                                                                                  fun_pre =
                                                                                                                                                                                    [`Invariant ( `App ( ( "I", [`App ( ( "TLC.LibList.app", [`Var ( "t"); `Constructor ( ( "::", [`Var ( "a"); `Constructor ( ( "[]", [])) ]))])); `Var ( "x")])))];
                                                                                                                                                                                  proof_fun =
                                                                                                                                                                                    ( Proof_term.VarApp ("X0", [
                                                                                                                                                                                        `Expr ( `Var ( "l1"));
                                                                                                                                                                                        `ProofTerm ( "`Proof (\"(Cst((Coq.Init.Logic.eq_ind)) (Ind(Coq.Init.Datatypes.list,0) A)\\n (Constr(Coq.Init.Datatypes.list,0,2) A #9 #8)\\n fun r:(Ind(Coq.Init.Datatypes.list,0) A) =>\\n  (Ind(TLC.LibList.list_sub,0) A #9 #1)\\n (Constr(TLC.LibList.list_sub,0,1) A #9 #8) #18 #3)\")");
                                                                                                                                                                                        `Expr ( `App ( ( "TLC.LibList.app", [`Var ( "t"); `Constructor ( ( "::", [`Var ( "a"); `Constructor ( ( "[]", [])) ]))]))); 
                                                                                                                                                                                        `Expr ( `Var ( "x"));
                                                                                                                                                                                        `ProofTerm ( "`Proof (\"(Cst((Coq.Init.Logic.eq_ind_r)) (Ind(Coq.Init.Datatypes.list,0) A)\\n (Cst((TLC.LibList.app)) A #15\\n  (Cst((TLC.LibList.app)) A\\n   (Constr(Coq.Init.Datatypes.list,0,2) A #9\\n    (Constr(Coq.Init.Datatypes.list,0,1) A)) #8))\\n fun l:(Ind(Coq.Init.Datatypes.list,0) A) =>\\n  (Ind(Coq.Init.Logic.eq,0) (Ind(Coq.Init.Datatypes.list,0) A)\\n   (Constr(Coq.Init.Datatypes.list,0,2) A symbol_10\\n    (Constr(Coq.Init.Datatypes.list,0,2) A symbol_9\\n     (Constr(Coq.Init.Datatypes.list,0,2) A symbol_8\\n      (Constr(Coq.Init.Datatypes.list,0,1) A)))) #1)\\n (Cst((Coq.Init.Logic.eq_ind_r)) (Ind(Coq.Init.Datatypes.list,0) A) #18\\n  fun l:(Ind(Coq.Init.Datatypes.list,0) A) =>\\n   (Ind(Coq.Init.Logic.eq,0) (Ind(Coq.Init.Datatypes.list,0) A)\\n    (Constr(Coq.Init.Datatypes.list,0,2) A symbol_10\\n     (Constr(Coq.Init.Datatypes.list,0,2) A symbol_9\\n      (Constr(Coq.Init.Datatypes.list,0,2) A symbol_8\\n       (Constr(Coq.Init.Datatypes.list,0,1) A))))\\n    (Cst((TLC.LibList.app)) A #16 #1)) #13\\n  (Constr(Coq.Init.Datatypes.list,0,2) A #9 #8) #3)\\n (Cst((TLC.LibList.app)) A\\n  (Cst((TLC.LibList.app)) A #15\\n   (Constr(Coq.Init.Datatypes.list,0,2) A #9\\n    (Constr(Coq.Init.Datatypes.list,0,1) A))) #8)\\n (Cst((TLC.LibList.app_assoc)) A #15\\n  (Constr(Coq.Init.Datatypes.list,0,2) A #9\\n   (Constr(Coq.Init.Datatypes.list,0,1) A)) #8))\")") ]));
                                                                                                                                                                                  proof = (
                                                                                                                                                                                    Proof_term.HimplTrans (
                                                                                                                                                                                      [`Invariant ( `App ( ( "I", [`App ( ( "TLC.LibList.app", [`Var ( "t"); `Constructor ( ( "::", [`Var ( "a"); `Constructor ( ( "[]", [])) ]))])); `Var ( "x")])))],
                                                                                                                                                                                      [`Invariant ( `App ( ( "I", [`App ( ( "TLC.LibList.app", [`Var ( "t"); `Constructor ( ( "::", [`Var ( "a"); `Constructor ( ( "[]", [])) ]))])); `Var ( "x")])))],
                                                                                                                                                                                      Proof_term.Refl,
                                                                                                                                                                                      (Proof_term.HimplTrans (
                                                                                                                                                                                         [], 
                                                                                                                                                                                         [],
                                                                                                                                                                                         (Proof_term.Lambda (
                                                                                                                                                                                            "x", `Ty ( Type.Int),
                                                                                                                                                                                            (Proof_term.HimplTrans (
                                                                                                                                                                                               [`Invariant ( `App ( ( "I", [`Constructor ( ( "::", [`Var ( "symbol_10"); `Constructor ( ( "::", [`Var ( "symbol_9"); `Constructor ( ( "::", [`Var ( "symbol_8"); `Constructor ( ( "[]", [])) ]))]))])); `Var ( "x")])))],
                                                                                                                                                                                               [`Invariant ( `App ( ( "I", [`Constructor ( ( "::", [`Var ( "symbol_10"); `Constructor ( ( "::", [`Var ( "symbol_9"); `Constructor ( ( "::", [`Var ( "symbol_8"); `Constructor ( ( "[]", [])) ]))]))])); `Var ( "x")])))],
                                                                                                                                                                                               Proof_term.Refl,
                                                                                                                                                                                               (Proof_term.HimplTrans (
                                                                                                                                                                                                  [`Invariant ( `App ( ( "I", [`Constructor ( ( "::", [`Var ( "symbol_10"); `Constructor ( ( "::", [`Var ( "symbol_9"); `Constructor ( ( "::", [`Var ( "symbol_8"); `Constructor ( ( "[]", [])) ]))]))])); `Var ( "x")])))],
                                                                                                                                                                                                  [],
                                                                                                                                                                                                  (Proof_term.HimplTrans (
                                                                                                                                                                                                     [`Invariant ( `App ( ( "I", [`Constructor ( ( "::", [`Var ( "symbol_10"); `Constructor ( ( "::", [`Var ( "symbol_9"); `Constructor ( ( "::", [`Var ( "symbol_8"); `Constructor ( ( "[]", [])) ]))]))])); `Var ( "x")])))],
                                                                                                                                                                                                     [`Invariant ( `App ( ( "I", [`Constructor ( ( "::", [`Var ( "symbol_10"); `Constructor ( ( "::", [`Var ( "symbol_9"); `Constructor ( ( "::", [`Var ( "symbol_8"); `Constructor ( ( "[]", [])) ]))]))])); `Var ( "x")])))],
                                                                                                                                                                                                     Proof_term.Refl,
                                                                                                                                                                                                     (Proof_term.HimplTrans (
                                                                                                                                                                                                        [], 
                                                                                                                                                                                                        [],
                                                                                                                                                                                                        Proof_term.Refl,
                                                                                                                                                                                                        Proof_term.Refl
                                                                                                                                                                                                      )))),
                                                                                                                                                                                                  Proof_term.Refl
                                                                                                                                                                                                )))))),
                                                                                                                                                                                         Proof_term.Refl
                                                                                                                                                                                       ))))},
                                                                                                                                                                                Proof_term.Refl
                                                                                                                                                                              )))))),
                                                                                                                                                                       Proof_term.Refl
                                                                                                                                                                     ))))}}))
                                                                                                                                                     )))))))),
                                                                                                                                           Proof_term.Refl
                                                                                                                                         ))))))))
                                                                                                                             )),
                                                                                                                            (Proof_term.Lambda (
                                                                                                                               "H", `Proof ( "(Cst((CFML.WPLifted.Wpgen_negpat))\n forall a:A,\n  forall l:(Ind(Coq.Init.Datatypes.list,0) A),\n   (Cst((Coq.Init.Logic.not))\n    (Ind(Coq.Init.Logic.eq,0) (Ind(Coq.Init.Datatypes.list,0) A) #5\n     (Constr(Coq.Init.Datatypes.list,0,2) A #2 #1))))"),
                                                                                                                               (Proof_term.HimplTrans (
                                                                                                                                  [`Invariant ( `App ( ( "I", [`Var ( "t"); `Var ( "init")]))) ],
                                                                                                                                  [`Invariant ( `App ( ( "I", [`Var ( "t"); `Var ( "init")]))) ],
                                                                                                                                  Proof_term.Refl,
                                                                                                                                  (Proof_term.HimplTrans (
                                                                                                                                     [`Invariant ( `App ( ( "I", [`Var ( "t"); `Var ( "init")]))) ], [],
                                                                                                                                     (Proof_term.XDone
                                                                                                                                        [`Invariant ( `App ( ( "I", [`Var ( "t"); `Var ( "init")]))) ]),
                                                                                                                                     Proof_term.Refl
                                                                                                                                   )))))))),
                                                                                                                         Proof_term.Refl
                                                                                                                       ))))))))}}}
                                                                                              )))))) };
                                                                                    vl =
                                                                                      `Var (
                                                                                        "l1");
                                                                                    args =
                                                                                      [`Expr ( `App ( ( "TLC.LibList.app", [`Constructor ( ( "[]", [])); `Constructor ( ( "::", [`Var ( "a"); `Constructor ( ( "[]", [])) ]))])));
                                                                                       `Expr ( `Var ( "x"));
                                                                                       `ProofTerm ( "`Proof (\"(Cst((Coq.Init.Logic.eq_ind_r)) (Ind(Coq.Init.Datatypes.list,0) A)\\n (Constr(Coq.Init.Datatypes.list,0,2) A symbol_10\\n  (Constr(Coq.Init.Datatypes.list,0,2) A symbol_9\\n   (Constr(Coq.Init.Datatypes.list,0,2) A symbol_8\\n    (Constr(Coq.Init.Datatypes.list,0,1) A))))\\n fun l:(Ind(Coq.Init.Datatypes.list,0) A) =>\\n  (Ind(Coq.Init.Logic.eq,0) (Ind(Coq.Init.Datatypes.list,0) A)\\n   (Constr(Coq.Init.Datatypes.list,0,2) A symbol_10\\n    (Constr(Coq.Init.Datatypes.list,0,2) A symbol_9\\n     (Constr(Coq.Init.Datatypes.list,0,2) A symbol_8\\n      (Constr(Coq.Init.Datatypes.list,0,1) A))))\\n   (Cst((TLC.LibList.app)) A (Constr(Coq.Init.Datatypes.list,0,1) A) #1))\\n (Constr(Coq.Init.Logic.eq,0,1) (Ind(Coq.Init.Datatypes.list,0) A)\\n  (Cst((TLC.LibList.app)) A (Constr(Coq.Init.Datatypes.list,0,1) A)\\n   (Constr(Coq.Init.Datatypes.list,0,2) A symbol_10\\n    (Constr(Coq.Init.Datatypes.list,0,2) A symbol_9\\n     (Constr(Coq.Init.Datatypes.list,0,2) A symbol_8\\n      (Constr(Coq.Init.Datatypes.list,0,1) A))))))\\n (Constr(Coq.Init.Datatypes.list,0,2) A #9 #8) #3)\")")
                                                                                      ]};
                                                                                proof =
                                                                                  (
                                                                                    Proof_term.HimplTrans (
                                                                                      [`Invariant ( `App ( ( "I", [`App ( ( "TLC.LibList.app", [`Constructor ( ( "[]", [])); `Constructor ( ( "::", [`Var ( "a"); `Constructor ( ( "[]", [])) ]))])); `Var ( "x")])))],
                                                                                      [`Invariant ( `App ( ( "I", [`App ( ( "TLC.LibList.app", [`Constructor ( ( "[]", [])); `Constructor ( ( "::", [`Var ( "a"); `Constructor ( ( "[]", [])) ]))])); `Var ( "x")])))],
                                                                                      Proof_term.Refl,
                                                                                      (Proof_term.HimplTrans (
                                                                                         [], 
                                                                                         [],
                                                                                         (Proof_term.Lambda (
                                                                                            "x", `Ty ( Type.Int),
                                                                                            (Proof_term.HimplTrans (
                                                                                               [`Invariant ( `App ( ( "I", [`Constructor ( ( "::", [`Var ( "symbol_10"); `Constructor ( ( "::", [`Var ( "symbol_9"); `Constructor ( ( "::", [`Var ( "symbol_8"); `Constructor ( ( "[]", [])) ]))]))])); `Var ( "x")])))],
                                                                                               [`Invariant ( `App ( ( "I", [`Constructor ( ( "::", [`Var ( "symbol_10"); `Constructor ( ( "::", [`Var ( "symbol_9"); `Constructor ( ( "::", [`Var ( "symbol_8"); `Constructor ( ( "[]", [])) ]))]))])); `Var ( "x")])))],
                                                                                               Proof_term.Refl,
                                                                                               (Proof_term.HimplTrans (
                                                                                                  [`Invariant ( `App ( ( "I", [`Constructor ( ( "::", [`Var ( "symbol_10"); `Constructor ( ( "::", [`Var ( "symbol_9"); `Constructor ( ( "::", [`Var ( "symbol_8"); `Constructor ( ( "[]", [])) ]))]))])); `Var ( "x")])))],
                                                                                                  [],
                                                                                                  (Proof_term.HimplTrans (
                                                                                                     [`Invariant ( `App ( ( "I", [`Constructor ( ( "::", [`Var ( "symbol_10"); `Constructor ( ( "::", [`Var ( "symbol_9"); `Constructor ( ( "::", [`Var ( "symbol_8"); `Constructor ( ( "[]", [])) ]))]))])); `Var ( "x")])))],
                                                                                                     [`Invariant ( `App ( ( "I", [`Constructor ( ( "::", [`Var ( "symbol_10"); `Constructor ( ( "::", [`Var ( "symbol_9"); `Constructor ( ( "::", [`Var ( "symbol_8"); `Constructor ( ( "[]", [])) ]))]))])); `Var ( "x")])))],
                                                                                                     Proof_term.Refl,
                                                                                                     (Proof_term.HimplTrans (
                                                                                                        [], 
                                                                                                        [],
                                                                                                        Proof_term.Refl,
                                                                                                        Proof_term.Refl
                                                                                                      )))),
                                                                                                  Proof_term.Refl
                                                                                                )))))),
                                                                                         Proof_term.Refl
                                                                                       ))))},
                                                                              Proof_term.Refl
                                                                            ))
                                                                         ))
                                                                      )),
                                                                     Proof_term.Refl))
                                                                ))}}
                                                     ))
                                                  ))
                                               ))
                                            ))
                                         )),
                                        Proof_term.Refl))
                                   ))
                                ))
                             ))
                          )),
                         (Proof_term.Lambda (
                            "H", `Proof ("(Cst((CFML.WPLifted.Wpgen_negpat))\n forall a:A,\n  forall l:(Ind(Coq.Init.Datatypes.list,0) A),\n   (Cst((Coq.Init.Logic.not))\n    (Ind(Coq.Init.Logic.eq,0) (Ind(Coq.Init.Datatypes.list,0) A) #5\n     (Constr(Coq.Init.Datatypes.list,0,2) A #2 #1))))"),
                            (Proof_term.HimplTrans (
                               [`Invariant (`App (("I", [`Constructor (("[]", [])); `Int (2)]))) ],
                               [`Invariant (`App (("I", [`Constructor (("[]", [])); `Int (2)]))) ],
                               Proof_term.Refl,
                               (Proof_term.HimplTrans (
                                  [`Invariant (`App (("I", [`Constructor (("[]", [])); `Int (2)]))) ],
                                  [],
                                  (Proof_term.XDone
                                     [`Invariant (`App (("I", [`Constructor (("[]", [])); `Int (2)]))) ]),
                                  Proof_term.Refl))
                             ))
                          ))
                       )),
                      Proof_term.Refl))
                 ))
              ))
           ))}}
