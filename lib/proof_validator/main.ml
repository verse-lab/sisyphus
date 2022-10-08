open Containers

let data =
  Proof_validator.VerificationCondition.{
    poly_vars = ["A"];
    functions =
      [("Coq.ZArith.BinInt.Z.max",
        Lang.Type.Forall ([], [Lang.Type.Int; Lang.Type.Int; Lang.Type.Int]));
       ("Coq.ZArith.BinInt.Z.min",
        Lang.Type.Forall ([], [Lang.Type.Int; Lang.Type.Int; Lang.Type.Int]));
       ("TLC.LibList.app",
        Lang.Type.Forall (["A"], [Lang.Type.List (Lang.Type.Var "A"); Lang.Type.List (Lang.Type.Var "A"); Lang.Type.List (Lang.Type.Var "A")]));
       ("TLC.LibList.combine",
        Lang.Type.Forall (["A"; "B"], [Lang.Type.List (Lang.Type.Var "B"); Lang.Type.List (Lang.Type.Var "A"); Lang.Type.List (Lang.Type.Product ([Lang.Type.Var "B"; Lang.Type.Var "A"]))]));
       ("TLC.LibList.concat",
        Lang.Type.Forall (["A"], [Lang.Type.List (Lang.Type.List (Lang.Type.Var "A")); Lang.Type.List (Lang.Type.Var "A")]));
       ("TLC.LibList.drop",
        Lang.Type.Forall (["A"], [Lang.Type.Int; Lang.Type.List (Lang.Type.Var "A"); Lang.Type.List (Lang.Type.Var "A")]));
       ("TLC.LibList.length",
        Lang.Type.Forall (["A"], [Lang.Type.List (Lang.Type.Var "A"); Lang.Type.Int]));
       ("TLC.LibList.remove",
        Lang.Type.Forall (["A"], [Lang.Type.Var "A"; Lang.Type.List (Lang.Type.Var "A"); Lang.Type.List (Lang.Type.Var "A")]));
       ("TLC.LibList.rev",
        Lang.Type.Forall (["A"], [Lang.Type.List (Lang.Type.Var "A"); Lang.Type.List (Lang.Type.Var "A")]));
       ("TLC.LibList.split",
        Lang.Type.Forall (["A"; "B"], [Lang.Type.List (Lang.Type.Product ([Lang.Type.Var "B"; Lang.Type.Var "A"])); Lang.Type.Product ([Lang.Type.List (Lang.Type.Var "B"); Lang.Type.List (Lang.Type.Var "A")])]));
       ("TLC.LibList.take",
        Lang.Type.Forall (["A"], [Lang.Type.Int; Lang.Type.List (Lang.Type.Var "A"); Lang.Type.List (Lang.Type.Var "A")]));
       ("TLC.LibListZ.drop",
        Lang.Type.Forall (["A"], [Lang.Type.Int; Lang.Type.List (Lang.Type.Var "A"); Lang.Type.List (Lang.Type.Var "A")]));
       ("TLC.LibListZ.length",
        Lang.Type.Forall (["A"], [Lang.Type.List (Lang.Type.Var "A"); Lang.Type.Int]));
       ("TLC.LibListZ.make",
        Lang.Type.Forall (["A"], [Lang.Type.Int; Lang.Type.Var "A"; Lang.Type.List (Lang.Type.Var "A")]));
       ("TLC.LibListZ.sum",
        Lang.Type.Forall ([], [Lang.Type.List (Lang.Type.Int); Lang.Type.Int]));
       ("TLC.LibListZ.take",
        Lang.Type.Forall (["A"], [Lang.Type.Int; Lang.Type.List (Lang.Type.Var "A"); Lang.Type.List (Lang.Type.Var "A")]))
      ];
    properties =
      [("Proofs.Verify_seq_to_array_utils.case_rev_split",
        (["A"],
         [("xs", Lang.Type.List (Lang.Type.Var "A")); ("v", Lang.Type.Var "A");
          ("l", Lang.Type.List (Lang.Type.Var "A"));
          ("r", Lang.Type.List (Lang.Type.Var "A"))],
         [`Eq ((Lang.Type.List (Lang.Type.Var "A"),
                `App (("TLC.LibList.rev", [`Var ("xs")])),
                `App (("TLC.LibList.app",
                       [`Var ("l");
                        `Constructor (("::", [`Var ("v"); `Var ("r")]))]))))
         ],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"), `Var ("xs"),
               `App (("TLC.LibList.app",
                      [`App (("TLC.LibList.rev", [`Var ("r")]));
                       `Constructor (("::",
                                      [`Var ("v");
                                       `App (("TLC.LibList.rev", [`Var ("l")]))
                                      ]))
                      ]))))));
       ("CFML.Semantics.app_trms_vals_rev_cons",
        ([],
         [("v", Lang.Type.Val); ("vs", Lang.Type.List (Lang.Type.Val));
          ("ts", Lang.Type.List (Lang.Type.Val))],
         [],
         `Eq ((Lang.Type.List (Lang.Type.Val),
               `App (("TLC.LibList.app",
                      [`App (("TLC.LibList.rev",
                              [`Constructor (("::", [`Var ("v"); `Var ("vs")]))]));
                       `Var ("ts")])),
               `App (("TLC.LibList.app",
                      [`App (("TLC.LibList.rev", [`Var ("vs")]));
                       `Constructor (("::", [`Var ("v"); `Var ("ts")]))]))))));
       ("TLC.LibListZ.sum_app",
        ([],
         [("l1", Lang.Type.List (Lang.Type.Int));
          ("l2", Lang.Type.List (Lang.Type.Int))],
         [],
         `Eq ((Lang.Type.Int,
               `App (("TLC.LibListZ.sum",
                      [`App (("TLC.LibList.app", [`Var ("l1"); `Var ("l2")]))])),
               `App (("+",
                      [`App (("TLC.LibListZ.sum", [`Var ("l1")]));
                       `App (("TLC.LibListZ.sum", [`Var ("l2")]))]))))));
       ("TLC.LibListZ.list_eq_take_app_drop",
        (["A"],
         [("n", Lang.Type.Int); ("l", Lang.Type.List (Lang.Type.Var "A"))],
         [`Assert (`App (("TLC.LibOrder.le",
                          [`Var ("n");
                           `App (("TLC.LibListZ.length", [`Var ("l")]))])))
         ],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.app",
                      [`App (("TLC.LibListZ.take", [`Var ("n"); `Var ("l")]));
                       `App (("TLC.LibListZ.drop", [`Var ("n"); `Var ("l")]))])),
               `Var ("l")))));
       ("TLC.LibListZ.drop_app_length",
        (["A"],
         [("l", Lang.Type.List (Lang.Type.Var "A"));
          ("l'", Lang.Type.List (Lang.Type.Var "A"))],
         [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibListZ.drop",
                      [`App (("TLC.LibListZ.length", [`Var ("l")]));
                       `App (("TLC.LibList.app", [`Var ("l"); `Var ("l'")]))])),
               `Var ("l'")))));
       ("TLC.LibListZ.drop_app_r",
        (["A"],
         [("n", Lang.Type.Int); ("l", Lang.Type.List (Lang.Type.Var "A"));
          ("l'", Lang.Type.List (Lang.Type.Var "A"))],
         [`Assert (`App (("TLC.LibOrder.ge",
                          [`Var ("n");
                           `App (("TLC.LibListZ.length", [`Var ("l")]))])))
         ],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibListZ.drop",
                      [`Var ("n");
                       `App (("TLC.LibList.app", [`Var ("l"); `Var ("l'")]))])),
               `App (("TLC.LibListZ.drop",
                      [`App (("-",
                              [`Var ("n");
                               `App (("TLC.LibListZ.length", [`Var ("l")]))]));
                       `Var ("l'")]))))));
       ("TLC.LibListZ.drop_app_l",
        (["A"],
         [("n", Lang.Type.Int); ("l", Lang.Type.List (Lang.Type.Var "A"));
          ("l'", Lang.Type.List (Lang.Type.Var "A"))],
         [`Assert (`App (("TLC.LibOrder.le",
                          [`Var ("n");
                           `App (("TLC.LibListZ.length", [`Var ("l")]))])))
         ],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibListZ.drop",
                      [`Var ("n");
                       `App (("TLC.LibList.app", [`Var ("l"); `Var ("l'")]))])),
               `App (("TLC.LibList.app",
                      [`App (("TLC.LibListZ.drop", [`Var ("n"); `Var ("l")]));
                       `Var ("l'")]))))));
       ("TLC.LibListZ.take_prefix_length",
        (["A"],
         [("l", Lang.Type.List (Lang.Type.Var "A"));
          ("l'", Lang.Type.List (Lang.Type.Var "A"))],
         [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibListZ.take",
                      [`App (("TLC.LibListZ.length", [`Var ("l")]));
                       `App (("TLC.LibList.app", [`Var ("l"); `Var ("l'")]))])),
               `Var ("l")))));
       ("TLC.LibListZ.take_app_r",
        (["A"],
         [("n", Lang.Type.Int); ("l", Lang.Type.List (Lang.Type.Var "A"));
          ("l'", Lang.Type.List (Lang.Type.Var "A"))],
         [`Assert (`App (("TLC.LibOrder.ge",
                          [`Var ("n");
                           `App (("TLC.LibListZ.length", [`Var ("l")]))])))
         ],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibListZ.take",
                      [`Var ("n");
                       `App (("TLC.LibList.app", [`Var ("l"); `Var ("l'")]))])),
               `App (("TLC.LibList.app",
                      [`Var ("l");
                       `App (("TLC.LibListZ.take",
                              [`App (("-",
                                      [`Var ("n");
                                       `App (("TLC.LibListZ.length",
                                              [`Var ("l")]))
                                      ]));
                               `Var ("l'")]))
                      ]))))));
       ("TLC.LibListZ.take_app_l",
        (["A"],
         [("n", Lang.Type.Int); ("l", Lang.Type.List (Lang.Type.Var "A"));
          ("l'", Lang.Type.List (Lang.Type.Var "A"))],
         [`Assert (`App (("TLC.LibOrder.le",
                          [`Var ("n");
                           `App (("TLC.LibListZ.length", [`Var ("l")]))])))
         ],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibListZ.take",
                      [`Var ("n");
                       `App (("TLC.LibList.app", [`Var ("l"); `Var ("l'")]))])),
               `App (("TLC.LibListZ.take", [`Var ("n"); `Var ("l")]))))));
       ("TLC.LibListZ.make_succ_r",
        (["A"], [("n", Lang.Type.Int); ("v", Lang.Type.Var "A")],
         [`Assert (`App (("TLC.LibOrder.ge", [`Var ("n"); `Int (0)])))],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibListZ.make",
                      [`App (("+", [`Var ("n"); `Int (1)])); `Var ("v")])),
               `App (("TLC.LibList.app",
                      [`App (("TLC.LibListZ.make", [`Var ("n"); `Var ("v")]));
                       `Constructor (("::",
                                      [`Var ("v"); `Constructor (("[]", []))]))
                      ]))))));
       ("TLC.LibListZ.update_middle",
        (["A"],
         [("i", Lang.Type.Int); ("l1", Lang.Type.List (Lang.Type.Var "A"));
          ("l2", Lang.Type.List (Lang.Type.Var "A")); ("v", Lang.Type.Var "A");
          ("w", Lang.Type.Var "A")],
         [`Eq ((Lang.Type.Int, `Var ("i"),
                `App (("TLC.LibListZ.length", [`Var ("l1")]))))
         ],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibContainer.update",
                      [`App (("TLC.LibList.app",
                              [`Var ("l1");
                               `Constructor (("::", [`Var ("w"); `Var ("l2")]))
                              ]));
                       `Var ("i"); `Var ("v")])),
               `App (("TLC.LibList.app",
                      [`App (("TLC.LibList.app",
                              [`Var ("l1");
                               `Constructor (("::",
                                              [`Var ("v");
                                               `Constructor (("[]", []))]))
                              ]));
                       `Var ("l2")]))))));
       ("TLC.LibListZ.update_app_r",
        (["A"],
         [("l2", Lang.Type.List (Lang.Type.Var "A")); ("j", Lang.Type.Int);
          ("l1", Lang.Type.List (Lang.Type.Var "A")); ("i", Lang.Type.Int);
          ("ij", Lang.Type.Int); ("v", Lang.Type.Var "A")],
         [`Eq ((Lang.Type.Int, `Var ("i"),
                `App (("TLC.LibListZ.length", [`Var ("l1")]))));
          `Assert (`App (("TLC.LibOrder.le", [`Int (0); `Var ("j")])));
          `Eq ((Lang.Type.Int, `Var ("ij"),
                `App (("+", [`Var ("i"); `Var ("j")]))))
         ],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibContainer.update",
                      [`App (("TLC.LibList.app", [`Var ("l1"); `Var ("l2")]));
                       `Var ("ij"); `Var ("v")])),
               `App (("TLC.LibList.app",
                      [`Var ("l1");
                       `App (("TLC.LibContainer.update",
                              [`Var ("l2"); `Var ("j"); `Var ("v")]))
                      ]))))));
       ("TLC.LibListZ.length_last",
        (["A"],
         [("x", Lang.Type.Var "A"); ("l", Lang.Type.List (Lang.Type.Var "A"))],
         [],
         `Eq ((Lang.Type.Int,
               `App (("TLC.LibListZ.length",
                      [`App (("TLC.LibList.app",
                              [`Var ("l");
                               `Constructor (("::",
                                              [`Var ("x");
                                               `Constructor (("[]", []))]))
                              ]))
                      ])),
               `App (("+",
                      [`Int (1); `App (("TLC.LibListZ.length", [`Var ("l")]))]))))));
       ("TLC.LibListZ.length_app",
        (["A"],
         [("l1", Lang.Type.List (Lang.Type.Var "A"));
          ("l2", Lang.Type.List (Lang.Type.Var "A"))],
         [],
         `Eq ((Lang.Type.Int,
               `App (("TLC.LibListZ.length",
                      [`App (("TLC.LibList.app", [`Var ("l1"); `Var ("l2")]))])),
               `App (("+",
                      [`App (("TLC.LibListZ.length", [`Var ("l1")]));
                       `App (("TLC.LibListZ.length", [`Var ("l2")]))]))))));
       ("TLC.LibList.list_eq_take_app_drop",
        (["A"],
         [("n", Lang.Type.Int); ("l", Lang.Type.List (Lang.Type.Var "A"))],
         [`Assert (`App (("TLC.LibOrder.le",
                          [`Var ("n");
                           `App (("TLC.LibList.length", [`Var ("l")]))])))
         ],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.app",
                      [`App (("TLC.LibList.take", [`Var ("n"); `Var ("l")]));
                       `App (("TLC.LibList.drop", [`Var ("n"); `Var ("l")]))])),
               `Var ("l")))));
       ("TLC.LibList.drop_app_length",
        (["A"],
         [("l", Lang.Type.List (Lang.Type.Var "A"));
          ("l'", Lang.Type.List (Lang.Type.Var "A"))],
         [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.drop",
                      [`App (("TLC.LibList.length", [`Var ("l")]));
                       `App (("TLC.LibList.app", [`Var ("l"); `Var ("l'")]))])),
               `Var ("l'")))));
       ("TLC.LibList.drop_app_r",
        (["A"],
         [("n", Lang.Type.Int); ("l", Lang.Type.List (Lang.Type.Var "A"));
          ("l'", Lang.Type.List (Lang.Type.Var "A"))],
         [`Assert (`App (("TLC.LibOrder.ge",
                          [`Var ("n");
                           `App (("TLC.LibList.length", [`Var ("l")]))])))
         ],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.drop",
                      [`Var ("n");
                       `App (("TLC.LibList.app", [`Var ("l"); `Var ("l'")]))])),
               `App (("TLC.LibList.drop",
                      [`App (("-",
                              [`Var ("n");
                               `App (("TLC.LibList.length", [`Var ("l")]))]));
                       `Var ("l'")]))))));
       ("TLC.LibList.drop_app_l",
        (["A"],
         [("n", Lang.Type.Int); ("l", Lang.Type.List (Lang.Type.Var "A"));
          ("l'", Lang.Type.List (Lang.Type.Var "A"))],
         [`Assert (`App (("TLC.LibOrder.le",
                          [`Var ("n");
                           `App (("TLC.LibList.length", [`Var ("l")]))])))
         ],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.drop",
                      [`Var ("n");
                       `App (("TLC.LibList.app", [`Var ("l"); `Var ("l'")]))])),
               `App (("TLC.LibList.app",
                      [`App (("TLC.LibList.drop", [`Var ("n"); `Var ("l")]));
                       `Var ("l'")]))))));
       ("TLC.LibList.take_prefix_length",
        (["A"],
         [("l", Lang.Type.List (Lang.Type.Var "A"));
          ("l'", Lang.Type.List (Lang.Type.Var "A"))],
         [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.take",
                      [`App (("TLC.LibList.length", [`Var ("l")]));
                       `App (("TLC.LibList.app", [`Var ("l"); `Var ("l'")]))])),
               `Var ("l")))));
       ("TLC.LibList.take_app_r",
        (["A"],
         [("n", Lang.Type.Int); ("l", Lang.Type.List (Lang.Type.Var "A"));
          ("l'", Lang.Type.List (Lang.Type.Var "A"))],
         [`Assert (`App (("TLC.LibOrder.ge",
                          [`Var ("n");
                           `App (("TLC.LibList.length", [`Var ("l")]))])))
         ],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.take",
                      [`Var ("n");
                       `App (("TLC.LibList.app", [`Var ("l"); `Var ("l'")]))])),
               `App (("TLC.LibList.app",
                      [`Var ("l");
                       `App (("TLC.LibList.take",
                              [`App (("-",
                                      [`Var ("n");
                                       `App (("TLC.LibList.length",
                                              [`Var ("l")]))
                                      ]));
                               `Var ("l'")]))
                      ]))))));
       ("TLC.LibList.take_app_l",
        (["A"],
         [("n", Lang.Type.Int); ("l", Lang.Type.List (Lang.Type.Var "A"));
          ("l'", Lang.Type.List (Lang.Type.Var "A"))],
         [`Assert (`App (("TLC.LibOrder.le",
                          [`Var ("n");
                           `App (("TLC.LibList.length", [`Var ("l")]))])))
         ],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.take",
                      [`Var ("n");
                       `App (("TLC.LibList.app", [`Var ("l"); `Var ("l'")]))])),
               `App (("TLC.LibList.take", [`Var ("n"); `Var ("l")]))))));
       ("TLC.LibList.split_last",
        (["A"; "B"],
         [("x", Lang.Type.Var "A"); ("y", Lang.Type.Var "B");
          ("l",
           Lang.Type.List (Lang.Type.Product ([Lang.Type.Var "A"; Lang.Type.Var "B"])));
          ("r", Lang.Type.List (Lang.Type.Var "A"));
          ("s", Lang.Type.List (Lang.Type.Var "B"))],
         [`Eq ((Lang.Type.Product ([Lang.Type.List (Lang.Type.Var "A"); Lang.Type.List (Lang.Type.Var "B")]),
                `Tuple ([`Var ("r"); `Var ("s")]),
                `App (("TLC.LibList.split", [`Var ("l")]))))
         ],
         `Eq ((Lang.Type.Product ([Lang.Type.List (Lang.Type.Var "A"); Lang.Type.List (Lang.Type.Var "B")]),
               `App (("TLC.LibList.split",
                      [`App (("TLC.LibList.app",
                              [`Var ("l");
                               `Constructor (("::",
                                              [`Tuple ([`Var ("x"); `Var ("y")]);
                                               `Constructor (("[]", []))]))
                              ]))
                      ])),
               `Tuple ([`App (("TLC.LibList.app",
                               [`Var ("r");
                                `Constructor (("::",
                                               [`Var ("x");
                                                `Constructor (("[]", []))]))
                               ]));
                        `App (("TLC.LibList.app",
                               [`Var ("s");
                                `Constructor (("::",
                                               [`Var ("y");
                                                `Constructor (("[]", []))]))
                               ]))
                       ])))));
       ("TLC.LibList.split_app",
        (["A"; "B"],
         [("l1",
           Lang.Type.List (Lang.Type.Product ([Lang.Type.Var "A"; Lang.Type.Var "B"])));
          ("l2",
           Lang.Type.List (Lang.Type.Product ([Lang.Type.Var "A"; Lang.Type.Var "B"])));
          ("r1", Lang.Type.List (Lang.Type.Var "A"));
          ("r2", Lang.Type.List (Lang.Type.Var "A"));
          ("s1", Lang.Type.List (Lang.Type.Var "B"));
          ("s2", Lang.Type.List (Lang.Type.Var "B"))],
         [`Eq ((Lang.Type.Product ([Lang.Type.List (Lang.Type.Var "A"); Lang.Type.List (Lang.Type.Var "B")]),
                `Tuple ([`Var ("r1"); `Var ("s1")]),
                `App (("TLC.LibList.split", [`Var ("l1")]))));
          `Eq ((Lang.Type.Product ([Lang.Type.List (Lang.Type.Var "A"); Lang.Type.List (Lang.Type.Var "B")]),
                `Tuple ([`Var ("r2"); `Var ("s2")]),
                `App (("TLC.LibList.split", [`Var ("l2")]))))
         ],
         `Eq ((Lang.Type.Product ([Lang.Type.List (Lang.Type.Var "A"); Lang.Type.List (Lang.Type.Var "B")]),
               `App (("TLC.LibList.split",
                      [`App (("TLC.LibList.app", [`Var ("l1"); `Var ("l2")]))])),
               `Tuple ([`App (("TLC.LibList.app", [`Var ("r1"); `Var ("r2")]));
                        `App (("TLC.LibList.app", [`Var ("s1"); `Var ("s2")]))])))));
       ("TLC.LibList.combine_last",
        (["A"; "B"],
         [("x", Lang.Type.Var "A"); ("r", Lang.Type.List (Lang.Type.Var "A"));
          ("y", Lang.Type.Var "B"); ("s", Lang.Type.List (Lang.Type.Var "B"))],
         [`Eq ((Lang.Type.Int, `App (("TLC.LibList.length", [`Var ("r")])),
                `App (("TLC.LibList.length", [`Var ("s")]))))
         ],
         `Eq ((Lang.Type.List (Lang.Type.Product ([Lang.Type.Var "A"; Lang.Type.Var "B"])),
               `App (("TLC.LibList.combine",
                      [`App (("TLC.LibList.app",
                              [`Var ("r");
                               `Constructor (("::",
                                              [`Var ("x");
                                               `Constructor (("[]", []))]))
                              ]));
                       `App (("TLC.LibList.app",
                              [`Var ("s");
                               `Constructor (("::",
                                              [`Var ("y");
                                               `Constructor (("[]", []))]))
                              ]))
                      ])),
               `App (("TLC.LibList.app",
                      [`App (("TLC.LibList.combine", [`Var ("r"); `Var ("s")]));
                       `Constructor (("::",
                                      [`Tuple ([`Var ("x"); `Var ("y")]);
                                       `Constructor (("[]", []))]))
                      ]))))));
       ("TLC.LibList.combine_app",
        (["A"; "B"],
         [("r1", Lang.Type.List (Lang.Type.Var "A"));
          ("r2", Lang.Type.List (Lang.Type.Var "A"));
          ("s1", Lang.Type.List (Lang.Type.Var "B"));
          ("s2", Lang.Type.List (Lang.Type.Var "B"))],
         [`Eq ((Lang.Type.Int, `App (("TLC.LibList.length", [`Var ("r1")])),
                `App (("TLC.LibList.length", [`Var ("s1")]))))
         ],
         `Eq ((Lang.Type.List (Lang.Type.Product ([Lang.Type.Var "A"; Lang.Type.Var "B"])),
               `App (("TLC.LibList.combine",
                      [`App (("TLC.LibList.app", [`Var ("r1"); `Var ("r2")]));
                       `App (("TLC.LibList.app", [`Var ("s1"); `Var ("s2")]))])),
               `App (("TLC.LibList.app",
                      [`App (("TLC.LibList.combine", [`Var ("r1"); `Var ("s1")]));
                       `App (("TLC.LibList.combine", [`Var ("r2"); `Var ("s2")]))
                      ]))))));
       ("TLC.LibList.concat_last",
        (["A"],
         [("l", Lang.Type.List (Lang.Type.Var "A"));
          ("m", Lang.Type.List (Lang.Type.List (Lang.Type.Var "A")))],
         [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.concat",
                      [`App (("TLC.LibList.app",
                              [`Var ("m");
                               `Constructor (("::",
                                              [`Var ("l");
                                               `Constructor (("[]", []))]))
                              ]))
                      ])),
               `App (("TLC.LibList.app",
                      [`App (("TLC.LibList.concat", [`Var ("m")])); `Var ("l")]))))));
       ("TLC.LibList.concat_app",
        (["A"],
         [("m1", Lang.Type.List (Lang.Type.List (Lang.Type.Var "A")));
          ("m2", Lang.Type.List (Lang.Type.List (Lang.Type.Var "A")))],
         [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.concat",
                      [`App (("TLC.LibList.app", [`Var ("m1"); `Var ("m2")]))])),
               `App (("TLC.LibList.app",
                      [`App (("TLC.LibList.concat", [`Var ("m1")]));
                       `App (("TLC.LibList.concat", [`Var ("m2")]))]))))));
       ("TLC.LibList.concat_cons",
        (["A"],
         [("l", Lang.Type.List (Lang.Type.Var "A"));
          ("m", Lang.Type.List (Lang.Type.List (Lang.Type.Var "A")))],
         [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.concat",
                      [`Constructor (("::", [`Var ("l"); `Var ("m")]))])),
               `App (("TLC.LibList.app",
                      [`Var ("l"); `App (("TLC.LibList.concat", [`Var ("m")]))]))))));
       ("TLC.LibList.rev_last",
        (["A"],
         [("x", Lang.Type.Var "A"); ("l", Lang.Type.List (Lang.Type.Var "A"))],
         [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.rev",
                      [`App (("TLC.LibList.app",
                              [`Var ("l");
                               `Constructor (("::",
                                              [`Var ("x");
                                               `Constructor (("[]", []))]))
                              ]))
                      ])),
               `Constructor (("::",
                              [`Var ("x");
                               `App (("TLC.LibList.rev", [`Var ("l")]))]))))));
       ("TLC.LibList.rev_cons",
        (["A"],
         [("x", Lang.Type.Var "A"); ("l", Lang.Type.List (Lang.Type.Var "A"))],
         [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.rev",
                      [`Constructor (("::", [`Var ("x"); `Var ("l")]))])),
               `App (("TLC.LibList.app",
                      [`App (("TLC.LibList.rev", [`Var ("l")]));
                       `Constructor (("::",
                                      [`Var ("x"); `Constructor (("[]", []))]))
                      ]))))));
       ("TLC.LibList.rev_app",
        (["A"],
         [("l1", Lang.Type.List (Lang.Type.Var "A"));
          ("l2", Lang.Type.List (Lang.Type.Var "A"))],
         [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.rev",
                      [`App (("TLC.LibList.app", [`Var ("l1"); `Var ("l2")]))])),
               `App (("TLC.LibList.app",
                      [`App (("TLC.LibList.rev", [`Var ("l2")]));
                       `App (("TLC.LibList.rev", [`Var ("l1")]))]))))));
       ("TLC.LibList.length_app",
        (["A"],
         [("l1", Lang.Type.List (Lang.Type.Var "A"));
          ("l2", Lang.Type.List (Lang.Type.Var "A"))],
         [],
         `Eq ((Lang.Type.Int,
               `App (("TLC.LibList.length",
                      [`App (("TLC.LibList.app", [`Var ("l1"); `Var ("l2")]))])),
               `App (("+",
                      [`App (("TLC.LibList.length", [`Var ("l1")]));
                       `App (("TLC.LibList.length", [`Var ("l2")]))]))))));
       ("TLC.LibList.last_app",
        (["A"],
         [("x", Lang.Type.Var "A"); ("l1", Lang.Type.List (Lang.Type.Var "A"));
          ("l2", Lang.Type.List (Lang.Type.Var "A"))],
         [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.app",
                      [`App (("TLC.LibList.app", [`Var ("l1"); `Var ("l2")]));
                       `Constructor (("::",
                                      [`Var ("x"); `Constructor (("[]", []))]))
                      ])),
               `App (("TLC.LibList.app",
                      [`Var ("l1");
                       `App (("TLC.LibList.app",
                              [`Var ("l2");
                               `Constructor (("::",
                                              [`Var ("x");
                                               `Constructor (("[]", []))]))
                              ]))
                      ]))))));
       ("TLC.LibList.last_one",
        (["A"], [("x", Lang.Type.Var "A"); ("y", Lang.Type.Var "A")], [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.app",
                      [`Constructor (("::",
                                      [`Var ("x"); `Constructor (("[]", []))]));
                       `Constructor (("::",
                                      [`Var ("y"); `Constructor (("[]", []))]))
                      ])),
               `Constructor (("::",
                              [`Var ("x");
                               `Constructor (("::",
                                              [`Var ("y");
                                               `Constructor (("[]", []))]))
                              ]))))));
       ("TLC.LibList.last_cons",
        (["A"],
         [("x", Lang.Type.Var "A"); ("y", Lang.Type.Var "A");
          ("l", Lang.Type.List (Lang.Type.Var "A"))],
         [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.app",
                      [`Constructor (("::", [`Var ("x"); `Var ("l")]));
                       `Constructor (("::",
                                      [`Var ("y"); `Constructor (("[]", []))]))
                      ])),
               `Constructor (("::",
                              [`Var ("x");
                               `App (("TLC.LibList.app",
                                      [`Var ("l");
                                       `Constructor (("::",
                                                      [`Var ("y");
                                                       `Constructor (
                                                         ("[]", []))]))
                                      ]))
                              ]))))));
       ("TLC.LibList.last_nil",
        (["A"], [("x", Lang.Type.Var "A")], [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.app",
                      [`Constructor (("[]", []));
                       `Constructor (("::",
                                      [`Var ("x"); `Constructor (("[]", []))]))
                      ])),
               `Constructor (("::", [`Var ("x"); `Constructor (("[]", []))]))))));
       ("TLC.LibList.app_last_r",
        (["A"],
         [("x", Lang.Type.Var "A"); ("l1", Lang.Type.List (Lang.Type.Var "A"));
          ("l2", Lang.Type.List (Lang.Type.Var "A"))],
         [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.app",
                      [`Var ("l1");
                       `App (("TLC.LibList.app",
                              [`Var ("l2");
                               `Constructor (("::",
                                              [`Var ("x");
                                               `Constructor (("[]", []))]))
                              ]))
                      ])),
               `App (("TLC.LibList.app",
                      [`App (("TLC.LibList.app", [`Var ("l1"); `Var ("l2")]));
                       `Constructor (("::",
                                      [`Var ("x"); `Constructor (("[]", []))]))
                      ]))))));
       ("TLC.LibList.app_last_l",
        (["A"],
         [("x", Lang.Type.Var "A"); ("l1", Lang.Type.List (Lang.Type.Var "A"));
          ("l2", Lang.Type.List (Lang.Type.Var "A"))],
         [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.app",
                      [`App (("TLC.LibList.app",
                              [`Var ("l1");
                               `Constructor (("::",
                                              [`Var ("x");
                                               `Constructor (("[]", []))]))
                              ]));
                       `Var ("l2")])),
               `App (("TLC.LibList.app",
                      [`Var ("l1");
                       `Constructor (("::", [`Var ("x"); `Var ("l2")]))]))))));
       ("TLC.LibList.app_cons_one_l",
        (["A"],
         [("x", Lang.Type.Var "A"); ("l", Lang.Type.List (Lang.Type.Var "A"))],
         [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.app",
                      [`Var ("l");
                       `Constructor (("::",
                                      [`Var ("x"); `Constructor (("[]", []))]))
                      ])),
               `App (("TLC.LibList.app",
                      [`Var ("l");
                       `Constructor (("::",
                                      [`Var ("x"); `Constructor (("[]", []))]))
                      ]))))));
       ("TLC.LibList.app_cons_one_r",
        (["A"],
         [("x", Lang.Type.Var "A"); ("l", Lang.Type.List (Lang.Type.Var "A"))],
         [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.app",
                      [`Constructor (("::",
                                      [`Var ("x"); `Constructor (("[]", []))]));
                       `Var ("l")])),
               `Constructor (("::", [`Var ("x"); `Var ("l")]))))));
       ("TLC.LibList.app_cons_r",
        (["A"],
         [("x", Lang.Type.Var "A"); ("l1", Lang.Type.List (Lang.Type.Var "A"));
          ("l2", Lang.Type.List (Lang.Type.Var "A"))],
         [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.app",
                      [`Var ("l1");
                       `Constructor (("::", [`Var ("x"); `Var ("l2")]))])),
               `App (("TLC.LibList.app",
                      [`App (("TLC.LibList.app",
                              [`Var ("l1");
                               `Constructor (("::",
                                              [`Var ("x");
                                               `Constructor (("[]", []))]))
                              ]));
                       `Var ("l2")]))))));
       ("TLC.LibList.app_assoc",
        (["A"],
         [("l1", Lang.Type.List (Lang.Type.Var "A"));
          ("l2", Lang.Type.List (Lang.Type.Var "A"));
          ("l3", Lang.Type.List (Lang.Type.Var "A"))],
         [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.app",
                      [`App (("TLC.LibList.app", [`Var ("l1"); `Var ("l2")]));
                       `Var ("l3")])),
               `App (("TLC.LibList.app",
                      [`Var ("l1");
                       `App (("TLC.LibList.app", [`Var ("l2"); `Var ("l3")]))]))))));
       ("TLC.LibList.app_nil_r",
        (["A"], [("l", Lang.Type.List (Lang.Type.Var "A"))], [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.app", [`Var ("l"); `Constructor (("[]", []))])),
               `Var ("l")))));
       ("TLC.LibList.app_nil_l",
        (["A"], [("l", Lang.Type.List (Lang.Type.Var "A"))], [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.app", [`Constructor (("[]", [])); `Var ("l")])),
               `Var ("l")))));
       ("TLC.LibList.app_cons_l",
        (["A"],
         [("x", Lang.Type.Var "A"); ("l1", Lang.Type.List (Lang.Type.Var "A"));
          ("l2", Lang.Type.List (Lang.Type.Var "A"))],
         [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.app",
                      [`Constructor (("::", [`Var ("x"); `Var ("l1")]));
                       `Var ("l2")])),
               `Constructor (("::",
                              [`Var ("x");
                               `App (("TLC.LibList.app",
                                      [`Var ("l1"); `Var ("l2")]))
                              ]))))));
       ("Proofs.Verify_seq_to_array_utils.case_rev_split",
        (["A"],
         [("xs", Lang.Type.List (Lang.Type.Var "A")); ("v", Lang.Type.Var "A");
          ("l", Lang.Type.List (Lang.Type.Var "A"));
          ("r", Lang.Type.List (Lang.Type.Var "A"))],
         [`Eq ((Lang.Type.List (Lang.Type.Var "A"),
                `App (("TLC.LibList.rev", [`Var ("xs")])),
                `App (("TLC.LibList.app",
                       [`Var ("l");
                        `Constructor (("::", [`Var ("v"); `Var ("r")]))]))))
         ],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"), `Var ("xs"),
               `App (("TLC.LibList.app",
                      [`App (("TLC.LibList.rev", [`Var ("r")]));
                       `Constructor (("::",
                                      [`Var ("v");
                                       `App (("TLC.LibList.rev", [`Var ("l")]))
                                      ]))
                      ]))))));
       ("CFML.Semantics.app_trms_vals_rev_cons",
        ([],
         [("v", Lang.Type.Val); ("vs", Lang.Type.List (Lang.Type.Val));
          ("ts", Lang.Type.List (Lang.Type.Val))],
         [],
         `Eq ((Lang.Type.List (Lang.Type.Val),
               `App (("TLC.LibList.app",
                      [`App (("TLC.LibList.rev",
                              [`Constructor (("::", [`Var ("v"); `Var ("vs")]))]));
                       `Var ("ts")])),
               `App (("TLC.LibList.app",
                      [`App (("TLC.LibList.rev", [`Var ("vs")]));
                       `Constructor (("::", [`Var ("v"); `Var ("ts")]))]))))));
       ("TLC.LibListZ.length_rev",
        (["A"], [("l", Lang.Type.List (Lang.Type.Var "A"))], [],
         `Eq ((Lang.Type.Int,
               `App (("TLC.LibListZ.length",
                      [`App (("TLC.LibList.rev", [`Var ("l")]))])),
               `App (("TLC.LibListZ.length", [`Var ("l")]))))));
       ("TLC.LibList.combine_rev",
        (["A"; "B"],
         [("r", Lang.Type.List (Lang.Type.Var "A"));
          ("s", Lang.Type.List (Lang.Type.Var "B"))],
         [`Eq ((Lang.Type.Int, `App (("TLC.LibList.length", [`Var ("r")])),
                `App (("TLC.LibList.length", [`Var ("s")]))))
         ],
         `Eq ((Lang.Type.List (Lang.Type.Product ([Lang.Type.Var "A"; Lang.Type.Var "B"])),
               `App (("TLC.LibList.combine",
                      [`App (("TLC.LibList.rev", [`Var ("r")]));
                       `App (("TLC.LibList.rev", [`Var ("s")]))])),
               `App (("TLC.LibList.rev",
                      [`App (("TLC.LibList.combine", [`Var ("r"); `Var ("s")]))]))))));
       ("TLC.LibList.length_rev",
        (["A"], [("l", Lang.Type.List (Lang.Type.Var "A"))], [],
         `Eq ((Lang.Type.Int,
               `App (("TLC.LibList.length",
                      [`App (("TLC.LibList.rev", [`Var ("l")]))])),
               `App (("TLC.LibList.length", [`Var ("l")]))))));
       ("TLC.LibList.rev_rev",
        (["A"], [("l", Lang.Type.List (Lang.Type.Var "A"))], [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.rev",
                      [`App (("TLC.LibList.rev", [`Var ("l")]))])),
               `Var ("l")))));
       ("TLC.LibList.rev_last",
        (["A"],
         [("x", Lang.Type.Var "A"); ("l", Lang.Type.List (Lang.Type.Var "A"))],
         [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.rev",
                      [`App (("TLC.LibList.app",
                              [`Var ("l");
                               `Constructor (("::",
                                              [`Var ("x");
                                               `Constructor (("[]", []))]))
                              ]))
                      ])),
               `Constructor (("::",
                              [`Var ("x");
                               `App (("TLC.LibList.rev", [`Var ("l")]))]))))));
       ("TLC.LibList.rev_one",
        (["A"], [("x", Lang.Type.Var "A")], [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.rev",
                      [`Constructor (("::",
                                      [`Var ("x"); `Constructor (("[]", []))]))
                      ])),
               `Constructor (("::", [`Var ("x"); `Constructor (("[]", []))]))))));
       ("TLC.LibList.rev_cons",
        (["A"],
         [("x", Lang.Type.Var "A"); ("l", Lang.Type.List (Lang.Type.Var "A"))],
         [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.rev",
                      [`Constructor (("::", [`Var ("x"); `Var ("l")]))])),
               `App (("TLC.LibList.app",
                      [`App (("TLC.LibList.rev", [`Var ("l")]));
                       `Constructor (("::",
                                      [`Var ("x"); `Constructor (("[]", []))]))
                      ]))))));
       ("TLC.LibList.rev_app",
        (["A"],
         [("l1", Lang.Type.List (Lang.Type.Var "A"));
          ("l2", Lang.Type.List (Lang.Type.Var "A"))],
         [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.rev",
                      [`App (("TLC.LibList.app", [`Var ("l1"); `Var ("l2")]))])),
               `App (("TLC.LibList.app",
                      [`App (("TLC.LibList.rev", [`Var ("l2")]));
                       `App (("TLC.LibList.rev", [`Var ("l1")]))]))))));
       ("TLC.LibList.rev_nil",
        (["A"], [], [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibList.rev", [`Constructor (("[]", []))])),
               `Constructor (("[]", []))))));
       ("Hlenls",
        ([], [], [],
         `Eq ((Lang.Type.Product ([Lang.Type.Int; Lang.Type.List (Lang.Type.Var "A")]),
               `Tuple ([`Var ("len");
                        `Constructor (("::", [`Var ("init"); `Var ("rest")]))]),
               `Tuple ([`App (("TLC.LibListZ.length", [`Var ("l")]));
                        `App (("TLC.LibList.rev", [`Var ("l")]))])))));
       ("Hls",
        ([], [], [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `Constructor (("::", [`Var ("init"); `Var ("rest")])),
               `App (("TLC.LibList.rev", [`Var ("l")]))))));
       ("Proofs.Verify_seq_to_array_utils.drop_last",
        (["A"],
         [("xs", Lang.Type.List (Lang.Type.Var "A"));
          ("rst", Lang.Type.List (Lang.Type.Var "A"));
          ("lst", Lang.Type.Var "A")],
         [`Eq ((Lang.Type.List (Lang.Type.Var "A"),
                `App (("TLC.LibList.rev", [`Var ("xs")])),
                `Constructor (("::", [`Var ("lst"); `Var ("rst")]))))
         ],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibListZ.drop",
                      [`App (("-",
                              [`App (("TLC.LibListZ.length", [`Var ("xs")]));
                               `Int (1)]));
                       `Var ("xs")])),
               `Constructor (("::", [`Var ("lst"); `Constructor (("[]", []))]))))));
       ("TLC.LibListZ.length_drop",
        (["A"],
         [("n", Lang.Type.Int); ("l", Lang.Type.List (Lang.Type.Var "A"))],
         [`Assert (`App (("TLC.LibOrder.le",
                          [`Var ("n");
                           `App (("TLC.LibListZ.length", [`Var ("l")]))])))
         ],
         `Eq ((Lang.Type.Int,
               `App (("TLC.LibListZ.length",
                      [`App (("TLC.LibListZ.drop", [`Var ("n"); `Var ("l")]))])),
               `App (("Coq.ZArith.BinInt.Z.min",
                      [`App (("TLC.LibListZ.length", [`Var ("l")]));
                       `App (("-",
                              [`App (("TLC.LibListZ.length", [`Var ("l")]));
                               `Var ("n")]))
                      ]))))));
       ("TLC.LibListZ.length_take",
        (["A"],
         [("n", Lang.Type.Int); ("l", Lang.Type.List (Lang.Type.Var "A"))],
         [`Assert (`App (("TLC.LibOrder.le",
                          [`Var ("n");
                           `App (("TLC.LibListZ.length", [`Var ("l")]))])))
         ],
         `Eq ((Lang.Type.Int,
               `App (("TLC.LibListZ.length",
                      [`App (("TLC.LibListZ.take", [`Var ("n"); `Var ("l")]))])),
               `App (("Coq.ZArith.BinInt.Z.max", [`Int (0); `Var ("n")]))))));
       ("TLC.LibListZ.drop_at_length",
        (["A"], [("l", Lang.Type.List (Lang.Type.Var "A"))], [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibListZ.drop",
                      [`App (("TLC.LibListZ.length", [`Var ("l")])); `Var ("l")])),
               `Constructor (("[]", []))))));
       ("TLC.LibListZ.drop_app_length",
        (["A"],
         [("l", Lang.Type.List (Lang.Type.Var "A"));
          ("l'", Lang.Type.List (Lang.Type.Var "A"))],
         [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibListZ.drop",
                      [`App (("TLC.LibListZ.length", [`Var ("l")]));
                       `App (("TLC.LibList.app", [`Var ("l"); `Var ("l'")]))])),
               `Var ("l'")))));
       ("TLC.LibListZ.drop_app_r",
        (["A"],
         [("n", Lang.Type.Int); ("l", Lang.Type.List (Lang.Type.Var "A"));
          ("l'", Lang.Type.List (Lang.Type.Var "A"))],
         [`Assert (`App (("TLC.LibOrder.ge",
                          [`Var ("n");
                           `App (("TLC.LibListZ.length", [`Var ("l")]))])))
         ],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibListZ.drop",
                      [`Var ("n");
                       `App (("TLC.LibList.app", [`Var ("l"); `Var ("l'")]))])),
               `App (("TLC.LibListZ.drop",
                      [`App (("-",
                              [`Var ("n");
                               `App (("TLC.LibListZ.length", [`Var ("l")]))]));
                       `Var ("l'")]))))));
       ("TLC.LibListZ.take_full_length",
        (["A"], [("l", Lang.Type.List (Lang.Type.Var "A"))], [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibListZ.take",
                      [`App (("TLC.LibListZ.length", [`Var ("l")])); `Var ("l")])),
               `Var ("l")))));
       ("TLC.LibListZ.take_prefix_length",
        (["A"],
         [("l", Lang.Type.List (Lang.Type.Var "A"));
          ("l'", Lang.Type.List (Lang.Type.Var "A"))],
         [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibListZ.take",
                      [`App (("TLC.LibListZ.length", [`Var ("l")]));
                       `App (("TLC.LibList.app", [`Var ("l"); `Var ("l'")]))])),
               `Var ("l")))));
       ("TLC.LibListZ.take_app_r",
        (["A"],
         [("n", Lang.Type.Int); ("l", Lang.Type.List (Lang.Type.Var "A"));
          ("l'", Lang.Type.List (Lang.Type.Var "A"))],
         [`Assert (`App (("TLC.LibOrder.ge",
                          [`Var ("n");
                           `App (("TLC.LibListZ.length", [`Var ("l")]))])))
         ],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibListZ.take",
                      [`Var ("n");
                       `App (("TLC.LibList.app", [`Var ("l"); `Var ("l'")]))])),
               `App (("TLC.LibList.app",
                      [`Var ("l");
                       `App (("TLC.LibListZ.take",
                              [`App (("-",
                                      [`Var ("n");
                                       `App (("TLC.LibListZ.length",
                                              [`Var ("l")]))
                                      ]));
                               `Var ("l'")]))
                      ]))))));
       ("TLC.LibListZ.length_remove",
        (["A"],
         [("l", Lang.Type.List (Lang.Type.Var "A")); ("a", Lang.Type.Var "A")],
         [],
         `Assert (`App (("TLC.LibOrder.le",
                         [`App (("TLC.LibListZ.length",
                                 [`App (("TLC.LibList.remove",
                                         [`Var ("a"); `Var ("l")]))
                                 ]));
                          `App (("TLC.LibListZ.length", [`Var ("l")]))])))));
       ("TLC.LibListZ.length_rev",
        (["A"], [("l", Lang.Type.List (Lang.Type.Var "A"))], [],
         `Eq ((Lang.Type.Int,
               `App (("TLC.LibListZ.length",
                      [`App (("TLC.LibList.rev", [`Var ("l")]))])),
               `App (("TLC.LibListZ.length", [`Var ("l")]))))));
       ("TLC.LibListZ.length_make",
        (["A"], [("n", Lang.Type.Int); ("v", Lang.Type.Var "A")],
         [`Assert (`App (("TLC.LibOrder.ge", [`Var ("n"); `Int (0)])))],
         `Eq ((Lang.Type.Int,
               `App (("TLC.LibListZ.length",
                      [`App (("TLC.LibListZ.make", [`Var ("n"); `Var ("v")]))])),
               `Var ("n")))));
       ("TLC.LibListZ.length_update",
        (["A"],
         [("l", Lang.Type.List (Lang.Type.Var "A")); ("i", Lang.Type.Int);
          ("v", Lang.Type.Var "A")],
         [],
         `Eq ((Lang.Type.Int,
               `App (("TLC.LibListZ.length",
                      [`App (("TLC.LibContainer.update",
                              [`Var ("l"); `Var ("i"); `Var ("v")]))
                      ])),
               `App (("TLC.LibListZ.length", [`Var ("l")]))))));
       ("TLC.LibListZ.Unnamed_thm",
        (["A"], [("l", Lang.Type.List (Lang.Type.Var "A"))], [],
         `Assert (`App (("TLC.LibOrder.le",
                         [`Int (0); `App (("TLC.LibListZ.length", [`Var ("l")]))
                         ])))));
       ("TLC.LibListZ.length_last",
        (["A"],
         [("x", Lang.Type.Var "A"); ("l", Lang.Type.List (Lang.Type.Var "A"))],
         [],
         `Eq ((Lang.Type.Int,
               `App (("TLC.LibListZ.length",
                      [`App (("TLC.LibList.app",
                              [`Var ("l");
                               `Constructor (("::",
                                              [`Var ("x");
                                               `Constructor (("[]", []))]))
                              ]))
                      ])),
               `App (("+",
                      [`Int (1); `App (("TLC.LibListZ.length", [`Var ("l")]))]))))));
       ("TLC.LibListZ.length_app",
        (["A"],
         [("l1", Lang.Type.List (Lang.Type.Var "A"));
          ("l2", Lang.Type.List (Lang.Type.Var "A"))],
         [],
         `Eq ((Lang.Type.Int,
               `App (("TLC.LibListZ.length",
                      [`App (("TLC.LibList.app", [`Var ("l1"); `Var ("l2")]))])),
               `App (("+",
                      [`App (("TLC.LibListZ.length", [`Var ("l1")]));
                       `App (("TLC.LibListZ.length", [`Var ("l2")]))]))))));
       ("TLC.LibListZ.length_one",
        (["A"], [("x", Lang.Type.Var "A")], [],
         `Eq ((Lang.Type.Int,
               `App (("TLC.LibListZ.length",
                      [`Constructor (("::",
                                      [`Var ("x"); `Constructor (("[]", []))]))
                      ])),
               `Int (1)))));
       ("TLC.LibListZ.length_cons",
        (["A"],
         [("x", Lang.Type.Var "A"); ("l", Lang.Type.List (Lang.Type.Var "A"))],
         [],
         `Eq ((Lang.Type.Int,
               `App (("TLC.LibListZ.length",
                      [`Constructor (("::", [`Var ("x"); `Var ("l")]))])),
               `App (("+",
                      [`Int (1); `App (("TLC.LibListZ.length", [`Var ("l")]))]))))));
       ("TLC.LibListZ.length_nil",
        (["A"], [], [],
         `Eq ((Lang.Type.Int,
               `App (("TLC.LibListZ.length", [`Constructor (("[]", []))])),
               `Int (0)))));
       ("TLC.LibListZ.length_nonneg",
        (["A"], [("l", Lang.Type.List (Lang.Type.Var "A"))], [],
         `Assert (`App (("TLC.LibOrder.le",
                         [`Int (0); `App (("TLC.LibListZ.length", [`Var ("l")]))
                         ])))));
       ("TLC.LibListZ.length_eq",
        (["A"], [("l", Lang.Type.List (Lang.Type.Var "A"))], [],
         `Eq ((Lang.Type.Int, `App (("TLC.LibListZ.length", [`Var ("l")])),
               `App (("TLC.LibList.length", [`Var ("l")]))))));
       ("Hlenls",
        ([], [], [],
         `Eq ((Lang.Type.Product ([Lang.Type.Int; Lang.Type.List (Lang.Type.Var "A")]),
               `Tuple ([`Var ("len");
                        `Constructor (("::", [`Var ("init"); `Var ("rest")]))]),
               `Tuple ([`App (("TLC.LibListZ.length", [`Var ("l")]));
                        `App (("TLC.LibList.rev", [`Var ("l")]))])))));
       ("Hlen",
        ([], [], [],
         `Eq ((Lang.Type.Int, `Var ("len"),
               `App (("TLC.LibListZ.length", [`Var ("l")]))))));
       ("TLC.LibListZ.make_eq_cons_make_pred",
        (["A"], [("n", Lang.Type.Int); ("v", Lang.Type.Var "A")],
         [`Assert (`App (("TLC.LibOrder.lt", [`Int (0); `Var ("n")])))],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibListZ.make", [`Var ("n"); `Var ("v")])),
               `Constructor (("::",
                              [`Var ("v");
                               `App (("TLC.LibListZ.make",
                                      [`App (("-", [`Var ("n"); `Int (1)]));
                                       `Var ("v")]))
                              ]))))));
       ("TLC.LibListZ.make_succ_r",
        (["A"], [("n", Lang.Type.Int); ("v", Lang.Type.Var "A")],
         [`Assert (`App (("TLC.LibOrder.ge", [`Var ("n"); `Int (0)])))],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibListZ.make",
                      [`App (("+", [`Var ("n"); `Int (1)])); `Var ("v")])),
               `App (("TLC.LibList.app",
                      [`App (("TLC.LibListZ.make", [`Var ("n"); `Var ("v")]));
                       `Constructor (("::",
                                      [`Var ("v"); `Constructor (("[]", []))]))
                      ]))))));
       ("TLC.LibListZ.make_succ_l",
        (["A"], [("n", Lang.Type.Int); ("v", Lang.Type.Var "A")],
         [`Assert (`App (("TLC.LibOrder.ge", [`Var ("n"); `Int (0)])))],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibListZ.make",
                      [`App (("+", [`Var ("n"); `Int (1)])); `Var ("v")])),
               `Constructor (("::",
                              [`Var ("v");
                               `App (("TLC.LibListZ.make",
                                      [`Var ("n"); `Var ("v")]))
                              ]))))));
       ("TLC.LibListZ.make_zero",
        (["A"], [("v", Lang.Type.Var "A")], [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"),
               `App (("TLC.LibListZ.make", [`Int (0); `Var ("v")])),
               `Constructor (("[]", []))))));
       ("TLC.LibListZ.length_make",
        (["A"], [("n", Lang.Type.Int); ("v", Lang.Type.Var "A")],
         [`Assert (`App (("TLC.LibOrder.ge", [`Var ("n"); `Int (0)])))],
         `Eq ((Lang.Type.Int,
               `App (("TLC.LibListZ.length",
                      [`App (("TLC.LibListZ.make", [`Var ("n"); `Var ("v")]))])),
               `Var ("n")))));
       ("Hdata",
        ([], [], [],
         `Eq ((Lang.Type.List (Lang.Type.Var "A"), `Var ("data"),
               `App (("TLC.LibListZ.make", [`Var ("len"); `Var ("init")]))))))
      ];
    env =
      [("l", Lang.Type.List (Lang.Type.Var "A")); ("s", Lang.Type.Func None);
       ("v", Lang.Type.Loc); ("tmp", Lang.Type.Val);
       ("len", Lang.Type.Var "Coq.Numbers.BinNums.Z");
       ("ls", Lang.Type.List (Lang.Type.Var "A")); ("init", Lang.Type.Var "A");
       ("rest", Lang.Type.List (Lang.Type.Var "A"));
       ("a", Lang.Type.Array (Lang.Type.Var "A"));
       ("data", Lang.Type.List (Lang.Type.Var "A"));
       ("idx", Lang.Type.Var "Coq.Numbers.BinNums.Z"); ("tmp0", Lang.Type.Val)];
    assumptions =
      [(Lang.Type.List (Lang.Type.Var "A"), `Var ("ls"),
        `Constructor (("::", [`Var ("init"); `Var ("rest")])));
       (Lang.Type.Product ([Lang.Type.Int; Lang.Type.List (Lang.Type.Var "A")]),
        `Tuple ([`Var ("len");
                 `Constructor (("::", [`Var ("init"); `Var ("rest")]))]),
        `Tuple ([`App (("TLC.LibListZ.length", [`Var ("l")]));
                 `App (("TLC.LibList.rev", [`Var ("l")]))]));
       (Lang.Type.List (Lang.Type.Var "A"),
        `Constructor (("::", [`Var ("init"); `Var ("rest")])),
        `App (("TLC.LibList.rev", [`Var ("l")])));
       (Lang.Type.Int, `Var ("len"),
        `App (("TLC.LibListZ.length", [`Var ("l")])));
       (Lang.Type.List (Lang.Type.Var "A"), `Var ("data"),
        `App (("TLC.LibListZ.make", [`Var ("len"); `Var ("init")])));
       (Lang.Type.Int, `Var ("idx"), `App (("-", [`Var ("len"); `Int (2)])))];
    invariant = ("I", [Lang.Type.List (Lang.Type.Var "A"); Lang.Type.Int]);
    initial =
      { expr_values = [|`Var ("data")|];
        param_values = [`Constructor (("[]", [])); `Var ("idx")] };
    conditions =
      [{ qf =
           [("r", Lang.Type.List (Lang.Type.Var "A"));
            ("t", Lang.Type.List (Lang.Type.Var "A")); ("v", Lang.Type.Var "A");
            ("acc", Lang.Type.Int)];
         param_values = [`Var ("t"); `Var ("acc")];
         assumptions =
           [`Eq ((Lang.Type.List (Lang.Type.Var "A"), `Var ("rest"),
                  `App (("TLC.LibList.app",
                         [`Var ("t");
                          `Constructor (("::", [`Var ("v"); `Var ("r")]))]))))
           ];
         post_param_values =
           [`App (("TLC.LibList.app",
                   [`Var ("t");
                    `Constructor (("::", [`Var ("v"); `Constructor (("[]", []))]))
                   ]));
            `App (("-", [`Var ("acc"); `Int (1)]))];
         expr_values =
           [|fun exp -> `App (("Array.set",
                               [`App (("CFML.WPArray.Array", [exp])); `Var ("acc");
                                `Var ("v")]))
           |]
       }
      ]
  }

let () =
  let[@warning "-8"] target_pure [t;i] =
    `App ("=", [
      i;
      `App ("-", [
        `App ("-", [
          `App ("TLC.LibList.length", [`Var "l"]);
          `App ("TLC.LibList.length", [t])
        ]);
        `Int 2
      ])
    ]) in
  let[@warning "-8"] target_expr [t;i] = [|
    `App ("TLC.LibList.app", [
      `App ("TLC.LibList.make", [
        `App ("+", [i; `Int 1]);
        `Var "init"
      ]);
      `App ("TLC.LibList.rev", [
        `Constructor ("::", [
          `Var "init";
          t
        ])
      ])
    ])
  |] in

  let[@warning "-8"] invalid_target_expr [t;i] = [|
    `App ("TLC.LibList.app", [
      `App ("TLC.LibList.make", [
        `App ("+", [i; `Int 10]);
        `Var "init"
      ]);
      `App ("TLC.LibList.rev", [
        `Constructor ("::", [
          `Var "init";
          t
        ])
      ])
    ])
  |] in

  let validator = Proof_validator.build_validator data in

  Iter.int_range ~start:0 ~stop:10  begin fun i ->
    Format.printf "[%d] validating invalid expr: " i;
    begin 
      match validator (target_pure, invalid_target_expr) with
      | `InvalidPure -> print_endline "invalid pure"
      | `InvalidSpatial -> print_endline "invalid spatial"
      | `Valid -> print_endline "success"
    end;
  end;


  begin 
    match validator (target_pure, target_expr) with
    | `InvalidPure -> print_endline "invalid pure"
    | `InvalidSpatial -> print_endline "invalid spatial"
    | `Valid -> print_endline "success"
  end;
