open Containers

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

let split_last =
  let rec loop (acc, last) = function
    | [] -> List.rev acc, last
    | h :: t -> loop (last :: acc, h) t in
  function
  | [] -> None
  | h :: t -> Some (loop ([], h) t)

let normalize =
  let update s =
    if String.prefix ~pre:"TLC.LibListZ." s
    then Some ("TLC.LibList." ^ String.drop (String.length "TLC.LibListZ.") s)
    else None in
  let update_expr e = Lang.Expr.subst_functions update e in
  let update_assertion = function
      `Eq (ty, l, r) ->
      `Eq (ty, update_expr l, update_expr r)
    | `Assert prop -> `Assert (update_expr prop) in
  fun (data: Proof_validator.Verification_condition.verification_condition) ->
    let functions =
      data.functions
      |> List.fold_map (fun fns (name, sg) ->
        let name = Option.value ~default:name @@ update name in
        if StringSet.mem name fns
        then (fns, None)
        else
          let fns = StringSet.add name fns in
          (fns, Some (name, sg))
      ) StringSet.empty
      |> snd
      |> List.filter_map Fun.id in

    let properties =
      List.map (fun (pname, (qfs, params, assums, (ty, l, r))) ->
        let assums = List.map update_assertion assums in
        (pname, (qfs, params, assums, (ty, update_expr l, update_expr r)))) data.properties in
    let assumptions =
      List.map (fun (ty, l, r) -> (ty, update_expr l, update_expr r)) data.assumptions in

    let initial : Proof_validator.Verification_condition.initial_vc =  {
      expr_values=Array.map update_expr data.initial.expr_values;
      param_values=List.map update_expr data.initial.param_values;
    } in
    let conditions = List.map (fun (vc: Proof_validator.Verification_condition.vc) ->
      {vc
        with param_values=List.map update_expr vc.param_values;
             assumptions=List.map update_assertion vc.assumptions;
             post_param_values=List.map update_expr vc.post_param_values;
             expr_values=Array.map (fun f -> fun e -> update_expr (f e)) vc.expr_values;
      }
    ) data.conditions in
    {data with
     functions;
     properties;
     assumptions;
     initial;
     conditions=conditions;
    }
      

let data = Proof_validator.Verification_condition.{
  poly_vars = ["A"];
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
     (Lang.Type.List (Lang.Type.Var "A"), `Var ("xs"),
      `App (("TLC.LibList.app",
             [`App (("TLC.LibList.rev", [`Var ("r")]));
               `Constructor (("::",
                              [`Var ("v");
                                `App (("TLC.LibList.rev", [`Var ("l")]))]))
               ])))));
    ("CFML.Semantics.app_trms_vals_rev_cons",
     ([],
      [("v", Lang.Type.Val); ("vs", Lang.Type.List (Lang.Type.Val));
        ("ts", Lang.Type.List (Lang.Type.Val))],
      [],
      (Lang.Type.List (Lang.Type.Val),
       `App (("TLC.LibList.app",
              [`App (("TLC.LibList.rev",
                      [`Constructor (("::", [`Var ("v"); `Var ("vs")]))]));
                `Var ("ts")])),
       `App (("TLC.LibList.app",
              [`App (("TLC.LibList.rev", [`Var ("vs")]));
                `Constructor (("::", [`Var ("v"); `Var ("ts")]))])))));
    ("TLC.LibListZ.sum_app",
     ([],
      [("l1", Lang.Type.List (Lang.Type.Int));
        ("l2", Lang.Type.List (Lang.Type.Int))],
      [],
      (Lang.Type.Int,
       `App (("TLC.LibListZ.sum",
              [`App (("TLC.LibList.app", [`Var ("l1"); `Var ("l2")]))])),
       `App (("+",
              [`App (("TLC.LibListZ.sum", [`Var ("l1")]));
                `App (("TLC.LibListZ.sum", [`Var ("l2")]))])))));
    ("TLC.LibListZ.list_eq_take_app_drop",
     (["A"],
      [("n", Lang.Type.Int); ("l", Lang.Type.List (Lang.Type.Var "A"))],
      [`Assert (`App (("TLC.LibOrder.le",
                       [`Var ("n");
                         `App (("TLC.LibListZ.length", [`Var ("l")]))])))
        ],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibList.app",
              [`App (("TLC.LibListZ.take", [`Var ("n"); `Var ("l")]));
                `App (("TLC.LibListZ.drop", [`Var ("n"); `Var ("l")]))])),
       `Var ("l"))));
    ("TLC.LibListZ.drop_app_length",
     (["A"],
      [("l", Lang.Type.List (Lang.Type.Var "A"));
        ("l'", Lang.Type.List (Lang.Type.Var "A"))],
      [],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibListZ.drop",
              [`App (("TLC.LibListZ.length", [`Var ("l")]));
                `App (("TLC.LibList.app", [`Var ("l"); `Var ("l'")]))])),
       `Var ("l'"))));
    ("TLC.LibListZ.drop_app_r",
     (["A"],
      [("n", Lang.Type.Int); ("l", Lang.Type.List (Lang.Type.Var "A"));
        ("l'", Lang.Type.List (Lang.Type.Var "A"))],
      [`Assert (`App (("TLC.LibOrder.ge",
                       [`Var ("n");
                         `App (("TLC.LibListZ.length", [`Var ("l")]))])))
        ],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibListZ.drop",
              [`Var ("n");
                `App (("TLC.LibList.app", [`Var ("l"); `Var ("l'")]))])),
       `App (("TLC.LibListZ.drop",
              [`App (("-",
                      [`Var ("n");
                        `App (("TLC.LibListZ.length", [`Var ("l")]))]));
                `Var ("l'")])))));
    ("TLC.LibListZ.drop_app_l",
     (["A"],
      [("n", Lang.Type.Int); ("l", Lang.Type.List (Lang.Type.Var "A"));
        ("l'", Lang.Type.List (Lang.Type.Var "A"))],
      [`Assert (`App (("TLC.LibOrder.le",
                       [`Var ("n");
                         `App (("TLC.LibListZ.length", [`Var ("l")]))])))
        ],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibListZ.drop",
              [`Var ("n");
                `App (("TLC.LibList.app", [`Var ("l"); `Var ("l'")]))])),
       `App (("TLC.LibList.app",
              [`App (("TLC.LibListZ.drop", [`Var ("n"); `Var ("l")]));
                `Var ("l'")])))));
    ("TLC.LibListZ.take_prefix_length",
     (["A"],
      [("l", Lang.Type.List (Lang.Type.Var "A"));
        ("l'", Lang.Type.List (Lang.Type.Var "A"))],
      [],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibListZ.take",
              [`App (("TLC.LibListZ.length", [`Var ("l")]));
                `App (("TLC.LibList.app", [`Var ("l"); `Var ("l'")]))])),
       `Var ("l"))));
    ("TLC.LibListZ.take_app_r",
     (["A"],
      [("n", Lang.Type.Int); ("l", Lang.Type.List (Lang.Type.Var "A"));
        ("l'", Lang.Type.List (Lang.Type.Var "A"))],
      [`Assert (`App (("TLC.LibOrder.ge",
                       [`Var ("n");
                         `App (("TLC.LibListZ.length", [`Var ("l")]))])))
        ],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibListZ.take",
              [`Var ("n");
                `App (("TLC.LibList.app", [`Var ("l"); `Var ("l'")]))])),
       `App (("TLC.LibList.app",
              [`Var ("l");
                `App (("TLC.LibListZ.take",
                       [`App (("-",
                               [`Var ("n");
                                 `App (("TLC.LibListZ.length", [`Var ("l")]))
                                 ]));
                         `Var ("l'")]))
                ])))));
    ("TLC.LibListZ.take_app_l",
     (["A"],
      [("n", Lang.Type.Int); ("l", Lang.Type.List (Lang.Type.Var "A"));
        ("l'", Lang.Type.List (Lang.Type.Var "A"))],
      [`Assert (`App (("TLC.LibOrder.le",
                       [`Var ("n");
                         `App (("TLC.LibListZ.length", [`Var ("l")]))])))
        ],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibListZ.take",
              [`Var ("n");
                `App (("TLC.LibList.app", [`Var ("l"); `Var ("l'")]))])),
       `App (("TLC.LibListZ.take", [`Var ("n"); `Var ("l")])))));
    ("TLC.LibListZ.make_succ_r",
     (["A"], [("n", Lang.Type.Int); ("v", Lang.Type.Var "A")],
      [`Assert (`App (("TLC.LibOrder.ge", [`Var ("n"); `Int (0)])))],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibListZ.make",
              [`App (("+", [`Var ("n"); `Int (1)])); `Var ("v")])),
       `App (("TLC.LibList.app",
              [`App (("TLC.LibListZ.make", [`Var ("n"); `Var ("v")]));
                `Constructor (("::", [`Var ("v"); `Constructor (("[]", []))]))
                ])))));
    ("TLC.LibListZ.update_middle",
     (["A"],
      [("i", Lang.Type.Int); ("l1", Lang.Type.List (Lang.Type.Var "A"));
        ("l2", Lang.Type.List (Lang.Type.Var "A")); ("v", Lang.Type.Var "A");
        ("w", Lang.Type.Var "A")],
      [`Eq ((Lang.Type.Int, `Var ("i"),
             `App (("TLC.LibListZ.length", [`Var ("l1")]))))
        ],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibContainer.update",
              [`App (("TLC.LibList.app",
                      [`Var ("l1");
                        `Constructor (("::", [`Var ("w"); `Var ("l2")]))]));
                `Var ("i"); `Var ("v")])),
       `App (("TLC.LibList.app",
              [`App (("TLC.LibList.app",
                      [`Var ("l1");
                        `Constructor (("::",
                                       [`Var ("v"); `Constructor (("[]", []))
                                         ]))
                        ]));
                `Var ("l2")])))));
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
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibContainer.update",
              [`App (("TLC.LibList.app", [`Var ("l1"); `Var ("l2")]));
                `Var ("ij"); `Var ("v")])),
       `App (("TLC.LibList.app",
              [`Var ("l1");
                `App (("TLC.LibContainer.update",
                       [`Var ("l2"); `Var ("j"); `Var ("v")]))
                ])))));
    ("TLC.LibListZ.length_last",
     (["A"],
      [("x", Lang.Type.Var "A"); ("l", Lang.Type.List (Lang.Type.Var "A"))],
      [],
      (Lang.Type.Int,
       `App (("TLC.LibListZ.length",
              [`App (("TLC.LibList.app",
                      [`Var ("l");
                        `Constructor (("::",
                                       [`Var ("x"); `Constructor (("[]", []))
                                         ]))
                        ]))
                ])),
       `App (("+", [`Int (1); `App (("TLC.LibListZ.length", [`Var ("l")]))])))));
    ("TLC.LibListZ.length_app",
     (["A"],
      [("l1", Lang.Type.List (Lang.Type.Var "A"));
        ("l2", Lang.Type.List (Lang.Type.Var "A"))],
      [],
      (Lang.Type.Int,
       `App (("TLC.LibListZ.length",
              [`App (("TLC.LibList.app", [`Var ("l1"); `Var ("l2")]))])),
       `App (("+",
              [`App (("TLC.LibListZ.length", [`Var ("l1")]));
                `App (("TLC.LibListZ.length", [`Var ("l2")]))])))));
    ("TLC.LibList.list_eq_take_app_drop",
     (["A"],
      [("n", Lang.Type.Int); ("l", Lang.Type.List (Lang.Type.Var "A"))],
      [`Assert (`App (("TLC.LibOrder.le",
                       [`Var ("n");
                         `App (("TLC.LibList.length", [`Var ("l")]))])))
        ],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibList.app",
              [`App (("TLC.LibList.take", [`Var ("n"); `Var ("l")]));
                `App (("TLC.LibList.drop", [`Var ("n"); `Var ("l")]))])),
       `Var ("l"))));
    ("TLC.LibList.drop_app_length",
     (["A"],
      [("l", Lang.Type.List (Lang.Type.Var "A"));
        ("l'", Lang.Type.List (Lang.Type.Var "A"))],
      [],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibList.drop",
              [`App (("TLC.LibList.length", [`Var ("l")]));
                `App (("TLC.LibList.app", [`Var ("l"); `Var ("l'")]))])),
       `Var ("l'"))));
    ("TLC.LibList.drop_app_r",
     (["A"],
      [("n", Lang.Type.Int); ("l", Lang.Type.List (Lang.Type.Var "A"));
        ("l'", Lang.Type.List (Lang.Type.Var "A"))],
      [`Assert (`App (("TLC.LibOrder.ge",
                       [`Var ("n");
                         `App (("TLC.LibList.length", [`Var ("l")]))])))
        ],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibList.drop",
              [`Var ("n");
                `App (("TLC.LibList.app", [`Var ("l"); `Var ("l'")]))])),
       `App (("TLC.LibList.drop",
              [`App (("Coq.Init.Nat.sub",
                      [`Var ("n");
                        `App (("TLC.LibList.length", [`Var ("l")]))]));
                `Var ("l'")])))));
    ("TLC.LibList.drop_app_l",
     (["A"],
      [("n", Lang.Type.Int); ("l", Lang.Type.List (Lang.Type.Var "A"));
        ("l'", Lang.Type.List (Lang.Type.Var "A"))],
      [`Assert (`App (("TLC.LibOrder.le",
                       [`Var ("n");
                         `App (("TLC.LibList.length", [`Var ("l")]))])))
        ],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibList.drop",
              [`Var ("n");
                `App (("TLC.LibList.app", [`Var ("l"); `Var ("l'")]))])),
       `App (("TLC.LibList.app",
              [`App (("TLC.LibList.drop", [`Var ("n"); `Var ("l")]));
                `Var ("l'")])))));
    ("TLC.LibList.take_prefix_length",
     (["A"],
      [("l", Lang.Type.List (Lang.Type.Var "A"));
        ("l'", Lang.Type.List (Lang.Type.Var "A"))],
      [],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibList.take",
              [`App (("TLC.LibList.length", [`Var ("l")]));
                `App (("TLC.LibList.app", [`Var ("l"); `Var ("l'")]))])),
       `Var ("l"))));
    ("TLC.LibList.take_app_r",
     (["A"],
      [("n", Lang.Type.Int); ("l", Lang.Type.List (Lang.Type.Var "A"));
        ("l'", Lang.Type.List (Lang.Type.Var "A"))],
      [`Assert (`App (("TLC.LibOrder.ge",
                       [`Var ("n");
                         `App (("TLC.LibList.length", [`Var ("l")]))])))
        ],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibList.take",
              [`Var ("n");
                `App (("TLC.LibList.app", [`Var ("l"); `Var ("l'")]))])),
       `App (("TLC.LibList.app",
              [`Var ("l");
                `App (("TLC.LibList.take",
                       [`App (("Coq.Init.Nat.sub",
                               [`Var ("n");
                                 `App (("TLC.LibList.length", [`Var ("l")]))]));
                         `Var ("l'")]))
                ])))));
    ("TLC.LibList.take_app_l",
     (["A"],
      [("n", Lang.Type.Int); ("l", Lang.Type.List (Lang.Type.Var "A"));
        ("l'", Lang.Type.List (Lang.Type.Var "A"))],
      [`Assert (`App (("TLC.LibOrder.le",
                       [`Var ("n");
                         `App (("TLC.LibList.length", [`Var ("l")]))])))
        ],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibList.take",
              [`Var ("n");
                `App (("TLC.LibList.app", [`Var ("l"); `Var ("l'")]))])),
       `App (("TLC.LibList.take", [`Var ("n"); `Var ("l")])))));
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
      (Lang.Type.Product ([Lang.Type.List (Lang.Type.Var "A"); Lang.Type.List (Lang.Type.Var "B")]),
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
                 ]))));
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
      (Lang.Type.Product ([Lang.Type.List (Lang.Type.Var "A"); Lang.Type.List (Lang.Type.Var "B")]),
       `App (("TLC.LibList.split",
              [`App (("TLC.LibList.app", [`Var ("l1"); `Var ("l2")]))])),
       `Tuple ([`App (("TLC.LibList.app", [`Var ("r1"); `Var ("r2")]));
                 `App (("TLC.LibList.app", [`Var ("s1"); `Var ("s2")]))]))));
    ("TLC.LibList.combine_last",
     (["A"; "B"],
      [("x", Lang.Type.Var "A"); ("r", Lang.Type.List (Lang.Type.Var "A"));
        ("y", Lang.Type.Var "B"); ("s", Lang.Type.List (Lang.Type.Var "B"))],
      [`Eq ((Lang.Type.Int, `App (("TLC.LibList.length", [`Var ("r")])),
             `App (("TLC.LibList.length", [`Var ("s")]))))
        ],
      (Lang.Type.List (Lang.Type.Product ([Lang.Type.Var "A"; Lang.Type.Var "B"])),
       `App (("TLC.LibList.combine",
              [`App (("TLC.LibList.app",
                      [`Var ("r");
                        `Constructor (("::",
                                       [`Var ("x"); `Constructor (("[]", []))
                                         ]))
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
                ])))));
    ("TLC.LibList.combine_app",
     (["A"; "B"],
      [("r1", Lang.Type.List (Lang.Type.Var "A"));
        ("r2", Lang.Type.List (Lang.Type.Var "A"));
        ("s1", Lang.Type.List (Lang.Type.Var "B"));
        ("s2", Lang.Type.List (Lang.Type.Var "B"))],
      [`Eq ((Lang.Type.Int, `App (("TLC.LibList.length", [`Var ("r1")])),
             `App (("TLC.LibList.length", [`Var ("s1")]))))
        ],
      (Lang.Type.List (Lang.Type.Product ([Lang.Type.Var "A"; Lang.Type.Var "B"])),
       `App (("TLC.LibList.combine",
              [`App (("TLC.LibList.app", [`Var ("r1"); `Var ("r2")]));
                `App (("TLC.LibList.app", [`Var ("s1"); `Var ("s2")]))])),
       `App (("TLC.LibList.app",
              [`App (("TLC.LibList.combine", [`Var ("r1"); `Var ("s1")]));
                `App (("TLC.LibList.combine", [`Var ("r2"); `Var ("s2")]))])))));
    ("TLC.LibList.concat_last",
     (["A"],
      [("l", Lang.Type.List (Lang.Type.Var "A"));
        ("m", Lang.Type.List (Lang.Type.List (Lang.Type.Var "A")))],
      [],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibList.concat",
              [`App (("TLC.LibList.app",
                      [`Var ("m");
                        `Constructor (("::",
                                       [`Var ("l"); `Constructor (("[]", []))
                                         ]))
                        ]))
                ])),
       `App (("TLC.LibList.app",
              [`App (("TLC.LibList.concat", [`Var ("m")])); `Var ("l")])))));
    ("TLC.LibList.concat_app",
     (["A"],
      [("m1", Lang.Type.List (Lang.Type.List (Lang.Type.Var "A")));
        ("m2", Lang.Type.List (Lang.Type.List (Lang.Type.Var "A")))],
      [],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibList.concat",
              [`App (("TLC.LibList.app", [`Var ("m1"); `Var ("m2")]))])),
       `App (("TLC.LibList.app",
              [`App (("TLC.LibList.concat", [`Var ("m1")]));
                `App (("TLC.LibList.concat", [`Var ("m2")]))])))));
    ("TLC.LibList.concat_cons",
     (["A"],
      [("l", Lang.Type.List (Lang.Type.Var "A"));
        ("m", Lang.Type.List (Lang.Type.List (Lang.Type.Var "A")))],
      [],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibList.concat",
              [`Constructor (("::", [`Var ("l"); `Var ("m")]))])),
       `App (("TLC.LibList.app",
              [`Var ("l"); `App (("TLC.LibList.concat", [`Var ("m")]))])))));
    ("TLC.LibList.rev_last",
     (["A"],
      [("x", Lang.Type.Var "A"); ("l", Lang.Type.List (Lang.Type.Var "A"))],
      [],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibList.rev",
              [`App (("TLC.LibList.app",
                      [`Var ("l");
                        `Constructor (("::",
                                       [`Var ("x"); `Constructor (("[]", []))
                                         ]))
                        ]))
                ])),
       `Constructor (("::",
                      [`Var ("x"); `App (("TLC.LibList.rev", [`Var ("l")]))])))));
    ("TLC.LibList.rev_cons",
     (["A"],
      [("x", Lang.Type.Var "A"); ("l", Lang.Type.List (Lang.Type.Var "A"))],
      [],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibList.rev",
              [`Constructor (("::", [`Var ("x"); `Var ("l")]))])),
       `App (("TLC.LibList.app",
              [`App (("TLC.LibList.rev", [`Var ("l")]));
                `Constructor (("::", [`Var ("x"); `Constructor (("[]", []))]))
                ])))));
    ("TLC.LibList.rev_app",
     (["A"],
      [("l1", Lang.Type.List (Lang.Type.Var "A"));
        ("l2", Lang.Type.List (Lang.Type.Var "A"))],
      [],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibList.rev",
              [`App (("TLC.LibList.app", [`Var ("l1"); `Var ("l2")]))])),
       `App (("TLC.LibList.app",
              [`App (("TLC.LibList.rev", [`Var ("l2")]));
                `App (("TLC.LibList.rev", [`Var ("l1")]))])))));
    ("TLC.LibList.length_app",
     (["A"],
      [("l1", Lang.Type.List (Lang.Type.Var "A"));
        ("l2", Lang.Type.List (Lang.Type.Var "A"))],
      [],
      (Lang.Type.Int,
       `App (("TLC.LibList.length",
              [`App (("TLC.LibList.app", [`Var ("l1"); `Var ("l2")]))])),
       `App (("Coq.Init.Nat.add",
              [`App (("TLC.LibList.length", [`Var ("l1")]));
                `App (("TLC.LibList.length", [`Var ("l2")]))])))));
    ("TLC.LibList.last_app",
     (["A"],
      [("x", Lang.Type.Var "A"); ("l1", Lang.Type.List (Lang.Type.Var "A"));
        ("l2", Lang.Type.List (Lang.Type.Var "A"))],
      [],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibList.app",
              [`App (("TLC.LibList.app", [`Var ("l1"); `Var ("l2")]));
                `Constructor (("::", [`Var ("x"); `Constructor (("[]", []))]))
                ])),
       `App (("TLC.LibList.app",
              [`Var ("l1");
                `App (("TLC.LibList.app",
                       [`Var ("l2");
                         `Constructor (("::",
                                        [`Var ("x");
                                          `Constructor (("[]", []))]))
                         ]))
                ])))));
    ("TLC.LibList.last_one",
     (["A"], [("x", Lang.Type.Var "A"); ("y", Lang.Type.Var "A")], [],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibList.app",
              [`Constructor (("::", [`Var ("x"); `Constructor (("[]", []))]));
                `Constructor (("::", [`Var ("y"); `Constructor (("[]", []))]))
                ])),
       `Constructor (("::",
                      [`Var ("x");
                        `Constructor (("::",
                                       [`Var ("y"); `Constructor (("[]", []))
                                         ]))
                        ])))));
    ("TLC.LibList.last_cons",
     (["A"],
      [("x", Lang.Type.Var "A"); ("y", Lang.Type.Var "A");
        ("l", Lang.Type.List (Lang.Type.Var "A"))],
      [],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibList.app",
              [`Constructor (("::", [`Var ("x"); `Var ("l")]));
                `Constructor (("::", [`Var ("y"); `Constructor (("[]", []))]))
                ])),
       `Constructor (("::",
                      [`Var ("x");
                        `App (("TLC.LibList.app",
                               [`Var ("l");
                                 `Constructor (("::",
                                                [`Var ("y");
                                                  `Constructor (("[]", []))]))
                                 ]))
                        ])))));
    ("TLC.LibList.last_nil",
     (["A"], [("x", Lang.Type.Var "A")], [],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibList.app",
              [`Constructor (("[]", []));
                `Constructor (("::", [`Var ("x"); `Constructor (("[]", []))]))
                ])),
       `Constructor (("::", [`Var ("x"); `Constructor (("[]", []))])))));
    ("TLC.LibList.app_last_r",
     (["A"],
      [("x", Lang.Type.Var "A"); ("l1", Lang.Type.List (Lang.Type.Var "A"));
        ("l2", Lang.Type.List (Lang.Type.Var "A"))],
      [],
      (Lang.Type.List (Lang.Type.Var "A"),
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
                `Constructor (("::", [`Var ("x"); `Constructor (("[]", []))]))
                ])))));
    ("TLC.LibList.app_last_l",
     (["A"],
      [("x", Lang.Type.Var "A"); ("l1", Lang.Type.List (Lang.Type.Var "A"));
        ("l2", Lang.Type.List (Lang.Type.Var "A"))],
      [],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibList.app",
              [`App (("TLC.LibList.app",
                      [`Var ("l1");
                        `Constructor (("::",
                                       [`Var ("x"); `Constructor (("[]", []))
                                         ]))
                        ]));
                `Var ("l2")])),
       `App (("TLC.LibList.app",
              [`Var ("l1"); `Constructor (("::", [`Var ("x"); `Var ("l2")]))])))));
    ("TLC.LibList.app_cons_one_l",
     (["A"],
      [("x", Lang.Type.Var "A"); ("l", Lang.Type.List (Lang.Type.Var "A"))],
      [],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibList.app",
              [`Var ("l");
                `Constructor (("::", [`Var ("x"); `Constructor (("[]", []))]))
                ])),
       `App (("TLC.LibList.app",
              [`Var ("l");
                `Constructor (("::", [`Var ("x"); `Constructor (("[]", []))]))
                ])))));
    ("TLC.LibList.app_cons_one_r",
     (["A"],
      [("x", Lang.Type.Var "A"); ("l", Lang.Type.List (Lang.Type.Var "A"))],
      [],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibList.app",
              [`Constructor (("::", [`Var ("x"); `Constructor (("[]", []))]));
                `Var ("l")])),
       `Constructor (("::", [`Var ("x"); `Var ("l")])))));
    ("TLC.LibList.app_cons_r",
     (["A"],
      [("x", Lang.Type.Var "A"); ("l1", Lang.Type.List (Lang.Type.Var "A"));
        ("l2", Lang.Type.List (Lang.Type.Var "A"))],
      [],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibList.app",
              [`Var ("l1"); `Constructor (("::", [`Var ("x"); `Var ("l2")]))])),
       `App (("TLC.LibList.app",
              [`App (("TLC.LibList.app",
                      [`Var ("l1");
                        `Constructor (("::",
                                       [`Var ("x"); `Constructor (("[]", []))
                                         ]))
                        ]));
                `Var ("l2")])))));
    ("TLC.LibList.app_assoc",
     (["A"],
      [("l1", Lang.Type.List (Lang.Type.Var "A"));
        ("l2", Lang.Type.List (Lang.Type.Var "A"));
        ("l3", Lang.Type.List (Lang.Type.Var "A"))],
      [],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibList.app",
              [`App (("TLC.LibList.app", [`Var ("l1"); `Var ("l2")]));
                `Var ("l3")])),
       `App (("TLC.LibList.app",
              [`Var ("l1");
                `App (("TLC.LibList.app", [`Var ("l2"); `Var ("l3")]))])))));
    ("TLC.LibList.app_nil_r",
     (["A"], [("l", Lang.Type.List (Lang.Type.Var "A"))], [],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibList.app", [`Var ("l"); `Constructor (("[]", []))])),
       `Var ("l"))));
    ("TLC.LibList.app_nil_l",
     (["A"], [("l", Lang.Type.List (Lang.Type.Var "A"))], [],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibList.app", [`Constructor (("[]", [])); `Var ("l")])),
       `Var ("l"))));
    ("TLC.LibList.app_cons_l",
     (["A"],
      [("x", Lang.Type.Var "A"); ("l1", Lang.Type.List (Lang.Type.Var "A"));
        ("l2", Lang.Type.List (Lang.Type.Var "A"))],
      [],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibList.app",
              [`Constructor (("::", [`Var ("x"); `Var ("l1")])); `Var ("l2")])),
       `Constructor (("::",
                      [`Var ("x");
                        `App (("TLC.LibList.app", [`Var ("l1"); `Var ("l2")]))
                        ])))));
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
      (Lang.Type.List (Lang.Type.Var "A"), `Var ("xs"),
       `App (("TLC.LibList.app",
              [`App (("TLC.LibList.rev", [`Var ("r")]));
                `Constructor (("::",
                               [`Var ("v");
                                 `App (("TLC.LibList.rev", [`Var ("l")]))]))
                ])))));
    ("CFML.Semantics.app_trms_vals_rev_cons",
     ([],
      [("v", Lang.Type.Val); ("vs", Lang.Type.List (Lang.Type.Val));
        ("ts", Lang.Type.List (Lang.Type.Val))],
      [],
      (Lang.Type.List (Lang.Type.Val),
       `App (("TLC.LibList.app",
              [`App (("TLC.LibList.rev",
                      [`Constructor (("::", [`Var ("v"); `Var ("vs")]))]));
                `Var ("ts")])),
       `App (("TLC.LibList.app",
              [`App (("TLC.LibList.rev", [`Var ("vs")]));
                `Constructor (("::", [`Var ("v"); `Var ("ts")]))])))));
    ("TLC.LibListZ.length_rev",
     (["A"], [("l", Lang.Type.List (Lang.Type.Var "A"))], [],
      (Lang.Type.Int,
       `App (("TLC.LibListZ.length",
              [`App (("TLC.LibList.rev", [`Var ("l")]))])),
       `App (("TLC.LibListZ.length", [`Var ("l")])))));
    ("TLC.LibList.combine_rev",
     (["A"; "B"],
      [("r", Lang.Type.List (Lang.Type.Var "A"));
        ("s", Lang.Type.List (Lang.Type.Var "B"))],
      [`Eq ((Lang.Type.Int, `App (("TLC.LibList.length", [`Var ("r")])),
             `App (("TLC.LibList.length", [`Var ("s")]))))
        ],
      (Lang.Type.List (Lang.Type.Product ([Lang.Type.Var "A"; Lang.Type.Var "B"])),
       `App (("TLC.LibList.combine",
              [`App (("TLC.LibList.rev", [`Var ("r")]));
                `App (("TLC.LibList.rev", [`Var ("s")]))])),
       `App (("TLC.LibList.rev",
              [`App (("TLC.LibList.combine", [`Var ("r"); `Var ("s")]))])))));
    ("TLC.LibList.length_rev",
     (["A"], [("l", Lang.Type.List (Lang.Type.Var "A"))], [],
      (Lang.Type.Int,
       `App (("TLC.LibList.length",
              [`App (("TLC.LibList.rev", [`Var ("l")]))])),
       `App (("TLC.LibList.length", [`Var ("l")])))));
    ("TLC.LibList.rev_rev",
     (["A"], [("l", Lang.Type.List (Lang.Type.Var "A"))], [],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibList.rev", [`App (("TLC.LibList.rev", [`Var ("l")]))])),
       `Var ("l"))));
    ("TLC.LibList.rev_last",
     (["A"],
      [("x", Lang.Type.Var "A"); ("l", Lang.Type.List (Lang.Type.Var "A"))],
      [],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibList.rev",
              [`App (("TLC.LibList.app",
                      [`Var ("l");
                        `Constructor (("::",
                                       [`Var ("x"); `Constructor (("[]", []))
                                         ]))
                        ]))
                ])),
       `Constructor (("::",
                      [`Var ("x"); `App (("TLC.LibList.rev", [`Var ("l")]))])))));
    ("TLC.LibList.rev_one",
     (["A"], [("x", Lang.Type.Var "A")], [],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibList.rev",
              [`Constructor (("::", [`Var ("x"); `Constructor (("[]", []))]))
                ])),
       `Constructor (("::", [`Var ("x"); `Constructor (("[]", []))])))));
    ("TLC.LibList.rev_cons",
     (["A"],
      [("x", Lang.Type.Var "A"); ("l", Lang.Type.List (Lang.Type.Var "A"))],
      [],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibList.rev",
              [`Constructor (("::", [`Var ("x"); `Var ("l")]))])),
       `App (("TLC.LibList.app",
              [`App (("TLC.LibList.rev", [`Var ("l")]));
                `Constructor (("::", [`Var ("x"); `Constructor (("[]", []))]))
                ])))));
    ("TLC.LibList.rev_app",
     (["A"],
      [("l1", Lang.Type.List (Lang.Type.Var "A"));
        ("l2", Lang.Type.List (Lang.Type.Var "A"))],
      [],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibList.rev",
              [`App (("TLC.LibList.app", [`Var ("l1"); `Var ("l2")]))])),
       `App (("TLC.LibList.app",
              [`App (("TLC.LibList.rev", [`Var ("l2")]));
                `App (("TLC.LibList.rev", [`Var ("l1")]))])))));
    ("Proofs.Verify_seq_to_array_utils.drop_last",
     (["A"],
      [("xs", Lang.Type.List (Lang.Type.Var "A"));
        ("rst", Lang.Type.List (Lang.Type.Var "A"));
        ("lst", Lang.Type.Var "A")],
      [`Eq ((Lang.Type.List (Lang.Type.Var "A"),
             `App (("TLC.LibList.rev", [`Var ("xs")])),
             `Constructor (("::", [`Var ("lst"); `Var ("rst")]))))
        ],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibListZ.drop",
              [`App (("-",
                      [`App (("TLC.LibListZ.length", [`Var ("xs")]));
                        `Int (1)]));
                `Var ("xs")])),
       `Constructor (("::", [`Var ("lst"); `Constructor (("[]", []))])))));
    ("TLC.LibListZ.length_drop",
     (["A"],
      [("n", Lang.Type.Int); ("l", Lang.Type.List (Lang.Type.Var "A"))],
      [`Assert (`App (("TLC.LibOrder.le",
                       [`Var ("n");
                         `App (("TLC.LibListZ.length", [`Var ("l")]))])))
        ],
      (Lang.Type.Int,
       `App (("TLC.LibListZ.length",
              [`App (("TLC.LibListZ.drop", [`Var ("n"); `Var ("l")]))])),
       `App (("Coq.ZArith.BinInt.Z.min",
              [`App (("TLC.LibListZ.length", [`Var ("l")]));
                `App (("-",
                       [`App (("TLC.LibListZ.length", [`Var ("l")]));
                         `Var ("n")]))
                ])))));
    ("TLC.LibListZ.length_take",
     (["A"],
      [("n", Lang.Type.Int); ("l", Lang.Type.List (Lang.Type.Var "A"))],
      [`Assert (`App (("TLC.LibOrder.le",
                       [`Var ("n");
                         `App (("TLC.LibListZ.length", [`Var ("l")]))])))
        ],
      (Lang.Type.Int,
       `App (("TLC.LibListZ.length",
              [`App (("TLC.LibListZ.take", [`Var ("n"); `Var ("l")]))])),
       `App (("Coq.ZArith.BinInt.Z.max", [`Int (0); `Var ("n")])))));
    ("TLC.LibListZ.drop_at_length",
     (["A"], [("l", Lang.Type.List (Lang.Type.Var "A"))], [],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibListZ.drop",
              [`App (("TLC.LibListZ.length", [`Var ("l")])); `Var ("l")])),
       `Constructor (("[]", [])))));
    ("TLC.LibListZ.drop_app_length",
     (["A"],
      [("l", Lang.Type.List (Lang.Type.Var "A"));
        ("l'", Lang.Type.List (Lang.Type.Var "A"))],
      [],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibListZ.drop",
              [`App (("TLC.LibListZ.length", [`Var ("l")]));
                `App (("TLC.LibList.app", [`Var ("l"); `Var ("l'")]))])),
       `Var ("l'"))));
    ("TLC.LibListZ.drop_app_r",
     (["A"],
      [("n", Lang.Type.Int); ("l", Lang.Type.List (Lang.Type.Var "A"));
        ("l'", Lang.Type.List (Lang.Type.Var "A"))],
      [`Assert (`App (("TLC.LibOrder.ge",
                       [`Var ("n");
                         `App (("TLC.LibListZ.length", [`Var ("l")]))])))
        ],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibListZ.drop",
              [`Var ("n");
                `App (("TLC.LibList.app", [`Var ("l"); `Var ("l'")]))])),
       `App (("TLC.LibListZ.drop",
              [`App (("-",
                      [`Var ("n");
                        `App (("TLC.LibListZ.length", [`Var ("l")]))]));
                `Var ("l'")])))));
    ("TLC.LibListZ.take_full_length",
     (["A"], [("l", Lang.Type.List (Lang.Type.Var "A"))], [],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibListZ.take",
              [`App (("TLC.LibListZ.length", [`Var ("l")])); `Var ("l")])),
       `Var ("l"))));
    ("TLC.LibListZ.take_prefix_length",
     (["A"],
      [("l", Lang.Type.List (Lang.Type.Var "A"));
        ("l'", Lang.Type.List (Lang.Type.Var "A"))],
      [],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibListZ.take",
              [`App (("TLC.LibListZ.length", [`Var ("l")]));
                `App (("TLC.LibList.app", [`Var ("l"); `Var ("l'")]))])),
       `Var ("l"))));
    ("TLC.LibListZ.take_app_r",
     (["A"],
      [("n", Lang.Type.Int); ("l", Lang.Type.List (Lang.Type.Var "A"));
        ("l'", Lang.Type.List (Lang.Type.Var "A"))],
      [`Assert (`App (("TLC.LibOrder.ge",
                       [`Var ("n");
                         `App (("TLC.LibListZ.length", [`Var ("l")]))])))
        ],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibListZ.take",
              [`Var ("n");
                `App (("TLC.LibList.app", [`Var ("l"); `Var ("l'")]))])),
       `App (("TLC.LibList.app",
              [`Var ("l");
                `App (("TLC.LibListZ.take",
                       [`App (("-",
                               [`Var ("n");
                                 `App (("TLC.LibListZ.length", [`Var ("l")]))
                                 ]));
                         `Var ("l'")]))
                ])))));
    ("TLC.LibListZ.length_rev",
     (["A"], [("l", Lang.Type.List (Lang.Type.Var "A"))], [],
      (Lang.Type.Int,
       `App (("TLC.LibListZ.length",
              [`App (("TLC.LibList.rev", [`Var ("l")]))])),
       `App (("TLC.LibListZ.length", [`Var ("l")])))));
    ("TLC.LibListZ.length_make",
     (["A"], [("n", Lang.Type.Int); ("v", Lang.Type.Var "A")],
      [`Assert (`App (("TLC.LibOrder.ge", [`Var ("n"); `Int (0)])))],
      (Lang.Type.Int,
       `App (("TLC.LibListZ.length",
              [`App (("TLC.LibListZ.make", [`Var ("n"); `Var ("v")]))])),
       `Var ("n"))));
    ("TLC.LibListZ.length_update",
     (["A"],
      [("l", Lang.Type.List (Lang.Type.Var "A")); ("i", Lang.Type.Int);
        ("v", Lang.Type.Var "A")],
      [],
      (Lang.Type.Int,
       `App (("TLC.LibListZ.length",
              [`App (("TLC.LibContainer.update",
                      [`Var ("l"); `Var ("i"); `Var ("v")]))
                ])),
       `App (("TLC.LibListZ.length", [`Var ("l")])))));
    ("TLC.LibListZ.length_last",
     (["A"],
      [("x", Lang.Type.Var "A"); ("l", Lang.Type.List (Lang.Type.Var "A"))],
      [],
      (Lang.Type.Int,
       `App (("TLC.LibListZ.length",
              [`App (("TLC.LibList.app",
                      [`Var ("l");
                        `Constructor (("::",
                                       [`Var ("x"); `Constructor (("[]", []))
                                         ]))
                        ]))
                ])),
       `App (("+", [`Int (1); `App (("TLC.LibListZ.length", [`Var ("l")]))])))));
    ("TLC.LibListZ.length_app",
     (["A"],
      [("l1", Lang.Type.List (Lang.Type.Var "A"));
        ("l2", Lang.Type.List (Lang.Type.Var "A"))],
      [],
      (Lang.Type.Int,
       `App (("TLC.LibListZ.length",
              [`App (("TLC.LibList.app", [`Var ("l1"); `Var ("l2")]))])),
       `App (("+",
              [`App (("TLC.LibListZ.length", [`Var ("l1")]));
                `App (("TLC.LibListZ.length", [`Var ("l2")]))])))));
    ("TLC.LibListZ.length_one",
     (["A"], [("x", Lang.Type.Var "A")], [],
      (Lang.Type.Int,
       `App (("TLC.LibListZ.length",
              [`Constructor (("::", [`Var ("x"); `Constructor (("[]", []))]))
                ])),
       `Int (1))));
    ("TLC.LibListZ.length_cons",
     (["A"],
      [("x", Lang.Type.Var "A"); ("l", Lang.Type.List (Lang.Type.Var "A"))],
      [],
      (Lang.Type.Int,
       `App (("TLC.LibListZ.length",
              [`Constructor (("::", [`Var ("x"); `Var ("l")]))])),
       `App (("+", [`Int (1); `App (("TLC.LibListZ.length", [`Var ("l")]))])))));
    ("TLC.LibListZ.length_eq",
     (["A"], [("l", Lang.Type.List (Lang.Type.Var "A"))], [],
      (Lang.Type.Int, `App (("TLC.LibListZ.length", [`Var ("l")])),
       `App (("TLC.LibInt.nat_to_Z",
              [`App (("TLC.LibList.length", [`Var ("l")]))])))));
    ("TLC.LibListZ.make_eq_cons_make_pred",
     (["A"], [("n", Lang.Type.Int); ("v", Lang.Type.Var "A")],
      [`Assert (`App (("TLC.LibOrder.lt", [`Int (0); `Var ("n")])))],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibListZ.make", [`Var ("n"); `Var ("v")])),
       `Constructor (("::",
                      [`Var ("v");
                        `App (("TLC.LibListZ.make",
                               [`App (("-", [`Var ("n"); `Int (1)]));
                                 `Var ("v")]))
                        ])))));
    ("TLC.LibListZ.make_succ_r",
     (["A"], [("n", Lang.Type.Int); ("v", Lang.Type.Var "A")],
      [`Assert (`App (("TLC.LibOrder.ge", [`Var ("n"); `Int (0)])))],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibListZ.make",
              [`App (("+", [`Var ("n"); `Int (1)])); `Var ("v")])),
       `App (("TLC.LibList.app",
              [`App (("TLC.LibListZ.make", [`Var ("n"); `Var ("v")]));
                `Constructor (("::", [`Var ("v"); `Constructor (("[]", []))]))
                ])))));
    ("TLC.LibListZ.make_succ_l",
     (["A"], [("n", Lang.Type.Int); ("v", Lang.Type.Var "A")],
      [`Assert (`App (("TLC.LibOrder.ge", [`Var ("n"); `Int (0)])))],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibListZ.make",
              [`App (("+", [`Var ("n"); `Int (1)])); `Var ("v")])),
       `Constructor (("::",
                      [`Var ("v");
                        `App (("TLC.LibListZ.make", [`Var ("n"); `Var ("v")]))
                        ])))));
    ("TLC.LibListZ.make_zero",
     (["A"], [("v", Lang.Type.Var "A")], [],
      (Lang.Type.List (Lang.Type.Var "A"),
       `App (("TLC.LibListZ.make", [`Int (0); `Var ("v")])),
       `Constructor (("[]", [])))));
    ("TLC.LibListZ.length_make",
     (["A"], [("n", Lang.Type.Int); ("v", Lang.Type.Var "A")],
      [`Assert (`App (("TLC.LibOrder.ge", [`Var ("n"); `Int (0)])))],
      (Lang.Type.Int,
       `App (("TLC.LibListZ.length",
              [`App (("TLC.LibListZ.make", [`Var ("n"); `Var ("v")]))])),
       `Var ("n"))))
    ];
  functions =
  [("Coq.Init.Nat.add",
    Lang.Type.Forall ([], [Lang.Type.Int; Lang.Type.Int; Lang.Type.Int]));
    ("Coq.Init.Nat.sub",
     Lang.Type.Forall ([], [Lang.Type.Int; Lang.Type.Int; Lang.Type.Int]));
    ("Coq.ZArith.BinInt.Z.max",
     Lang.Type.Forall ([], [Lang.Type.Int; Lang.Type.Int; Lang.Type.Int]));
    ("Coq.ZArith.BinInt.Z.min",
     Lang.Type.Forall ([], [Lang.Type.Int; Lang.Type.Int; Lang.Type.Int]));
    ("TLC.LibInt.nat_to_Z",
     Lang.Type.Forall ([], [Lang.Type.Int; Lang.Type.Int]));
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
  invariant = ("I", [List (Var "A"); Int]);
  (* define fresh variables + make env map for  *)
  env =
    [("l", List (Var "A")); ("s", Func); ("v", Loc); ("tmp", Val);
     ("len", Var "Coq.Numbers.BinNums.Z"); ("ls", List (Var "A")); ("init", Var "A");
     ("rest", List (Var "A")); ("a", Array (Var "A")); ("data", List (Var "A"));
     ("idx", Var "Coq.Numbers.BinNums.Z"); ("tmp0", Val)];
  (* evaluate and assert equalities for all assumptions *)
  assumptions =
    [(List (Var "A"), `Var "ls", `Constructor ("::", [`Var "init"; `Var "rest"]));
     (Product [Int; List (Var "A")],
      `Tuple [`Var "len"; `Constructor ("::", [`Var "init"; `Var "rest"])],
      `Tuple [`App ("TLC.LibListZ.length", [`Var "l"]); `App ("TLC.LibList.rev", [`Var "l"])]);
     (List (Var "A"), `Constructor ("::", [`Var "init"; `Var "rest"]), `App ("TLC.LibList.rev", [`Var "l"]));
     (Int, `Var "len", `App ("TLC.LibListZ.length", [`Var "l"]));
     (List (Var "A"), `Var "data", `App ("TLC.LibListZ.make", [`Var "len"; `Var "init"]));
     (Int, `Var "idx", `App ("-", [`Var "len"; `Int 2]))];

  (* user provides input expression (Expr.t list -> Expr.t) & (Expr.t list -> Expr.t array)  *)
  initial = { expr_values = [|`Var "data"|]; param_values = [`Constructor ("[]", []); `Var "idx"] };

  conditions =
    [
      (* define fresh variables + make env map for qf *)
      { qf =
         [("r", List (Var "A")); ("t", List (Var "A")); ("v", Var "A"); ("acc", Int)];
        (* evaluate and assert equalities for assumptions *)
       assumptions = [`Eq ((List (Var "A"),
                            `Var "rest",
                            `App ("TLC.LibList.app", [`Var "t"; `Constructor ("::", [`Var "v"; `Var "r"])])))];
        (* param values *)
       param_values = [`Var "t"; `Var "acc"];

       post_param_values = [
         `App ("TLC.LibList.app",
               [`Var "t"; `Constructor ("::", [`Var "v"; `Constructor ("[]", [])])]);
         `App ("-", [`Var "acc"; `Int 1])
       ];
       expr_values = [|fun exp -> `App ("Array.set", [(`App ("CFML.WPArray.Array", [exp])); `Var "acc"; `Var "v"])|] }
    ]
}

type ctx = {
  ctx: Z3.context;
  solver: Z3.Solver.solver;
  int_sort: Z3.Sort.sort;
  poly_var_map: (string, Z3.Sort.sort) Hashtbl.t;
  update_map: (Lang.Type.t, Z3.FuncDecl.func_decl) Hashtbl.t;
  type_map: (Lang.Type.t, Z3.Sort.sort) Hashtbl.t;
  fun_map: (string, Lang.Type.t list * (Lang.Type.t list * Z3.FuncDecl.func_decl) list) Hashtbl.t
}

type env = {
  types: Lang.Type.t StringMap.t;
  values: Z3.Expr.expr StringMap.t;
}

type t = {
  ctx: ctx;
}

let rec typeof env (expr: Lang.Expr.t) : Lang.Type.t option =
  (match expr with
   | `Tuple elts ->
     List.all_some (List.map (typeof env) elts)
     |> Option.map (fun tys -> Lang.Type.Product tys)
   | `Var v -> StringMap.find_opt v env

   | `Lambda _ -> None
   | `Int _ -> Some Lang.Type.Int
   | `App ("-", _) -> Some Lang.Type.Int
   | `App ("+", _) -> Some Lang.Type.Int
   | `Constructor ("[]", []) -> None
   | `Constructor ("::", [h; t]) ->
     Option.choice [
       typeof env h |> Option.map (fun ty -> Lang.Type.List ty);
       typeof env t
     ]
   | `App (_, _) -> None
   | `Constructor _ -> None
  )

let rec eval_type (ctx: ctx) (ty: Lang.Type.t) : Z3.Sort.sort =
  Hashtbl.get_or_add ctx.type_map ~k:ty ~f:(fun ty ->
    match ty with
    | Unit -> Z3.Sort.mk_uninterpreted ctx.ctx (Z3.Symbol.mk_string ctx.ctx "unit")
    | Var "Coq.Numbers.BinNums.Z" -> ctx.int_sort
    | Int -> ctx.int_sort
    | Var v -> begin match Hashtbl.find_opt ctx.poly_var_map v with
      | Some s -> s
      | None -> failwith (Format.sprintf "found unknown type variable %s" v)
      end
    | List ity ->
      let sort = eval_type ctx ity in
      Z3.Z3List.mk_list_s ctx.ctx (Lang.Type.show ty) sort
    | Product elts ->
      Z3.Tuple.mk_sort ctx.ctx
        Z3.Symbol.(mk_string ctx.ctx (Lang.Type.show ty))
        (List.mapi (fun ind _ -> Z3.Symbol.mk_string ctx.ctx @@ Format.sprintf "get(%s)(%d)" (Lang.Type.show ty) ind)
           elts)
        (List.map (eval_type ctx) elts)
    | Array _
    | Ref _ 
    | Loc
    | ADT (_, _, _) 
    | Val 
    | Func ->
      Format.printf "treating type %s as opaque Z3 sort@." (Lang.Type.show ty);
      Z3.Sort.mk_uninterpreted_s ctx.ctx ((Lang.Type.show ty))
  )

let rec eval_expr ?(ty: Lang.Type.t option)
      (ctx: ctx)
      (env: env)
      (expr: Lang.Expr.t) =
  match expr, Option.or_lazy ~else_:(fun () -> typeof env.types expr) ty with
  | (`Var name, _) ->
    StringMap.find_opt name env.values
    |> Option.get_exn_or (Printf.sprintf "found unknown variable %s" name)
  | (`Int n, _) ->
    Z3.Arithmetic.Integer.mk_numeral_i ctx.ctx n
  | (`Tuple exprs, ty) ->
    let ty = ty |> Option.get_exn_or (Format.sprintf "could not type tuple %s" (Lang.Expr.show expr)) in
    let sort = eval_type ctx ty in
    let mk = Z3.Tuple.get_mk_decl sort in
    let exprs =
      begin match ty with
      | Product elts -> List.combine exprs (List.map Option.some elts) |> List.to_iter
      | _ -> List.to_iter exprs |> Iter.map (Fun.flip Pair.make None)
      end |> Iter.map (fun (expr, ty) -> eval_expr ?ty ctx env expr)
      |> Iter.to_list in
    Z3.FuncDecl.apply mk exprs
  | (`App ("TLC.LibOrder.le", [l;r]), _) ->
    let l = eval_expr ctx env l in
    let r = eval_expr ctx env r in
    Z3.Arithmetic.mk_le ctx.ctx l r
  | (`App ("TLC.LibOrder.lt", [l;r]), _) ->
    let l = eval_expr ctx env l in
    let r = eval_expr ctx env r in
    Z3.Arithmetic.mk_lt ctx.ctx l r
  | (`App ("TLC.LibOrder.ge", [l;r]), _) ->
    let l = eval_expr ctx env l in
    let r = eval_expr ctx env r in
    Z3.Arithmetic.mk_ge ctx.ctx l r
  | (`App ("TLC.LibOrder.gt", [l;r]), _) ->
    let l = eval_expr ctx env l in
    let r = eval_expr ctx env r in
    Z3.Arithmetic.mk_gt ctx.ctx l r
  | (`App ("+", [l;r]), _) ->
    let l = eval_expr ctx env l in
    let r = eval_expr ctx env r in
    Z3.Arithmetic.mk_add ctx.ctx [l;r]
  | (`App ("-", [l;r]), _) ->
    let l = eval_expr ctx env l in
    let r = eval_expr ctx env r in
    Z3.Arithmetic.mk_sub ctx.ctx [l;r]
  | (`App ("Array.set", [`App ("CFML.WPArray.Array", [ls]);ind;vl]), ty)
  | (`App ("TLC.LibContainer.update", [ls;ind;vl]), ty) ->
    let ty =
      match ty with
      | Some (List ty) -> Some ty
      | _ ->
        Option.or_lazy ~else_:(fun () -> typeof env.types vl)
          (Option.bind (typeof env.types ls) (function (List ty) -> Some ty | _ -> None)) in
    let ty = Option.get_exn_or "could not extract type of update" ty in
    let fdecl = Hashtbl.find_opt ctx.update_map ty
                |> Option.get_exn_or (Format.sprintf "found application of update to unsupported type %s"
                                     (Lang.Type.show ty)) in
    Z3.Expr.mk_app ctx.ctx fdecl [
      eval_expr ~ty:(List ty) ctx env ls;
      eval_expr ~ty:Int ctx env ind;
      eval_expr ~ty ctx env vl;
    ]
  | (`App (fname, args), _) ->
    begin match Hashtbl.find ctx.fun_map fname with
    | args_tys, [ptys, fapp] ->
      let arg_ty_map =
        let tbl = Hashtbl.create 10 in
        List.combine args_tys args
        |> List.iter (fun (aty, arg) ->
          Option.iter (fun ty ->
            Hashtbl.add tbl aty ty
          ) (typeof env.types arg)
        );
        tbl in
      let args = List.map (fun (ty, arg) ->
        let ty = Hashtbl.find_opt arg_ty_map ty in
        eval_expr ?ty ctx env arg
      ) (List.combine args_tys args) in
      Z3.Expr.mk_app ctx.ctx fapp args
    | _ ->
      failwith (Format.sprintf
                  "found multiple polymorphic instantiations for function %s (not supported atm)"
                  fname)
    | exception e ->
      failwith (Format.sprintf
                  "found use of unknown function %s (error %s)" fname (Printexc.to_string e))
    end
  | (`Constructor ("::", [h; t]), None) when Option.is_some (typeof env.types h) ->
    let ty = Lang.Type.List (typeof env.types h |> Option.get_exn_or "invalid type") in
    let cons = Z3.Z3List.get_cons_decl (Hashtbl.find ctx.type_map ty) in
    let h =
      let ty = match ty with Lang.Type.List ty -> Some ty | _ -> None in
      eval_expr ?ty ctx env h in
    let t = eval_expr ~ty ctx env t in
    Z3.Expr.mk_app ctx.ctx cons [h;t]
  | (`Constructor ("::", [h; t]), None) when Option.is_some (typeof env.types t) ->
    let ty = typeof env.types t |> Option.get_exn_or "invalid type" in
    let cons = Z3.Z3List.get_cons_decl (Hashtbl.find ctx.type_map ty) in
    let h =
      let ty = match ty with Lang.Type.List ty -> Some ty | _ -> None in
      eval_expr ?ty ctx env h in
    let t = eval_expr ~ty ctx env t in
    Z3.Expr.mk_app ctx.ctx cons [h;t]
  | (`Constructor ("::", [h; t]), Some ty) ->
    let cons = Z3.Z3List.get_cons_decl (Hashtbl.find ctx.type_map ty) in
    let t = eval_expr ~ty ctx env t in
    let h =
      let ty = match ty with Lang.Type.List ty -> Some ty | _ -> None in
      eval_expr ?ty ctx env h in
    Z3.Expr.mk_app ctx.ctx cons [h;t]
  | (`Constructor ("[]", []), Some ty) ->
    let nil = Z3.Z3List.get_nil_decl (Hashtbl.find ctx.type_map ty) in
    Z3.Expr.mk_app ctx.ctx nil []
  | (`Lambda _, _)
  | (`Constructor _, _) -> invalid_arg (Format.sprintf "attempt to convert unsupported expression %s to Z3"
                                       (Lang.Expr.show expr))

let embed (data: Proof_validator.Verification_condition.verification_condition) =
  let data = normalize data in
  let ctx = Z3.mk_context ["model", "false"; "proof", "false"; "timeout", "1000"] in
  let solver = Z3.Solver.mk_solver ctx None in
  Z3.Solver.set_parameters solver (
    let params = Z3.Params.mk_params ctx in
    Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout") 1000;
    params
  );

  let poly_var_map = 
    List.map Fun.(Pair.dup_map @@ Z3.Sort.mk_uninterpreted ctx % Z3.Symbol.mk_string ctx) data.poly_vars
    |> Hashtbl.of_list in
  let int_sort = Z3.Arithmetic.Integer.mk_sort ctx in

  let ctx = {ctx; solver; int_sort; poly_var_map;
             type_map=Hashtbl.create 10;
             fun_map=Hashtbl.create 10;
             update_map=Hashtbl.create 10; } in
  let type_map = StringMap.of_list data.env in
  let env =
    data.env
    |> List.to_iter
    |> Iter.map Pair.(map_snd (eval_type ctx))
    |> Iter.map Fun.(Pair.dup_map @@ uncurry @@ Z3.Expr.mk_fresh_const ctx.ctx)
    |> Iter.map Pair.(map_fst fst)
    |> StringMap.of_iter in

  List.iter (fun (name, sort) ->
    let fdecl = 
    Z3.FuncDecl.mk_fresh_func_decl ctx.ctx
      (Format.sprintf "TLC.LibContainer.update(%s)" name) [
        eval_type ctx (List (Var name));
        eval_type ctx (Int);
        eval_type ctx (Var name)
      ]  (eval_type ctx (List (Var name)) ) in
    Hashtbl.add ctx.update_map (Var name) fdecl
  ) (Hashtbl.to_list poly_var_map);

  List.iter (fun (fname, Lang.Type.Forall (vars, sign)) ->
    let (let+) x f = List.(>>=) x f in
    let param_tys = split_last sign |> Option.get_exn_or "unexpected func signature" |> fst in
    let bindings = 
      let+ vars = List.map_product_l (fun v -> List.map Pair.(make v) data.poly_vars) vars in
      let fname = fname ^ "(" ^ String.concat "," (List.map snd vars) ^ ")" in
      let poly_binding =
        List.map (fun (v, poly_var) -> (v, Lang.Type.Var poly_var)) vars
        |> StringMap.of_list in
      let sign = List.map Lang.Type.(subst poly_binding) sign in
      let fname = Z3.Symbol.mk_string ctx.ctx fname in

      let sign = List.map (eval_type ctx) sign in
      let args, ret = split_last sign |> Option.get_exn_or "empty signature" in
      let fb = Z3.FuncDecl.mk_func_decl ctx.ctx fname args ret in
      [List.map (fun (_, v) -> Lang.Type.Var v) vars, fb] in
    Hashtbl.add ctx.fun_map fname (param_tys, bindings);
  ) data.functions;
  let env = {values=env; types=type_map} in
  let assumptions = 
    List.map (fun (ty, l, r) ->
      let l = eval_expr ~ty ctx env l in
      let r = eval_expr ~ty ctx env r in
      Z3.Boolean.mk_eq ctx.ctx l r
    ) data.assumptions in
  Z3.Solver.add solver assumptions;
  List.iter (fun (name, (poly_vars, params, assumptions, (ty, l, r))) ->
    List.map_product_l (fun v -> List.map Pair.(make v) data.poly_vars) poly_vars
    |> List.iter (fun vars ->
      try
        let ty_instantiation =
          List.map (fun (v, poly_var) -> (v, Lang.Type.Var poly_var)) vars
          |> StringMap.of_list in
        let env, params = List.fold_map (fun env (name, ty) ->
          let ty = Lang.Type.subst ty_instantiation ty in
          let sort = eval_type ctx ty in
          let var = Z3.Expr.mk_const_s ctx.ctx name sort in
          {types=StringMap.add name ty env.types;
           values=StringMap.add name var env.values}, var
        ) env params in
        let body =
          let assumptions' =
            List.map (function
                `Eq (ty, l, r) ->
                let ty = Lang.Type.subst ty_instantiation ty in
                let l = eval_expr ~ty ctx env l in
                let r = eval_expr ~ty ctx env r in
                Z3.Boolean.mk_eq ctx.ctx l r              
              | `Assert expr ->
                eval_expr ctx env expr
            ) assumptions
            |> Z3.Boolean.mk_and ctx.ctx in
          let concl =
            let l = eval_expr ~ty ctx env l in
            let r = eval_expr ~ty ctx env r in
            Z3.Boolean.mk_eq ctx.ctx l r in
          if List.is_empty assumptions
          then concl
          else
            Z3.Boolean.mk_implies ctx.ctx
              assumptions'
              concl
        in
        Z3.Solver.add solver [
          Z3.Quantifier.expr_of_quantifier @@
          Z3.Quantifier.mk_forall_const ctx.ctx params body None [] [] None None
        ]
      with (Z3.Error _ | Invalid_argument _) as _e ->
        (* Format.printf "adding %s ==> " name;
         * Format.printf "failed %s@." ( Printexc.to_string e ); *)
        ()
    );
  ) data.properties;

  print_endline @@ Format.sprintf "Z3 model is %s" (Z3.Solver.to_string solver);

  (* once Z3 context initialised, return a generator function that can be used to validate candidate expressions *)
  fun (gen_pred, gen_values) ->
    let (let-!) x f = match x with Some true -> f () | v -> Z3.Solver.pop solver 1; v in 
    let negate x = Z3.Boolean.mk_not ctx.ctx x in
    let check x = match Z3.Solver.check solver [x] with
        Z3.Solver.UNSATISFIABLE -> Some false
      | SATISFIABLE -> Some true
      | UNKNOWN -> None in
    let prove x = Option.map not @@ check (negate x) in
    let rec all_hold = function
      | [] -> Some true
      | h :: t ->
        match prove h with
        | Some true -> Z3.Solver.add solver [h]; all_hold t
        | v -> v in
    let rec iter f = function
      | [] -> Some true
      | h :: t ->
        match f h with
        | Some true -> iter f t
        | v -> v in
    Z3.Solver.push solver;
    (* check the initial predicate generated by the user *)
    let user_initial_pred = gen_pred data.initial.param_values
                            |> eval_expr ctx env in
    let-! () = prove user_initial_pred in
    Z3.Solver.add solver [user_initial_pred];
    let user_initial_values = gen_values data.initial.param_values |> Array.to_list in

    (* check initial values are equal to the expressions used to fill the holes by the user *)
    let-! () = 
      List.combine user_initial_values (Array.to_list data.initial.expr_values)
      |> List.map (fun (l, r) -> Z3.Boolean.mk_eq ctx.ctx (eval_expr ctx env l) (eval_expr ctx env r))
      |> all_hold in

    (* for each remaining invariant verification condition  *)

    let-! () = iter (fun (vc: Proof_validator.Verification_condition.vc) ->
      Z3.Solver.push solver;
      let env = vc.qf
                |> List.fold_left (fun env (name, ty) ->
                  let sort = eval_type ctx ty in
                  {values = StringMap.add
                              name (Z3.Expr.mk_const_s ctx.ctx name sort)
                              env.values;
                   types = StringMap.add name ty env.types}
                ) env in
      let assumptions = 
        List.map (function
          | `Eq (ty, l, r) ->
            let l = eval_expr ~ty ctx env l in
            let r = eval_expr ~ty ctx env r in
            Z3.Boolean.mk_eq ctx.ctx l r
          | `Assert expr ->
            eval_expr ctx env expr
        ) vc.assumptions in
      Z3.Solver.add solver assumptions;
      (* user predicate holds with initial parameters *)
      let user_pre_pred = gen_pred vc.param_values |> eval_expr ctx env in
      Z3.Solver.add solver [user_pre_pred];

      (* 1st. check that implies predicate with post param values *)
      let user_post_pred = gen_pred vc.post_param_values |> eval_expr ctx env in
      let-! () = prove user_post_pred in
      Z3.Solver.add solver [user_post_pred];

      (* 2nd. check user generated post values (with post param values) are equal to
         user generated pre values symbolically evaluated *)
      let user_post_values = gen_values vc.post_param_values |> Array.to_list in
      let user_preval_values = 
        let user_pre_values = gen_values vc.param_values |> Array.to_list in
        List.combine user_pre_values (Array.to_list vc.expr_values)
        |> List.map (fun (expr, f) -> f expr) in
      let-! () =
        List.combine user_post_values user_preval_values
        |> List.map (fun (l,r) ->
          Z3.Boolean.mk_eq ctx.ctx (eval_expr ctx env l) (eval_expr ctx env r)
        )
        |> all_hold in
      (* if all hold, then we good boys. *)
      Z3.Solver.pop solver 1;
      Some true
    ) data.conditions in

    Z3.Solver.pop solver 1;
    Some true


let () =
  let _t = embed data in
  print_endline "hello world"
