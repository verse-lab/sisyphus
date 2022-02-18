open Logic

let p ls t i = i = List.length ls - List.length t - !* 2
let e last t i = List.append (List.repeat (i + !* 1) last) (List.rev (List.cons last t))

let do_test_pure p = 
  let len = declare "len" int in
  let ls = declare "ls" List.t in
  let last = declare "last" a in
  let rest = declare "rest" List.t in


  let eval t i exp =
    let ctx = Eval.StringMap.of_list [
      "len", len; "ls", ls; "last", last; "rest", rest;
      "t", t; "i", i; 
    ] in
    Eval.eval_expr ctx exp in

  let p t i = eval t i p in

  let test1 p () =
    let h1 = len = List.length ls in
    let h2 = List.cons last rest = List.rev ls in
    let h3 = p List.nil (len - !* 2) in
    let result = prove [h1;h2] h3 in
    Option.value ~default:false result in
  
  let do_test p () =
    test1 p () in
  do_test p ()

let do_test p e = 
  let len = declare "len" int in
  let ls = declare "ls" List.t in
  let last = declare "last" a in
  let rest = declare "rest" List.t in


  let eval t i exp =
    let ctx = Eval.StringMap.of_list [
      "len", len; "ls", ls; "last", last; "rest", rest;
      "t", t; "i", i; 
    ] in
    Eval.eval_expr ctx exp in

  let p t i = eval t i p in
  let e t i = eval t i e in
  
  let t = declare "t" List.t in
  let i = declare "i" int in
  let x = declare "x" a in
  let r = declare "r" List.t in

  let test1 _e p () =
    let h1 = len = List.length ls in
    let h2 = List.cons last rest = List.rev ls in
    let h3 = p List.nil (len - !* 2) in
    let result = prove [h1;h2] h3 in
    Option.value ~default:false result in


  let test2 e p () =
    let h1 = len = List.length ls in
    let h2 = List.cons last rest = List.rev ls in
    let h3 = p List.nil (len - !* 2) in
    let h4 = List.repeat len last = e List.nil (len - !* 2) in
    let result = prove [h1;h2; h3] h4 in
    Option.value ~default:false result in

  let test3 e p () =

    let h1 = len = List.length ls in
    let h2 = List.cons last rest = List.rev ls in
    let h3 = p List.nil (len - !* 2) in
    let h4 = List.repeat len last = e List.nil (len - !* 2) in

    let h5 = p t i in
    let h6 = rest = List.append t (List.cons x r) in

    let h7 = i < (List.length (e t i)) in

    let result = prove [h1;h2; h3; h4; h5; h6] h7 in
    Option.value ~default:false result in

  let test4 e p () =

    let h1 = len = List.length ls in
    let h2 = List.cons last rest = List.rev ls in
    let h3 = p List.nil (len - !* 2) in
    let h4 = List.repeat len last = e List.nil (len - !* 2) in

    let h5 = p t i in
    let h6 = rest = List.append t (List.cons x r) in

    let h7 = i < (List.length (e t i)) in
    let h8 = !* 0 <= i in

    let result = prove [h1;h2; h3; h4; h5; h6; h7] h8 in
    Option.value ~default:false result in

  let test5 e p () =

    let h1 = len = List.length ls in
    let h2 = List.cons last rest = List.rev ls in
    let h3 = p List.nil (len - !* 2) in
    let h4 = List.repeat len last = e List.nil (len - !* 2) in

    let h5 = p t i in
    let h6 = rest = List.append t (List.cons x r) in

    let h7 = i < (List.length (e t i)) in
    let h8 = !* 0 <= i in

    let h9 = p (List.rcons t x) (i - !* 1)  in
    let result = prove [h1;h2; h3; h4; h5; h6; h7; h8] h9 in
    Option.value ~default:false result in

  let test6 e p () =

    let h1 = len = List.length ls in
    let h2 = List.cons last rest = List.rev ls in
    let h3 = p List.nil (len - !* 2) in
    let h4 = List.repeat len last = e List.nil (len - !* 2) in

    let h5 = p t i in
    let h6 = rest = List.append t (List.cons x r) in

    let h7 = i < (List.length (e t i)) in
    let h8 = !* 0 <= i in

    let h9 = p (List.rcons t x) (i - !* 1)  in

    let h10 = 
      List.update (List.append (List.repeat (i + !* 1) last) (List.rev (List.cons last t))) i x =
      e (List.rcons t x) (i - !* 1) in
    let result = prove [h1;h2; h3; h4; h5; h6; h7; h8; h9] h10 in
    Option.value ~default:false result in
  
  let do_test e p () =
    Bool.(test1 e p () && test2 e p () && test3 e p () && test4 e p () && test5 e p () && test6 e p ()) in
  do_test e p ()
