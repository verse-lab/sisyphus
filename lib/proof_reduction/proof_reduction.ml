type filter = Config.filter

let with_filter filter f =
  let saved_filter = !Config.filter in
  Config.filter := filter;
  Fun.protect
    ~finally:(fun () -> Config.filter := saved_filter)
    (fun () ->
       f ())

let reduce ?unfold ?filter ?cbv env evd cstr =
  match filter with
  | None -> Ultimate_tactics.reduce ?unfold ?cbv env evd cstr
  | Some filter ->
    with_filter filter (fun () -> Ultimate_tactics.reduce  ?unfold ?cbv env evd cstr)
