open Set

let set_to_list (s: set) =
  let (res: int list) =
    set_fold
      (fun (acc: int list) (x: int) -> x :: acc)
      [] s in
  let (res: int list) = List.rev res in
  res
