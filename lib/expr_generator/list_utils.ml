open Containers

let (let+) x f = List.(>>=) x f
let mapM f ls =
  let fold_func a r =
    let+ x = f a in
    let+ xs = r in
    List.return (x :: xs)
  in
  List.fold_right fold_func ls (List.return [])
