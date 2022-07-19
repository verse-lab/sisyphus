let a = Array.make 100 1
let tmp0 = (fun (i: int) (x: 'a) -> a.(i) <- x; i - 1)

let test i =  
  let x0__ = 9 :: 8 :: [] in
  i [] 2;
  match x0__ with
  | [] ->
    i [] 2;
    2
  | a :: l1 ->
    i [] 2;
    let x = tmp0 2 a in
    let rec loop x t init =
      i t init;
      let x0__ = x in
      i t init;
      match x0__ with
      | [] ->
        i t init;
        init
      | a :: l1 ->
        i t init;
        let x = tmp0 init a in
        i (t @ a :: []) x;
        loop l1 (t @ a :: []) x
    in
    loop l1 ([] @ (a :: [])) x
    
