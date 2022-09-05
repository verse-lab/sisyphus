open Common

let map_left2 f a g b =
  let l = Array.length a in
  if l = 0 then [||], [||] else begin
    let r = Array.make l (f a.(0)) in
    let s = Array.make l (g b.(0)) in
    Array.iteri (fun i _ -> r.(i) <- f a.(i)) r;
    Array.iteri (fun i _ -> s.(i) <- g b.(i)) s;
    r, s
  end
