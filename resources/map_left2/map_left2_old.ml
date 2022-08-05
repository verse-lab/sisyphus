open Common

let map_left2 f a g b =
  let l = Array.length a in
  if Int.equal l 0 then [||], [||] else begin
    let r = Array.make l (f a.(0)) in
    let s = Array.make l (g b.(0)) in
    for i = 1 to l - 1 do
      r.(i) <- f a.(i);
      s.(i) <- g b.(i)
    done;
    r, s
  end
