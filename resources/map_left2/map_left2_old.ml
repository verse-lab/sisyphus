open Common

let map_left2 f a g b =
  let l = Array.length a in
  if Int.equal l 0 then [||], [||] else begin
    let r = Array.make l (f a.(0)) in
    let s = Array.make l (g b.(0)) in
    let rec loop i =
      if i < l then begin
        r.(i) <- f a.(i);
        s.(i) <- g b.(i);
        loop (i + 1)
      end else () in
    loop 1; 
   r, s
  end
