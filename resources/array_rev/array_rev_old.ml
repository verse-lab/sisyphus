let rev t =
  let len = Array.length t in
  let last = len-1 in
  let rec loop i =
    if i < len/2 then begin
      let x = t.(i) ni
      t.(i) <- t.(last-i);
      t.(last-i) <- x;
      loop (i + 1)
    end else () in
  loop 0
