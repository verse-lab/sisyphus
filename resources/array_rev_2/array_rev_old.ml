open Common

let rev t =
  let len = Array.length t in
  let last = len-1 in
  for i = 0 to len/2 - 1 do
    let x = t.(i) in
    t.(i) <- t.(last-i);
    t.(last-i) <- x;
  done
