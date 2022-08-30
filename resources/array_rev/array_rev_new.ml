open Common

let rev t =
  let len = Array.length t in
  let last = len - 1 in
  let rec rev_aux i =
    if i < 0 then ()
    else begin
      let x = t.(i) in
      t.(i) <- t.(last-i);
      t.(last-i) <- x;
      rev_aux (i - 1);
    end in
  rev_aux (len / 2 - 1)
