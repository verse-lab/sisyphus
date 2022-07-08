let hd = function
  | [] -> assert false
  | a::_ -> a

let tl = function
  | [] -> assert false
  | _::l -> l
