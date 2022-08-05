type 'a mut_list =  {
  hd: 'a option;
  mutable tl: 'a mut_list option
}

let dummy () = {hd=None;tl=None}
let create x = {hd=Some x; tl=Some {hd=None; tl=None}}

let rec proj ls =
  let tl = match ls.tl with
    | None -> []
    | Some x -> proj x
  in
  match ls.hd with
  | None -> tl
  | Some x -> x :: tl

let accum acc x =
    let cell = create x in
    acc.tl <- Some cell;
    cell
