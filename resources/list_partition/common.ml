type 'a mut_list =  {
  hd: 'a option;
  mutable tl: 'a list
}

let dummy () = {hd=None;tl=[]}
let create x = {hd=Some x; tl=[]}

let inj {hd; tl} =
  match hd with
  | None -> tl
  | Some hd -> (hd :: tl)

let accum acc x =
    let cell = create x in
    acc.tl <- inj cell;
    cell
