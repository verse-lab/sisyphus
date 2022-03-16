open Containers

module StringMap = Map.Make (String)
module IntMap = Map.Make(Int)
module IntPairMap = Map.Make(struct
    type t = int * int [@@deriving ord]
  end)

type 'a stringmap = 'a StringMap.t
let equal_stringmap f a b = StringMap.equal f a b
let pp_stringmap f fmt vl =
  StringMap.pp
    ~pp_start:Format.(fun fmt () ->
      pp_open_hovbox fmt 1;
      pp_print_string fmt "{")
    ~pp_stop:Format.(fun fmt () ->
      pp_print_string fmt "}";
      pp_close_box fmt ()
    )
    ~pp_sep:Format.(fun fmt () -> pp_print_string fmt " -> ")
    String.pp f fmt vl

type 'a intmap = 'a IntMap.t
let equal_intmap f a b = IntMap.equal f a b
let pp_intmap f fmt vl =
  IntMap.pp
    ~pp_start:Format.(fun fmt () ->
      pp_open_hovbox fmt 1;
      pp_print_string fmt "{")
    ~pp_stop:Format.(fun fmt () ->
      pp_print_string fmt "}";
      pp_close_box fmt ()
    )
    ~pp_sep:Format.(fun fmt () -> pp_print_string fmt " -> ")
    Int.pp f fmt vl

type 'a intpairmap = 'a IntPairMap.t
let equal_intpairmap f a b = IntPairMap.equal f a b
let pp_intpairmap f fmt vl =
  IntPairMap.pp
    ~pp_start:Format.(fun fmt () ->
      pp_open_hovbox fmt 1;
      pp_print_string fmt "{")
    ~pp_stop:Format.(fun fmt () ->
      pp_print_string fmt "}";
      pp_close_box fmt ()
    )
    ~pp_sep:Format.(fun fmt () -> pp_print_string fmt " -> ")
    (Pair.pp Int.pp Int.pp) f fmt vl

let remove_one ~eq x l =
  let rec remove_one ~eq x acc l = match l with
    | [] -> assert false
    | y :: tl when eq x y -> List.rev_append acc tl
    | y :: tl -> remove_one ~eq x (y::acc) tl
  in
  if List.mem ~eq x l then Some (remove_one ~eq x [] l) else None


let remove_first ~pred l =
  let exception Fail in
  let[@tail_mod_cons] rec loop l =
    match l with
    | [] -> raise_notrace Fail
    | h :: t when pred h -> t
    | h :: t -> h :: loop t in
  try Some (loop l) with
  | Fail -> None
        
