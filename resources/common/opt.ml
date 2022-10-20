
let option_is_some = function
  | Some _ -> true
  | _ -> false


let option_is_none = function
  | None -> true
  | _ -> false

let opt_of_bool = function
  | true -> Some ()
  | false -> None
