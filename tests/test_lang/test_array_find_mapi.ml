open Containers

let () = 
  let prog =
    IO.with_in "../../resources/find_mapi/find_mapi_old.ml" IO.read_all
    |> Lang.Sanitizer.parse_str in
  Format.printf "OLD:\n%a\n" (Lang.Program.pp Lang.Expr.print) prog


let () = 
  let prog =
    IO.with_in "../../resources/find_mapi/find_mapi_new.ml" IO.read_all
    |> Lang.Sanitizer.parse_str in
  Format.printf "NEW:\n%a\n" (Lang.Program.pp Lang.Expr.print) prog

