open Containers
module SP = Serapi.Serapi_protocol

include Context

module Make(C: Context.CONFIG) = struct
  module Ctx = Context.Make(C)

  type proof = {mutable states: Ctx.state list}

  let prf = {states=[]}

  let size () = List.length prf.states

  let current_state prf =
    List.head_opt prf.states
    |> Option.value ~default:Ctx.initial_state

  let reset () =
    Ctx.fresh_doc ();
    prf.states <- []

  let add txt =
    let states =
      Ctx.add ~state:(current_state prf) txt in
    prf.states <- List.rev_append states  prf.states

  let cancel ~count =
    let cancelled, states = List.take_drop count prf.states in
    prf.states <- states;
    ignore @@ Ctx.cancel states

  let cancel_last () =
    let cancelled, states = List.hd_tl prf.states in
    prf.states <- states;
    ignore @@ Ctx.cancel [cancelled]

  let parse txt =
    Ctx.parse ~state:(current_state prf) txt
    
  let query cmd =
    Ctx.query (current_state prf) cmd
    
  let exec () =
    Ctx.exec (current_state prf)

  let debug_current_goal () =
    query SP.Goals
    |> Option.map (fun objs ->
      Format.sprintf "%a" 
        (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ") Pp.pp_with)
        (List.map (SP.gen_pp_obj Environ.empty_env Evd.empty) objs)
    )
    |> Option.value ~default:"EMPTY-CONTEXT"

end
