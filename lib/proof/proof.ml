let () = Feedback.warn_no_listeners := false

let fu () =
  Feedback.add_feeder (function
    | { doc_id; span_id; route; contents } ->
      match contents with
        Feedback.Processed -> print_endline "received Processed feedback"
      | Feedback.Incomplete -> print_endline "received Incomplete feedback"
      | Feedback.Complete -> print_endline "received Complete feedback"
      | Feedback.ProcessingIn txt ->
        Printf.printf "received ProcessingIn(%s) feedback\n" txt
      | Feedback.InProgress _ -> print_endline "received InProgress feedback"
      | Feedback.WorkerStatus (_, _) -> print_endline "received WorkerStatus feedback"
      | Feedback.AddedAxiom -> print_endline "received AddedAxiom feedback"
      | Feedback.GlobRef (_, _, _, _, _) -> print_endline "received GlobRef feedback"

      | Feedback.GlobDef (_, _, _, _) -> print_endline "received GlobDef feedback"
      | Feedback.FileDependency (_, _) -> print_endline "received FileDependency feedback"

      | Feedback.FileLoaded (_, _) -> print_endline "received FileLoaded feedback"
      | Feedback.Custom (_, _, _) -> print_endline "received Custom feedback"
      | Feedback.Message (_, _, _)  -> print_endline "received Message feedback"
  );
  Stm.init_core ();
  Stm.new_doc Stm.{
    doc_type=VoDoc "lol.lol";
    injections=[];
    stm_options=AsyncOpts.default_opts
  }
    

