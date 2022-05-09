[@@@warning "-33-26"]
open Containers

let old_program =
  IO.with_in "../../_build/default/resources/seq_to_array/seq_to_array_old.ml" IO.read_all
  |> Lang.Sanitizer.parse_str

let new_program =
  IO.with_in "../../_build/default/resources/seq_to_array/seq_to_array_new.ml" IO.read_all
  |> Lang.Sanitizer.parse_str
  
let prelude = {coq|
Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Proofs Require Import Verify_seq_to_array_utils.
From Proofs Require Import Seq_to_array_new_ml.
|coq}
  

type coq_ctx = (module Coq.Proof.PROOF)
let add (module Ctx: Coq.Proof.PROOF) txt =
  Ctx.add txt
let exec (module Ctx: Coq.Proof.PROOF) =
  Ctx.exec ()

let add_and_exec ctx txt =
  add ctx txt;
  exec ctx

let goal ?at (module Ctx: Coq.Proof.PROOF) =
  Ctx.query ?at Serapi.Serapi_protocol.Goals
  |> Option.map @@ List.map (function[@warning "-8"]
    | Serapi.Serapi_protocol.CoqGoal g -> g
  )
  |> function
  | Some [goal] -> goal
  | Some _ -> failwith "failed to obtain goal - serapi returned multiple goals."
  | None -> failwith "unable to retrieve goal - serapi returned None."

let env ?at (module Ctx: Coq.Proof.PROOF) =
  Ctx.query ?at Serapi.Serapi_protocol.Env
  |> Option.flat_map (fun env ->
    match env with
    |[Serapi.Serapi_protocol.CoqEnv env] -> Some env
    | _ -> None
  )


let generate (alignment: Dynamic.Matcher.t) (ctx: coq_ctx) (prog: Lang.Expr.t Lang.Program.t) =
  (* TODO: add spec for function.... *)
  add_and_exec ctx {|
Lemma to_array_spec : forall (A: Type) `{EA:Enc A} (l:list A) (s:func) (v: loc),
    SPEC (to_array s)
    PRE (\[LSeq l s])
    POST (fun (a: loc) => a ~> Array l).
Proof using.
|};
  (* initialise proof state *)
  add_and_exec ctx {|xcf.|};
  let current_goal () =
    match (goal ctx).goals with
    | [goal] -> goal
    | _ -> failwith "expected a single goal - found multiple goals." in
  let to_string s = Format.sprintf "%a" Pp.pp_with (Constr.debug_print s) in
  let debug_print_current_goal () =
    let env = env ctx |> Option.get_exn_or "failed" in
    print_endline @@ "current goal: \n" ^
                     Format.sprintf "%a" Pp.pp_with
                       (Serapi.Serapi_protocol.gen_pp_obj
                          env Evd.empty (Serapi.Serapi_protocol.CoqGoal (goal ctx))) in
  let print_current_goal () =
    print_endline @@ "current goal: \n" ^ to_string (current_goal ()).ty in

  let extract_cfml_goal () =
    let goal = (current_goal ()).ty in
    let[@warning "-8"] himpl, [pre; post] = Constr.decompose_app goal in
    assert begin
      String.equal
        "himpl"
        (fst (Constr.destConst himpl)
         |> Names.Constant.label
         |> Names.Label.to_string)
    end;
    let is_const_named name const =
      Constr.isConst const &&
      String.(
        (fst @@ Constr.destConst const)
        |> Names.Constant.label
        |> Names.Label.to_string = name
      ) in
    let is_hempty const = is_const_named "hempty" const in
    let is_hstar const = is_const_named "hstar" const in
    let is_hpure const = is_const_named "hpure" const in
    let destruct_heap pre =
      let rec loop acc pre =
        match Constr.kind pre with
        | Constr.Const (_, _) when is_hempty pre -> acc
        | Constr.App (fname, [|heaplet; rest|]) when is_hstar fname ->
          begin match Constr.kind heaplet with
          | Constr.App (fname, _) when is_hpure fname ->
            loop (`Pure heaplet :: acc) rest             
          | _ ->
            loop (`Impure heaplet :: acc) rest 
          end
        | _ ->
          (`Impure pre :: acc) in
      loop [] pre in
    let pre =
      match Constr.kind pre with
      | Constr.Const (_, _) when is_hempty pre -> `Empty
      | Constr.App (fname, _) when is_hstar fname ->
        begin match destruct_heap pre with
        | heap -> `NonEmpty heap
        | exception _ -> failwith ("unexpected pre-heap structure: " ^ (to_string pre))
        end
      | Constr.App (fname, _) when is_hpure fname ->
        `NonEmpty ([`Pure pre])
      | _ -> failwith ("unexpected pre-heap structure: " ^ (to_string pre)) in
    (pre, post) in

  let pre, _ = extract_cfml_goal () in
  let intro_pure no_pure =
    let pat = 
    Int.range 1 no_pure
    |> Iter.map (fun i -> "H" ^ Int.to_string i)
    |> Iter.concat_str in
    add_and_exec ctx (Format.sprintf "xpullpure %s." pat) in

  let module StringSet = Set.Make(String) in

  let current_names () =
    let goal = current_goal () in
    goal.hyp
    |> List.to_iter
    |> Iter.filter_map (fun (name, _, _) -> List.last_opt name)
    |> Iter.map Names.Id.to_string
    |> StringSet.of_iter in

  let fresh ?(base="tmp") () =
    let names = current_names () in
    let name_in_use name =
      StringSet.mem name names in
    let rec loop incr =
      let name = Format.sprintf "%s%d" base incr in 
      if name_in_use name
      then loop (incr + 1)
      else name in
    if name_in_use base
    then loop 0
    else base in

  begin match pre with
  | `Empty -> ()
  | `NonEmpty ls ->
    let no_pure = List.count (function `Pure _ -> true | _ -> false) ls in
    intro_pure no_pure;
  end;
  let rec loop (body: Lang.Expr.t Lang.Program.stmt) =
    print_endline @@ Format.sprintf "remaining program is: %a" (Lang.Program.pp_stmt_line Lang.Expr.print) body;
    debug_print_current_goal ();
    (match body with
     | `LetLambda (name, body, rest) ->
       let fname = fresh ~base:name () in
       let h_fname = fresh ~base:("H" ^ name) () in
       add_and_exec ctx (Format.sprintf "xletopaque %s %s." fname h_fname);
       loop rest
     | `Match _ -> failwith "don't know how to handle matches"
     | `EmptyArray -> failwith "don't know how to handle empty arrays"
     | `Write _ -> failwith "don't know how to handle write"
     | `Value _ -> failwith "don't know how to handle value"
     | `LetExp _ -> failwith "don't know how to handle let bindings")
  in
  ignore @@ loop prog.body;
  ()


let () =
  (* build alignment between programs *)
  let alignment =
    Dynamic.build_alignment
      ~deps:["../../_build/default/resources/seq_to_array/common.ml"]
      ~old_program
      ~new_program () in

  (* initialise coq ctx *)
  let module Ctx = (val Coq.Proof.make [
    Coq.Coqlib.make ~path:(Fpath.of_string "../../_build/default/resources/seq_to_array/" |> Result.get_exn) "Proofs"
  ]) in
  Ctx.reset ();
  Ctx.add prelude;
  Ctx.exec ();

  ignore @@ generate alignment (module Ctx) new_program;

