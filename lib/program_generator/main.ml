[@@@warning "-33-26"]
open Containers

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

let old_program =
  IO.with_in "../../_build/default/resources/seq_to_array/seq_to_array_old.ml" IO.read_all
  |> Lang.Sanitizer.parse_str

let new_program =
  IO.with_in "../../_build/default/resources/seq_to_array/seq_to_array_new.ml" IO.read_all
  |> Lang.Sanitizer.parse_str

let drop_last ls =
  let rec loop acc = function
    | [] | [_] -> List.rev acc
    | h :: t -> loop (h :: acc) t in
  loop [] ls

let prelude = {coq|
Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Proofs Require Import Verify_seq_to_array_utils.
From Proofs Require Import Seq_to_array_new_ml.
|coq}

let tag ty =
  match Constr.kind ty with
  | Constr.Rel _ -> "Rel"
  | Constr.Var _ -> "Var"
  | Constr.Meta _ -> "Meta"
  | Constr.Evar _ -> "Evar"
  | Constr.Sort _ -> "Sort"
  | Constr.Cast (_, _, _) -> "Cast"
  | Constr.Prod (_, _, _) -> "Prod"
  | Constr.Lambda (_, _, _) -> "Lambda"
  | Constr.LetIn (_, _, _, _) -> "LetIn"
  | Constr.App (_, _) -> "App"
  | Constr.Const _ -> "Const"
  | Constr.Ind _ -> "Ind"
  | Constr.Construct _ -> "Construct"
  | Constr.Case (_, _, _, _, _, _, _) -> "Case"
  | Constr.Fix _ -> "Fix"
  | Constr.CoFix _ -> "CoFix"
  | Constr.Proj (_, _) -> "Proj"
  | Constr.Int _ -> "Int"
  | Constr.Float _ -> "Float"
  | Constr.Array (_, _, _, _)  -> "Array"  

type coq_ctx = (module Coq.Proof.PROOF)
let add (module Ctx: Coq.Proof.PROOF) txt =
  Ctx.add txt
let exec (module Ctx: Coq.Proof.PROOF) =
  Ctx.exec ()

let search (module Ctx: Coq.Proof.PROOF) txt =
  Ctx.query Serapi.Serapi_protocol.(Names txt)
  |> Option.map (List.map (fun v -> Format.to_string Pp.pp_with @@ Serapi.Serapi_protocol.gen_pp_obj Environ.empty_env Evd.empty v))
  |> Option.map (String.concat ",")
  |> Option.get_or ~default:"EMPTY"
  |> fun s -> "result: [" ^ s ^ "]"

let add_and_exec ctx txt =
  add ctx txt;
  exec ctx

let goal ?at (module Ctx: Coq.Proof.PROOF) =
  Ctx.query ?at Serapi.Serapi_protocol.Goals
  |> Option.map @@ List.map (function[@warning "-8"]
    | Serapi.Serapi_protocol.CoqGoal g -> g
  )
  |> function
  | Some (goal :: _) -> goal
  | Some [] -> failwith "failed to obtain goal - serapi returned no remaining goals."
  | None -> failwith "unable to retrieve goal - serapi returned None."

let env ?at (module Ctx: Coq.Proof.PROOF) =
  Ctx.query ?at Serapi.Serapi_protocol.Env
  |> Option.flat_map (fun env ->
    match env with
    |[Serapi.Serapi_protocol.CoqEnv env] -> Some env
    | _ -> None
  )

let ast ?at (module Ctx: Coq.Proof.PROOF)  =
  Ctx.query ?at Serapi.Serapi_protocol.Ast
  |> Option.flat_map (function
    | [Serapi.Serapi_protocol.CoqAst v] -> Some v.v.expr
    | _ -> None
  ) |> Option.get_exn_or "failed to get ast"

let search ?at ctx query =
  let (let+) x f= Option.bind x f in
  let+ env = env ?at ctx  in
  let evd = Evd.from_env env in
  let acc = ref [] in
  Search.search env evd query ([], false) (fun refr kind _ typ ->
    acc := (refr,kind,typ) :: !acc
  );
  Some !acc

let drop_implicits fn params =
  let implicits = Impargs.implicits_of_global (Names.GlobRef.ConstRef fn) in
  List.rev implicits
  |> List.concat_map Fun.(List.rev % snd)
  |> List.filter_map (Option.map (fun ((_, id,_), _, _) -> id))
  |> List.fold_left (fun ls i -> List.remove_at_idx (i - 1) ls) params

let coqobj_to_string v =
  Format.to_string Pp.pp_with @@ Serapi.Serapi_protocol.gen_pp_obj Environ.empty_env Evd.empty v

let typeof ?at (module Ctx: Coq.Proof.PROOF) name =
  Ctx.query ?at Serapi.Serapi_protocol.(TypeOf name)
  |> Option.map (List.map coqobj_to_string)
  |> Option.map (String.concat "; ")
  |> Option.get_or ~default:"NONE"
  |> (fun s -> "[" ^ s ^ "]")
  |> print_endline

let find_spec ?at ctx const =
  search ?at ctx [
    true, Search.(GlobSearchLiteral (GlobSearchString "spec"));
    true, Search.(GlobSearchLiteral
                    (GlobSearchSubPattern (Vernacexpr.InConcl, false, Pattern.PRef (Names.GlobRef.ConstRef const))))
  ] |> function
  | Some [(Names.GlobRef.ConstRef name, _, ty)] -> (name, ty)
  | Some [_] -> failwith "failure finding specification for function application: non-constant name for reference"
  | Some [] -> failwith "failure finding specification for function application: could not find an appropriate specification"
  | Some _ -> failwith "failure finding specification for function application: ambiguity - more than one valid specification found"
  | None -> failwith "internal Coq error: unable to search in context"

let is_pure (prog: [ `Lambda of Lang.Expr.typed_param list * Lang.Expr.t Lang.Program.stmt ]) =
  let rec loop (stmt: Lang.Expr.t Lang.Program.stmt) =
    match stmt with
    | `Match (_, cases) ->
      List.for_all (fun (_, _, body) -> loop body) cases
    | `LetLambda (_, `Lambda (_, body), rest) ->
      loop body && loop rest
    | `EmptyArray -> true
    | `Write _ -> false
    | `Value _ -> true
    | `LetExp (_, _, rest) -> loop rest in
  match prog with
  | `Lambda (_, body) -> loop body

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

  (* Extend.user_symbol *)
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
  let is_wptag const = is_const_named "Wptag" const in
  let is_wp_gen_let_trm const = is_const_named "Wpgen_let_trm" const in
  let is_wp_gen_app const = is_const_named "Wpgen_app" const in

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

  let extract_x_app_fun pre =
    let extract_app_enforce name f n pre =
      match Constr.kind pre with
      | Constr.App (fname, args) when f fname ->
        args.(n)
      | _ ->
        Format.eprintf "failed because unknown structure for %s: %s\n" name (to_string pre);
        failwith "" in
    try
      pre
      |> extract_app_enforce "wptag" is_wptag 0
      |> extract_app_enforce "xlet" is_wp_gen_let_trm 0
      |> extract_app_enforce "wptag" is_wptag 0
      |> extract_app_enforce "xapp" is_wp_gen_app 2
      |> Constr.destConst
      |> fst
    with
      Failure _ -> failwith ("extract_f_app failed because unsupported context: " ^ (to_string pre)) in

  let extract_spec pre =
    let rec loop acc pre = 
      if Constr.isProd pre
      then
        let ({Context.binder_name; _}, ty, pre)  = Constr.destProd pre in
        loop ((binder_name, ty) :: acc) pre
      else List.rev acc, pre in
    loop [] pre in
  let extract_spec pre =
    let rec split acc ls =
      match ls with
      | [] -> (List.rev acc,[])
      | ((name, _) as h) :: t when Names.Name.is_anonymous name ->
        (List.rev acc, h::t)
      | h :: t -> split (h :: acc) t in
    let params, body = extract_spec pre in
    let params, invariants = split [] params in
    (params, invariants, body) in
  begin match pre with
  | `Empty -> ()
  | `NonEmpty ls ->
    let no_pure = List.count (function `Pure _ -> true | _ -> false) ls in
    intro_pure no_pure;
  end;
  let rec loop env (body: Lang.Expr.t Lang.Program.stmt) =
    print_endline @@ Format.sprintf "remaining program is: %a" (Lang.Program.pp_stmt_line Lang.Expr.print) body;
    debug_print_current_goal ();
    (match body with
     | `LetLambda (name, body, rest) ->
       let fname = fresh ~base:name () in
       let h_fname = fresh ~base:("H" ^ name) () in
       add_and_exec ctx (Format.sprintf "xletopaque %s %s." fname h_fname);
       let env = StringMap.add name body env in
       loop env rest
     | `LetExp (pat, body, rest) ->
       begin match body with
       (* pure function application *)
       | `App (_, prog_args)
         when List.exists (function
           |`Var v -> StringMap.find_opt v env |> Option.exists is_pure
           | _ -> false
           ) prog_args ->
         (* work out the name of function being called and the spec for it *)
         let (f_name, raw_spec) =
           (* extract the proof script name for the function being called *)
           let (_, post) = extract_cfml_goal () in
           let f_app = extract_x_app_fun post in
           (* use Coq's searching functionality to work out the spec for the function *)
           find_spec ctx f_app in
         let (params, invariant, spec) = extract_spec raw_spec in

         (* work out the parameters to instantiate *)
         let evar_params =
           params
           (* drop implicits from parameters *)
           |> drop_implicits f_name
           (* drop concrete arguments *)
           |> List.drop (List.length prog_args)
           (* last parameter is the concretisation of the pure function *)
           |> drop_last in

         (* instantiate evars, and collect variables to clear at end *)
         let clear_vars =
           List.fold_left (fun to_clear (name, _) ->
             let name = Format.to_string Pp.pp_with @@ Names.Name.print name in
             let ty = fresh ~base:("ty_" ^ name ) () in
             add_and_exec ctx @@ Printf.sprintf "evar (%s: Type)." ty;
             let name = fresh ~base:name () in
             add_and_exec ctx @@ Printf.sprintf "evar (%s: %s)." name ty;
             to_clear
             |> StringSet.add ty
             |> StringSet.add name
           ) StringSet.empty evar_params in

         let fn_body =
           List.find_map (function `Var v -> StringMap.find_opt v env |> Option.flat_map (Option.if_ is_pure)
                                 | _ -> None) prog_args
           |> Option.get_exn_or "invalid assumptions" in

         let cmd = Printf.sprintf
                               "xapp (%s %s %s %s)."
                               (Names.Constant.to_string f_name)
                               (List.map (Program_generator.Printer.show_expr) prog_args |> String.concat " ")
                               (List.map (fun (name, _) -> "?" ^ Format.to_string Pp.pp_with (Names.Name.print name))
                                  evar_params
                                |> String.concat " ")
                               (Program_generator.Printer.show_lambda fn_body) in
         print_endline @@ Printf.sprintf "sending %s" cmd;
         add_and_exec ctx cmd;

         debug_print_current_goal ();


         List.iter (fun (name, ty) ->
           print_endline @@ Format.sprintf "param %a (%b): %s" Pp.pp_with
                              (Names.Name.print name)
                              (Names.Name.is_anonymous name)
                              (to_string ty)
         ) evar_params;

         (* Search.generic_search env (fun gr _ _ typ ) *)
         (* print_endline @@ Printf.sprintf "got %s (is %b)"  (to_string const) (Constr.isConst const); *)

         failwith "don't know how to handle let bindings"
       | _ ->
         failwith ("TODO: implement handling of let _ = " ^ Format.to_string Lang.Expr.pp body ^ " expressions")
       end
     | `Match _ -> failwith "don't know how to handle matches"
     | `EmptyArray -> failwith "don't know how to handle empty arrays"
     | `Write _ -> failwith "don't know how to handle write"
     | `Value _ -> failwith "don't know how to handle value"
    )
  in
  let env = StringMap.empty in
  ignore @@ loop env prog.body;
  ()


let () =
  (* build alignment between programs *)
  let alignment =
    Dynamic.build_alignment
      ~deps:["../../_build/default/resources/seq_to_array/common.ml"]
      ~old_program
      ~new_program () in

  (* initialise coq ctx *)
  let module Ctx = (val Coq.Proof.make ~verbose:true [
    Coq.Coqlib.make ~path:(Fpath.of_string "../../_build/default/resources/seq_to_array/" |> Result.get_exn) "Proofs"
  ]) in
  Ctx.reset ();
  Ctx.add prelude;
  Ctx.exec ();

  ignore @@ generate alignment (module Ctx) new_program;

