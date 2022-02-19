open Containers

type int_expr =
  | Int of int
  | IntVar of string
  | Add of int_expr * int_expr
  | Sub of int_expr * int_expr
  | AppInt of string * expr list
and list_expr =
  | Nil
  | ListVar of string
  | AppList of string * expr list
and bool_expr =
  | Bool of bool
  | BoolVar of string
  | Lt of int_expr * int_expr
  | Le of int_expr * int_expr
  | Gt of int_expr * int_expr
  | Ge of int_expr * int_expr
  | IntEq of int_expr * int_expr
  | ListEq of list_expr * list_expr
  | AppBool of string * expr list
and expr = ListExpr of list_expr | IntExpr of int_expr | BoolExpr of bool_expr | Var of string
[@@deriving eq]


let rec pp ?(parens=false) fmt = function
  | IntExpr iexp -> pp_int_expr ~parens fmt iexp
  | ListExpr lexp -> pp_list_expr ~parens fmt lexp
  | BoolExpr bexp -> pp_bool_expr ~parens fmt bexp
  | Var str -> Format.pp_print_string fmt str
and pp_int_expr ?(parens=false) fmt = let open Format in
  function
  | Int i -> pp_print_int fmt i
  | IntVar v -> pp_print_string fmt v
  | Add (l,r) ->
    if parens then (pp_open_hvbox fmt 1; pp_print_char fmt '(');
    pp_int_expr ~parens:(not parens) fmt l; pp_print_string fmt " + "; pp_int_expr ~parens:(not parens) fmt r;
    if parens then (pp_print_char fmt ')'; pp_close_box fmt ())
  | Sub (l,r) ->
    if parens then (pp_open_hvbox fmt 1; pp_print_char fmt '(');
    pp_int_expr fmt l; pp_print_string fmt " - "; pp_int_expr fmt r;
    if parens then (pp_print_char fmt ')'; pp_close_box fmt ())
  | AppInt (fn, args) ->
    pp_open_hovbox fmt 2;
    if parens then (pp_print_char fmt '(');
    pp_print_string fmt fn;
    pp_print_space fmt ();
    pp_print_list ~pp_sep:pp_print_space (pp ~parens:true) fmt args;
    if parens then (pp_print_char fmt ')');
    pp_close_box fmt ()
and pp_bool_expr ?(parens=false) fmt = let open Format in
  let pp_lr pp l comb r = 
    if parens then (pp_open_hvbox fmt 1; pp_print_char fmt '(');
    pp ?parens:(Some (not parens)) fmt l; pp_print_string fmt comb; pp ?parens:(Some (not parens)) fmt r;
    if parens then (pp_print_char fmt ')'; pp_close_box fmt ()) in
  function
  | Bool v -> pp_print_bool fmt v
  | BoolVar v -> pp_print_string fmt v
  | Lt (l,r) -> pp_lr pp_int_expr l " < " r
  | Le (l,r) -> pp_lr pp_int_expr l " <= " r
  | Gt (l,r) -> pp_lr pp_int_expr l " > " r
  | Ge (l,r) -> pp_lr pp_int_expr l " >= " r
  | IntEq (l,r) -> pp_lr pp_int_expr l " = " r
  | ListEq (l,r) ->  pp_lr pp_list_expr l " = " r
  | AppBool (fn, args) ->
    pp_open_hovbox fmt 2;
    if parens then (pp_print_char fmt '(');
    pp_print_string fmt fn;
    pp_print_space fmt ();
    pp_print_list ~pp_sep:pp_print_space (pp ~parens:true) fmt args;
    if parens then (pp_print_char fmt ')');
    pp_close_box fmt ()
and pp_list_expr ?(parens=false) fmt = let open Format in
  function
  | Nil -> pp_print_string fmt "[]"
  | ListVar v -> pp_print_string fmt v
  | AppList ("cons", [hd; tl]) ->
    if parens then (pp_open_hvbox fmt 1; pp_print_char fmt '(');
    pp ?parens:(Some (not parens)) fmt hd; pp_print_string fmt " :: "; pp ?parens:(Some (not parens)) fmt tl;
    if parens then (pp_print_char fmt ')'; pp_close_box fmt ())
  | AppList ("rcons", [ls; x]) ->
    if parens then (pp_open_hvbox fmt 1; pp_print_char fmt '(');
    pp ?parens:(Some (not parens)) fmt ls; pp_print_string fmt " & "; pp ?parens:(Some (not parens)) fmt x;
    if parens then (pp_print_char fmt ')'; pp_close_box fmt ())
  | AppList ("append", [l; r]) ->
    if parens then (pp_open_hvbox fmt 1; pp_print_char fmt '(');
    pp ?parens:(Some (not parens)) fmt l; pp_print_string fmt " ++ "; pp ?parens:(Some (not parens)) fmt r;
    if parens then (pp_print_char fmt ')'; pp_close_box fmt ())

  | AppList (fn, args) ->
    pp_open_hovbox fmt 2;
    if parens then (pp_print_char fmt '(');
    pp_print_string fmt fn;
    pp_print_space fmt ();
    pp_print_list ~pp_sep:pp_print_space (pp ~parens:true) fmt args;
    if parens then (pp_print_char fmt ')');
    pp_close_box fmt ()
let show = Format.to_string pp 
let show_int_expr = Format.to_string pp_int_expr
let show_bool_expr = Format.to_string pp_bool_expr
let show_list_expr = Format.to_string pp_list_expr

type ty = IntTy | ListTy | VarTy | BoolTy

let rec contains var : expr -> bool =
  function
    ListExpr lexp -> contains_list_expr var lexp
  | IntExpr iexp -> contains_int_expr var iexp
  | BoolExpr bexp -> contains_bool_expr var bexp
  | Var var' -> String.equal var var'
and contains_list_expr var =
  function Nil -> false
         | ListVar var' -> String.equal var var'
         | AppList (_, args) -> List.exists (contains var) args
and contains_int_expr var =
  function Int _ -> false
         | IntVar var' -> String.equal var var'
         | Add (l, r) -> contains_int_expr var l || contains_int_expr var r
         | Sub (l, r) -> contains_int_expr var l || contains_int_expr var r
         | AppInt (_, args) -> List.exists (contains var) args
and contains_bool_expr var =
  function Bool _ -> false
         | BoolVar var' -> String.equal var var'
         | Lt (l, r) -> contains_int_expr var l || contains_int_expr var r
         | Le (l, r) -> contains_int_expr var l || contains_int_expr var r
         | Gt (l, r) -> contains_int_expr var l || contains_int_expr var r
         | Ge (l, r) -> contains_int_expr var l || contains_int_expr var r
         | IntEq (l, r) -> contains_int_expr var l || contains_int_expr var r
         | ListEq (l, r) -> contains_list_expr var l || contains_list_expr var r
         | AppBool (_, args) -> List.exists (contains var) args
