open Containers
open Expr
module StringMap = Map.Make(String)

type ctx = Z3.Expr.expr StringMap.t
  
let rec eval_expr (ctx: ctx) : Expr.expr -> Z3.Expr.expr = function
  | Var var -> StringMap.find var ctx
  | ListExpr lexp -> eval_list_expr ctx lexp
  | IntExpr iexp -> eval_int_expr ctx iexp
  | BoolExpr bexp -> eval_bool_expr ctx bexp
and eval_list_expr ctx = function
  | ListVar var -> StringMap.find var ctx
  | Nil -> Logic.List.nil
  | AppList ("cons", [hd;tl]) ->
    Logic.List.cons (eval_expr ctx hd) (eval_expr ctx tl)
  | AppList ("tail", [ls]) -> Logic.List.tail (eval_expr ctx ls)
  | AppList ("head", [ls]) -> Logic.List.head (eval_expr ctx ls)
  | AppList ("rcons", [ls; x]) -> Logic.List.rcons (eval_expr ctx ls) (eval_expr ctx x)
  | AppList ("append", [ls1; ls2]) -> Logic.List.append (eval_expr ctx ls1) (eval_expr ctx ls2)
  | AppList ("repeat", [len; vl]) -> Logic.List.repeat (eval_expr ctx len) (eval_expr ctx vl)
  | AppList ("rev", [ls]) -> Logic.List.rev (eval_expr ctx ls)
  | AppList ("drop", [len; ls]) -> Logic.List.drop (eval_expr ctx len) (eval_expr ctx ls)
  | AppList ("update", [ls; ind; vl]) -> Logic.List.update (eval_expr ctx ls) (eval_expr ctx ind) (eval_expr ctx vl)
  | AppList (fn, _) -> failwith ("unsupported list function" ^ fn)
and eval_int_expr _ctx = function
  | IntVar var -> StringMap.find var _ctx
  | Int i -> Logic.(!* i)
  | Add (l, r) -> Logic.(eval_int_expr _ctx l + eval_int_expr _ctx r)
  | Sub (l, r) -> Logic.(eval_int_expr _ctx l - eval_int_expr _ctx r)
  | AppInt ("length", [ls]) -> Logic.List.length (eval_expr _ctx ls)
  | AppInt (fn, _) -> failwith ("unsupported int function " ^ fn)
and eval_bool_expr _ctx = function
  | BoolVar var -> StringMap.find var _ctx
  | Bool false -> Logic.bool_false | Bool true -> Logic.bool_true
  | Lt (l, r) -> Logic.(eval_int_expr _ctx l < eval_int_expr _ctx r)
  | Le (l, r) -> Logic.(eval_int_expr _ctx l <= eval_int_expr _ctx r)
  | Gt (l, r) -> Logic.(eval_int_expr _ctx l > eval_int_expr _ctx r)
  | Ge (l, r) -> Logic.(eval_int_expr _ctx l >= eval_int_expr _ctx r)
  | IntEq (l, r)  -> Logic.(eval_int_expr _ctx l = eval_int_expr _ctx r)
  | ListEq (l, r) -> Logic.(eval_list_expr _ctx l < eval_list_expr _ctx r)
  | AppBool (fn, _) -> failwith ("unsupported bool function " ^ fn)
