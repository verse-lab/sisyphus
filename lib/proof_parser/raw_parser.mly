%{


open Proof
%}


%token<Command.t> DIRECTIVE                  "(* ... *)"
%token<string> COQ_PROOF                     "{...}"
%token<string> SEMI_WITH_COQ_PROOF           ";{...}"


%token LET                                  "let"
%token BIND                                 ":="
%token EQ                                   "="

%token PROOF_DASH_OR_SUB                     "-"
%token CONS                                  "::"
%token APPEND                                "++"
%token ADD                                   "+"
%token PURE_LBRACE                           "\\["
%token PURE_LBRACE_EQ                        "\\[="
%token IMPLICIT_LBRACE                       "`{"
%token IMPLICIT_RBRACE                       "}"
%token LPAREN                                "("
%token RPAREN                                ")"
%token LSQBRACE                              "["
%token RSQBRACE                              "]"
%token FULL_STOP                             "."
%token COLON                                 ":"
%token COMMA                                 ","

%token<int>     INT                          "NUM"
%token<string> IDENT                         "VAR"
%token LEMMA                                 "Lemma"
%token PROOF_USING                           "Proof using"
%token QED                                   "Qed"

%token FORALL                                "forall"


%token SPEC                                  "SPEC"
%token SPEC_PURE                             "SPEC_PURE"
%token PRE                                   "PRE"
%token POST                                  "POST"
%token FUN                                   "fun"
%token ARROW                                 "=>"
%token SEP                                   "\\*"
%token PTS                                   "~>"



%token<string list> INTROS                   "intros"
%token APPLY                                 "apply"
%token IN                                    "in"
%token<(string * string list list)> CASE_EQ  "case_eq"
%token REWRITE                               "rewrite"
%token STAR                                  "*"

%token XCF                                   "xcf"
%token XPULL                                 "xpull"
%token XAPP                                  "xapp"
%token XMATCH                                "xmatch"
%token XLET                                  "xlet"
%token XSEQ                                  "xseq"
%token XVALS                                 "xvals"
%token XSIMPL                                "xsimpl"

%token EOF                                   "$$"

%left "+" "-" "++" "::" "in" "="


%start <Proof.t> proof

%%

directive : DIRECTIVE "." { $1 }

proof : list(directive) theorem=theorem proof = theorem_proof EOF { Proof.{theorem with directives= $1; proof} }

function_application : fname=IDENT args=list(parenthesized_pure_expression) {(fname, args)}

base_ty: list(IDENT) { Type $1 }

ty:
  | base_ty { $1 }
  | t1= base_ty "*" t2=ty { Prod ([t1; t2]) }
  | "(" ty = ty ")" { ty }

param :
| "`{" id = IDENT ":" ty=ty "}" { Implicit (id, ty) }
| "(" id = IDENT ":" ty=ty ")" { Explicit (id, ty) }
| IDENT { Ident $1 }

pure_expression :
    | var=IDENT { Var var }
    | num=INT   { Int num }
    | fname=IDENT args=nonempty_list(parenthesized_pure_expression) { Predicate (fname, args) }
    | e1 = pure_expression; "="; e2 = pure_expression { Eq (e1,e2) }
    | e1 = pure_expression; "::"; e2 = pure_expression { Cons (e1,e2) }
    | e1 = pure_expression; "++"; e2 = pure_expression { Append (e1,e2) }
    | e1 = pure_expression; "+"; e2 = pure_expression { Add (e1,e2) }
    | e1 = pure_expression; "-"; e2 = pure_expression { Sub (e1,e2) }
    | "let" "(" i1=IDENT "," i2 = IDENT ")" ":=" pair=IDENT "in" body=pure_expression
     { DestructurePair (i1, i2, pair, body)}
    | "(" e1 = pure_expression "," rest = separated_nonempty_list(",", pure_expression) ")" { Tuple (e1 :: rest) }
    | "(" expr = pure_expression ")" { expr }
    | "(" "fun" params=nonempty_list(param) "=>" body=coq_expression ")"
    { Lambda (params, body) }

parenthesized_pure_expression:
    | var=IDENT { Var var }
    | "(" expr = pure_expression ")" { expr }
    | "(" "fun" params=nonempty_list(param) "=>" body=coq_expression ")"
    { Lambda (params, body) }
    | "(" e1 = pure_expression "," rest = separated_nonempty_list(",", pure_expression) ")" { Tuple (e1 :: rest) }

assertion :
    | "\\[" exp = pure_expression "]" { Pure exp }
    | ptr=IDENT "~>" body=pure_expression { Spatial (PointsTo (ptr,body)) }


sep_spec : separated_nonempty_list("\\*", assertion) { $1 }
    
coq_expression :
    | sep_spec { HeapSpec $1  }
    | pure_expression { FunctionalSpec $1  }

theorem :
  "Lemma" name=IDENT ":" "forall" formal_params=list(param) ","
        "SPEC" "(" spec=function_application ")"
        "PRE" "(" pre = sep_spec ")"
        "POST" "(" "fun" post_arg = param "=>" post_spec = sep_spec  ")" "."
 {
        Proof.{directives=[]; name; formal_params; spec; pre; post=(post_arg, post_spec); proof=([]: proof_step list)}
}

proof_case :
    | "-" steps=list(proof_step) { steps }

let_spec:
    | "(" "fun" p=param "=>" "forall" formals=nonempty_list(param) ","
              "SPEC_PURE" "(" fapp = function_application ")"
              "POST" "\\[=" res = pure_expression "]" ")"
    { (p,formals, fapp, res) }

proof_step :
    | "xcf" "." { Xcf }
    | "xpull" extra=list(";{...}") "." { Xpull extra }
    | "xapp" inv=option(pure_expression) extra=list(";{...}") "." oblig=list("{...}") { Xapp (inv, extra, oblig)}
    | "xmatch" extra=list(";{...}") "." oblig=list("{...}") { Xmatch (extra, oblig) }
    | "xlet" spec=option(let_spec) extra=list(";{...}") "." oblig=list("{...}") { Xlet(spec, extra, oblig) }
    | "xseq" "." { Xseq }
    | "xvals" "." oblig=list("{...}") { Xvals oblig}
    | "intros" "." { Intros $1 }
    | "xsimpl" "." { Xsimpl }

proof_split: case="case_eq" extra=list(";{...}") "." cases=list(proof_case) { CaseEq (case, extra, cases) }

proof_script : steps=list(proof_step) last=option(proof_split)  { steps @ Option.to_list last }

theorem_proof:
  "Proof using" "."
  ps = proof_script
  "Qed" "." { ps }
