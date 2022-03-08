%{


open Proof
%}


%token<Command.t> DIRECTIVE                  "(* ... *)"
%token<string> COQ_PROOF                     "{...}"
%token<string> SEMI_WITH_COQ_PROOF           ";{...}"

%token FUN                                   "fun"
%token ARROW                                 "=>"

%token HOLE                                  "(??)"

%token EQ                                    "="

%token PROOF_DASH_OR_SUB                     "-"
%token CONS                                  "::"
%token APPEND                                "++"
%token ADD                                   "+"
%token PURE_LBRACE                           "\\["
%token DESTRUCT_PAREN                        "'("
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
%token ADMITTED                              "Admitted"

%token FORALL                                "forall"


%token SPEC                                  "SPEC"
%token PRE                                   "PRE"
%token POST                                  "POST"
%token SEP                                   "\\*"
%token PTS                                   "~>"


%token STAR                                  "*"

%token XCF                                   "xcf"
%token XPULLPURE                             "xpullpure"

%token XPUREFUN                              "xpurefun"
%token USING                                 "using"

%token XAPP                                  "xapp"
%token XDESTRUCT                             "xdestruct"

%token REWRITE                               "rewrite"
%token IN                                    "in"

%token SEP_SPLIT_TUPLE                       "sep_split_tuple"

%token <int>XMATCH_CASE_N                    "xmatch_case_n"
%token WITH                                  "with"

%token XVALEMPTYARR                          "xvalemptyarr"
%token XALLOC                                "xalloc"
%token XLETOPAQUE                            "xletopaque"
%token INTROS                                "intros"
%token XVALS                                 "xvals"

%token CASE                                  "case"
%token AS                                    "as"
%token BAR                                   "|"
%token EQN                                   "eqn:"

%token EOF                                   "$$"

%left "+" "-" "++" "::" "="


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
| "'(" "(" ids = separated_nonempty_list(",", IDENT) ")" ":" ty=ty ")" { TupleParam (ids, ty)  }

pure_expression :
    | var=IDENT { Var var }
    | num=INT   { Int num }
    | fname=IDENT args=nonempty_list(parenthesized_pure_expression) { Predicate (fname, args) }
    | e1 = pure_expression; "="; e2 = pure_expression { Eq (e1,e2) }
    | e1 = pure_expression; "::"; e2 = pure_expression { Cons (e1,e2) }
    | e1 = pure_expression; "++"; e2 = pure_expression { Append (e1,e2) }
    | e1 = pure_expression; "+"; e2 = pure_expression { Add (e1,e2) }
    | e1 = pure_expression; "-"; e2 = pure_expression { Sub (e1,e2) }
    | "(" e1 = pure_expression "," rest = separated_nonempty_list(",", pure_expression) ")" { Tuple (e1 :: rest) }
    | "(" expr = pure_expression ")" { expr }


parenthesized_pure_expression:
    | var=IDENT { Var var }
    | "(" expr = pure_expression ")" { expr }
    | "(" e1 = pure_expression "," rest = separated_nonempty_list(",", pure_expression) ")" { Tuple (e1 :: rest) }

assertion :
    | "\\[" "]" { Emp }
    | "\\[" exp = pure_expression "]" { Pure exp }
    | ptr=IDENT "~>" body=pure_expression { Spatial (PointsTo (ptr,body)) }

lambda: | "(" "fun" params=nonempty_list(param) "=>" body=coq_expression ")"
    { Lambda (params, body) }

spec_arg :
    | parenthesized_pure_expression { Pure $1 }
    | lambda                        { $1 }
    | "(??)"                        { Hole }

spec_app : 
 id = IDENT args = nonempty_list(spec_arg) { SpecApp (id, args)}

sep_spec : separated_nonempty_list("\\*", assertion) { $1 }
    
coq_expression :
    | sep_spec { HeapSpec $1  }
    | pure_expression { FunctionalSpec $1  }

spec : "forall" formal_params=list(param) ","
        "SPEC" "(" fapp=function_application ")"
        "PRE" "(" pre = sep_spec ")"
        "POST" "(" "fun" post_arg = param "=>" post_spec = sep_spec  ")" 
{ Spec (formal_params, fapp, pre, post_arg, post_spec) }

theorem :
  "Lemma" name=IDENT ":" spec=spec "."
 {
        Proof.{directives=[]; name; spec; proof=([]: proof_step list)}
}

proof_case :
    | "-" steps=list(proof_step) { steps }

proof_step :
    | "xcf" "." { Xcf }
    | "xpullpure" ids=nonempty_list(IDENT) "." { Xpullpure ids }
    | "xpurefun" f=IDENT hf=IDENT "using" "(" "fun" "(" fn = IDENT ":" ty=ty ")" "=>" s=spec ")" "."
     { Xpurefun (f, hf, (fn, ty), s) }
    | "xapp" "(" sapp = spec_app ")" extra=list(";{...}") "." oblig=list("{...}") { Xapp (sapp, extra, oblig) }
    | "xdestruct" ids=list(IDENT) "." { Xdestruct ids }
    | "rewrite" lemma=IDENT "in" hyp=IDENT "." { Rewrite (lemma, hyp) }
    | "sep_split_tuple" ids=nonempty_list(IDENT) "." { SepSplitTuple ids }
    | "xmatch_case_n" "." { Xmatchcase ($1, []) }
    | "xmatch_case_n" "with" ids=nonempty_list(IDENT) "." { Xmatchcase ($1, ids) }
    | "xvalemptyarr" "." { Xvalemptyarr }
    | "xalloc" arr=IDENT data=IDENT harr=IDENT "." { Xalloc (arr,data,harr) }
    | "xletopaque" sym=IDENT hsym=IDENT "." { Xletopaque (sym, hsym) }
    | "intros" ids=list(IDENT) "." { Intros ids }
    | "xvals" "." oblig=list("{...}") { Xvals oblig}

proof_split: "case" vl = IDENT "as" "[" cases=separated_nonempty_list("|", list(IDENT)) "]" "eqn:" h=IDENT "." 
proofs_cases=list(proof_case)
{ Case (vl, h, cases, proofs_cases) }

proof_script : steps=list(proof_step) last=option(proof_split)  { steps @ Option.to_list last }

terminator: "Qed" { () }
 | "Admitted" { () }

theorem_proof:
  "Proof using" "."
  ps = proof_script
  terminator "." { ps }
