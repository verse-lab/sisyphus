Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From ProofsArrayFindi Require Import Common_ml.

Lemma while_upto_spec:
  forall (start stop: int) (f: func)
         (I: int -> bool -> hprop),
         (forall (i: int),
             start <= i < stop ->
             SPEC (f i)
             PRE (I i true)
             POST (fun (b: bool) => I (i + 1) b)
         ) -> start <= stop ->
   SPEC (while_upto start stop f)
   PRE (I start true)
   POST (fun (b: bool) => \exists i, \[i <= stop /\ implb b (i =? stop)] \* I i b).
Proof.
  intros start stop f I.
  induction_wf IH: (upto stop) start.
  intros HI Hlen.
  xcf.
  xlet.
  xif;=> Hcond; rewrite Px0__, istrue_isTrue_eq in Hcond.
  - rewrite Hcond. xval. xsimpl. rewrite Z.eqb_refl; simpl; auto; split; auto; try math.
  - xapp; try  math.
    intros res.
    case_eq res;=> Hres; simpl.
    + xif; [intros []; auto| intros _].
      xapp. { apply upto_intro; math. }
      { intros i Hi; apply HI; math. }
      { math. }
      { intros b; xsimpl*. }
    + xif; [intros _| intros []; auto].
      xvals*; split; auto; math.
Qed.
  
Lemma until_upto_spec:
  forall (A: Type) `{EA: Enc A} (start stop: int) (f: func)
         (I: int -> option A -> hprop),
         (forall (i: int),
             start <= i < stop ->
             SPEC (f i)
             PRE (I i None)
             POST (fun (res: option A) => I (i + 1) res)
         ) -> start <= stop ->
   SPEC (until_upto start stop f)
   PRE (I start None)
   POST (fun (res: option A) =>
           \exists i, \[ i <= stop /\  implb (negb (is_some res)) (i =? stop)] \* I i res).
Proof.
  intros A EA start stop f I.
  induction_wf IH: (upto stop) start.
  intros HI Hlen.
  xcf.
  xlet.
  xif;=> Hcond; rewrite Px0__, istrue_isTrue_eq in Hcond.
  - rewrite Hcond. xval. xsimpl; split; rewrite ?Z.eqb_refl; simpl; auto; try math.
  - xapp; try  math.
    intros res.
    case_eq res; [ intros result Hres| intros Hnone].
    + xmatch. xvals; split; try math; simpl; auto.
    + xmatch.
      xapp. { apply upto_intro; math. }
      { intros i Hi; apply HI; math. }
      { math. }
      { intros b; xsimpl*. }
Qed.

Fixpoint findi (A: Type) (i: int) (f: int -> A -> bool) (ls: list A) : option (int * A) :=
  match ls with
  | nil => None
  | h :: t =>
      if f i h then Some (i, h)
      else findi (i + 1) f t
  end.

Lemma findi_app_r (A: Type) (B: Type) i (f: int -> A -> bool) l1 l2:
  findi i f l1 = None ->
  (findi i f (l1 ++ l2)) = findi (i + length l1) f l2.
Proof.
  gen i l2; induction l1.
  - intros i l2; simpl; rew_list; auto; intros _; repeat f_equal; math.
  - intros i l2; rew_list; simpl.
    case_eq (f i a); intros; simpl; try inversion H0.
    rewrite IHl1; auto.
    f_equal; try math.
Qed.

Lemma findi_app_l (A: Type) i (f: int -> A -> bool) l1 l2:
  is_some (findi i f l1) ->
  (findi i f (l1 ++ l2)) = findi i f l1.
Proof.
  gen i l2; induction l1.
  - intros i l2; simpl; rew_list; intros Hf. inversion Hf.
  - intros i l2; rew_list; simpl.
    case_eq (f i a); intros; simpl. try inversion H0; auto.
    rewrite IHl1; auto.
Qed.



Fixpoint findi_map (A: Type) (B: Type) (i: int) (f: A -> option B) (ls: list A) : option (int * B) :=
  match ls with
  | nil => None
  | h :: t =>
      match f h with
      | Some v => Some (i, v)
      | None => findi_map (i + 1) f t
      end
  end.

Lemma findi_map_app_r (A: Type) (B: Type) i (f: A -> option B) l1 l2:
  findi_map i f l1 = None ->
  (findi_map i f (l1 ++ l2)) = findi_map (i + length l1) f l2.
Proof.
  gen i l2; induction l1.
  - intros i l2; simpl; rew_list; auto; intros _; repeat f_equal; math.
  - intros i l2; rew_list; simpl.
    case_eq (f a); intros; simpl; try inversion H0.
    rewrite IHl1; auto.
    f_equal; try math.
Qed.

Lemma findi_map_app_l (A: Type) (B: Type) i (f: A -> option B) l1 l2:
  is_some (findi_map i f l1) ->
  (findi_map i f (l1 ++ l2)) = findi_map i f l1.
Proof.
  gen i l2; induction l1.
  - intros i l2; simpl; rew_list; intros Hf. inversion Hf.
  - intros i l2; rew_list; simpl.
    case_eq (f a); intros; simpl. try inversion H0; auto.
    rewrite IHl1; auto.
Qed.

Fixpoint find_map (A: Type) (B: Type) (f: A -> option B) (ls: list A) : option (B) :=
  match ls with
  | nil => None
  | h :: t =>
      match f h with
      | Some v => Some (v)
      | None => find_map f t
      end
  end.

Lemma find_map_app_r (A: Type) (B: Type) (f: A -> option B) l1 l2:
  find_map f l1 = None ->
  (find_map f (l1 ++ l2)) = find_map f l2.
Proof.
  gen l2; induction l1.
  - intros l2; simpl; rew_list; auto; intros _; repeat f_equal; math.
  - intros l2; rew_list; simpl.
    case_eq (f a); intros; simpl; try inversion H0.
    rewrite IHl1; auto.
Qed.

Lemma find_map_app_l (A: Type) (B: Type) (f: A -> option B) l1 l2:
  is_some (find_map f l1) ->
  (find_map f (l1 ++ l2)) = find_map f l1.
Proof.
  gen l2; induction l1.
  - intros l2; simpl; rew_list; intros Hf. inversion Hf.
  - intros l2; rew_list; simpl.
    case_eq (f a); intros; simpl. try inversion H0; auto.
    rewrite IHl1; auto.
Qed.


Lemma list_fold_spec : forall A `{EA: Enc A} B `{EB: Enc B}
                              (f: func) (init: B) (l: list A),
  forall (I: list A -> B -> hprop),
  (forall acc v t r, (l = t++v::r) ->
     SPEC (f acc v)
     PRE (I t acc)
     POST (fun acc => I (t&v) acc)) ->
  SPEC (List_ml.fold_left f init l)
    PRE (I nil init)
    POST (fun acc => I l acc).
Proof using.
  intros A EA B EB f init l I f_spec. gen init.
  cuts G: (forall r t init,
              l = t ++ r ->
              SPEC (List_ml.fold_left f init r)
              PRE I t init
              POST (fun acc : B => I l acc)).
  { intros init; applys~ (G l nil init). }
  intros r. induction_wf IH: list_sub r.
  intros t init Ht. xcf.
  xmatch.
  - xvals.
    rewrite Ht. rewrite <- TEMP; rew_list; xsimpl.
  - xapp (f_spec init a t l1); auto. { rewrite Ht. rewrite TEMP. auto. }
    intros acc.
    xapp. rewrite <- TEMP. apply list_sub_cons. { rew_list; try rewrite TEMP; auto. }
    xsimpl.
Qed.
Arguments list_fold_spec {A} {HA} {B} {HB} f init l I Hf : rename.


Lemma list_existsb_app (A: Type) (l1 l2: list A) (fp: A -> bool):
  List.existsb fp (l1 ++ l2) =
    List.existsb fp l1 || List.existsb fp l2.
Proof.
  gen l2; induction l1.
  - intros l2; simpl; rew_list; rewrite if_then_true_else_false; auto.
  - intros l2; rewrite app_cons_l; simpl; rewrite IHl1; simpl.
    case (fp a); simpl; auto.
Qed.



Ltac sep_solve_int := lazymatch goal with
  | [|- forall Y, ?X] => let y := fresh in intros y; sep_solve_int
  | [|- Triple ?Code ?Pre ?Post ] => xgo* 
  | [|- himpl ?X ?Y ] => xgo*
  | [ H: ?X = ?Z |- ?X = ?Y ] => autorewrite with sep_solve_db; auto
  | _ => idtac
  end.
Ltac sep_solve := repeat progress (auto; sep_solve_int).

#[export] Hint Rewrite nil_eq_rev_inv: sep_solve_db.

Ltac done := auto; tryif only 1 : idtac then fail else idtac.
Tactic Notation "by" tactic(t) := t; done.
Tactic Notation "first" tactic(t) := only 1 : t.

Tactic Notation "xdestruct" := xmatch Xcase_as.
Tactic Notation "xdestruct" simple_intropattern(p1) := xmatch Xcase_as; intros p1. 
Tactic Notation "xdestruct"
       simple_intropattern(p1)
       simple_intropattern(p2):= xmatch Xcase_as; intros p1 p2. 
Tactic Notation "xdestruct"
       simple_intropattern(p1)
       simple_intropattern(p2)
       simple_intropattern(p3)
  := xmatch Xcase_as; intros p1 p2 p3.
Tactic Notation "sep_split_tuple"
       hyp(H)
       simple_intropattern(p1)
       simple_intropattern(p2) :=
  inversion H as [[p1 p2]].
Tactic Notation "xalloc"
       simple_intropattern(arr)
       simple_intropattern(data)
       simple_intropattern(Hdata) :=
    xapp; try math; intros arr data Hdata.

Tactic Notation "xpurefun" 
  simple_intropattern(f)
  simple_intropattern(Hf) "using"
  constr(fn) :=
    xlet fn as; (first by sep_solve); intros f Hf.

Tactic Notation "xalloc"
       simple_intropattern(arr)
       simple_intropattern(data)
       simple_intropattern(Hdata) :=
    xapp; try math; intros arr data Hdata.

Tactic Notation "xpullpure"
       simple_intropattern(H1) :=
  xpull; intro H1.
Tactic Notation "xpullpure"
       simple_intropattern(H1)
       simple_intropattern(H2)
  :=
  xpull; intros H1 H2.
Tactic Notation "xpullpure"
       simple_intropattern(H1)
       simple_intropattern(H2)
       simple_intropattern(H3)
  :=
  xpull; intros H1 H2 H3.
Tactic Notation "xpullpure"
       simple_intropattern(H1)
       simple_intropattern(H2)
       simple_intropattern(H3)
       simple_intropattern(H4)
  :=
  xpull; intros H1 H2 H3 H4.
Tactic Notation "xpullpure"
       simple_intropattern(H1)
       simple_intropattern(H2)
       simple_intropattern(H3)
       simple_intropattern(H4)
       simple_intropattern(H5)
  :=
  xpull; intros H1 H2 H3 H4 H5.

Tactic Notation "xmatch_case_0"  :=
  xmatch Xcase_as.
Tactic Notation "xmatch_case_0" "with"
       simple_intropattern(h1)
  :=
  xmatch Xcase_as; intros h1.
Tactic Notation "xmatch_case_0" "with"
       simple_intropattern(h1)
       simple_intropattern(h2) :=
  xmatch Xcase_as; intros h1 h2.

Tactic Notation "xmatch_case_1"  :=
  xmatch Xcase_as; (first sep_solve); intros _.
Tactic Notation "xmatch_case_1" "with"
       simple_intropattern(h1)
  :=
  xmatch Xcase_as; (first sep_solve); intros _ h1.
Tactic Notation "xmatch_case_1" "with"
       simple_intropattern(h1)
       simple_intropattern(h2)
  :=
  xmatch Xcase_as; (first sep_solve); intros _ h1 h2.
Tactic Notation "xmatch_case_1" "with"
       simple_intropattern(h1)
       simple_intropattern(h2)
       simple_intropattern(h3)
  :=
  xmatch Xcase_as; (first sep_solve); intros _ h1 h2 h3.
Tactic Notation "xmatch_case_1" "with"
       simple_intropattern(h1)
       simple_intropattern(h2)
       simple_intropattern(h3)
       simple_intropattern(h4)
  :=
  xmatch Xcase_as; (first sep_solve); intros _ h1 h2 h3 h4.

Tactic Notation "xletopaque"
       simple_intropattern(idx)
       simple_intropattern(Hidx) :=
  xlet as;=> idx Hidx.

Tactic Notation "xvalemptyarr" :=
  xapp; xsimpl.
