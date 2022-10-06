Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Lst_ml.

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

Lemma list_ml_iteri_spec : forall A `{EA: Enc A},
  forall (f:func)  (l: list A) (I: list A -> hprop)  ,
    (forall i x t r, (l = t ++ x :: r) -> i = length t ->
     SPEC (f i x) 
     PRE (I t) 
     POST (fun (unused: unit) => I (t & x))) ->  
  SPEC (List_ml.iteri f l)
    PRE (I nil)
    POST (fun (unused: unit) => I l).
Proof using.
  =>> Hf; xcf.
  xlet as;=> tmp Htmp.

  assert (tmp_spec:
  forall  (i: int) (r t: list A),
    l = t ++ r ->
    i = length t ->
    SPEC (tmp i r)
      PRE (I t)
      POSTUNIT (I l)). {
    introv Hl0 Hlen.
    gen r t. induction_wf IH: (upto (length l)) i.
    intros r t Hl Hi.
    apply Htmp; clear Htmp.
    xmatch.
    - xvals.
      rew_list in Hl; rewrite Hl; xsimpl.
    - xapp (Hf i a t l1); auto.
      xapp; try xsimpl; rew_list; try apply upto_intro; try math.
      rewrite Hl; rew_list; math.
      auto.
  }
  xapp (tmp_spec 0 l); auto; try xsimpl; rew_list; try math.
Qed.
Arguments list_ml_iteri_spec {A} {HA} f s l I Hf : rename.

Lemma hd_spec: forall (A: Type) `{EA: Enc A} `{IA: Inhab A} (ls: list A),
    length ls > 0 ->
    SPEC_PURE (hd ls)
      POST (fun (a: A) => \[a = ls[0]]).
Proof.
  intros A EA IA ls Hls.
  xcf.
  xmatch.
  - rew_list in Hls; math.
  - xvals. rew_list; auto.
Qed.    

Lemma tl_spec: forall (A: Type) `{EA: Enc A} (ls: list A),
    length ls > 0 ->
    SPEC_PURE (tl ls)
      POST (fun (ls': list A) => \[ls' = drop 1 ls]).
Proof.
  intros A EA ls Hls.
  xcf.
  xmatch.
  - rew_list in Hls; math.
  - xvals. rew_list; auto.
Qed.    

