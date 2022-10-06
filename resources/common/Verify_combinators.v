Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Combinators_ml.

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


Lemma for_downto_spec : forall (from: int) (down_to: int) (f: func),
  forall (I: int -> hprop),
    (from >= down_to - 1) ->
    (forall i, down_to <= i <= from ->
     SPEC (f i)
     PRE (I i)
     POST (fun (_: unit) => I (i - 1))) ->
  SPEC (for_downto from down_to f)
    PRE (I from)
    POST (fun (_: unit) => I (down_to - 1)).
Proof using.
  intros from down_to.
  induction_wf IH: (downto down_to) from.
  intros f I Hvld HI.
  xcf. 
  xif.
  - rewrite Px0__, istrue_isTrue_eq; intros ->.  
    xapp (HI down_to); try math.
    xsimpl*.
  - rewrite Px0__, istrue_isTrue_eq; intros Hneq.
    xif; try math.
    + intros Hgt.
      xapp (HI from); try math.
      xapp (IH (from - 1)); try (apply downto_intro; try math); try math; auto.
      * intros i Hi; apply HI; math.
      * xsimpl*.
    + intros Hgt.
      assert (H: from = down_to - 1) by math.
      rewrite H.
      xvals*.
Qed.
Arguments for_downto_spec from down_to f I Hf HI : rename, clear implicits.

