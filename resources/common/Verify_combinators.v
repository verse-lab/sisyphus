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
Arguments while_upto_spec start stop f I HI: rename, clear implicits.

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
           \exists i, \[ start <= i <= stop /\  implb (negb (is_some res)) (i =? stop)] \* I i res).
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
      { intros b; xsimpl*; intros; split; auto; destruct H; try math; auto. }
Qed.
Arguments until_upto_spec {A} {EA} start stop f I Hf : rename.

Lemma for_upto_spec:
  forall (start stop: int) (f: func)
         (I: int -> hprop),
         (forall (i: int),
             start <= i < stop ->
             SPEC (f i)
             PRE (I i)
             POST (fun (_: unit) => I (i + 1))
         ) -> start <= stop ->
   SPEC (for_upto start stop f)
   PRE (I start)
   POST (fun (_: unit) => I stop).
Proof.
  intros start stop f I.
  induction_wf IH: (upto stop) start.
  intros Hf Hlen.
  xcf.
  xlet as;=> cond Hcond.
  xif;=> Hres; rewrite Hcond, istrue_isTrue_eq in Hres.
  - xvals*. subst; xsimpl*. 
  - xif;=> Hlt.
    + xapp (Hf start); [ math | ].
      xapp; try (apply upto_intro; math); auto.
      intros i Hi; apply Hf; math.
      math.
      xsimpl*.
    + xvals*.
      math.
Qed.
Arguments for_upto_spec start stop f I Hf HI: rename, clear implicits.

Lemma while_downto_spec:
  forall (start stop: int) (f: func)
         (I: int -> bool -> hprop),
         (forall (i: int),
             stop < i <= start ->
             SPEC (f i)
             PRE (I i true)
             POST (fun (b: bool) => I (i - 1) b)
         ) -> stop <= start ->
   SPEC (while_downto start stop f)
   PRE (I start true)
   POST (fun (b: bool) => \exists i, \[ stop <= i <= start /\ implb b (i =? stop)] \* I i b).
Proof.
  intros start stop f I.
  induction_wf IH: (downto stop) start.
  intros HI Hlen.
  xcf.
  xlet.
  xif;=> Hcond; rewrite Px0__, istrue_isTrue_eq in Hcond.
  - rewrite Hcond. xval. xsimpl. rewrite Z.eqb_refl; simpl; auto; split; auto; try math.
  - xapp; try  math.
    intros res.
    case_eq res;=> Hres; simpl.
    + xif; [intros []; auto| intros _].
      xapp. { apply downto_intro; math. }
      { intros i Hi; apply HI; math. }
      { math. }
      { intros b; xsimpl*. intros x [H1 H2]; split; auto; math. }
    + xif; [intros _| intros []; auto].
      xvals*; split; auto; math.
Qed.
Arguments while_downto_spec start stop f I HI: rename, clear implicits.

Lemma until_downto_spec:
  forall (A: Type) `{EA: Enc A} (start stop: int) (f: func)
         (I: int -> option A -> hprop),
         (forall (i: int),
             stop < i <= start ->
             SPEC (f i)
             PRE (I i None)
             POST (fun (res: option A) => I (i - 1) res)
         ) -> stop <= start ->
   SPEC (until_downto start stop f)
   PRE (I start None)
   POST (fun (res: option A) =>
           \exists i, \[ stop <= i <= start /\  implb (negb (is_some res)) (i =? stop)] \* I i res).
Proof.
  intros A EA start stop f I.
  induction_wf IH: (downto stop) start.
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
      xapp. { apply downto_intro; math. }
      { intros i Hi; apply HI; math. }
      { math. }
      { intros b; xsimpl*. intros i [H1 H2]; split; auto; math. }
Qed.
Arguments until_downto_spec {A} {EA} start stop f I Hf : rename.

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

Lemma nat_fold_up_spec :
  forall {A: Type} {EA: Enc A} (from: int) (upto: int) (f: func) (init: A)
         (I: int -> A -> hprop),
    (forall (i: int) (a: A), from <= i < upto ->
     SPEC (f i a)
     PRE (I i a)
     POST (fun (res: A) => I (i + 1) res)) ->
    (from <= upto) ->
  SPEC (nat_fold_up from upto f init)
    PRE (I from init)
    POST (fun (res: A) => I upto res).
Proof using.
  intros A EA from up_to f init I  Hf Hvld.
  xcf.
  xlet as;=> tmp Htmp.
  assert (
           forall (i: int) (acc: A),
             from <= i <= up_to ->
             SPEC (tmp i acc)
             PRE (I i acc)
             POST (fun (res: A) => I up_to res)
    ). {
    intros i; induction_wf IH: (upto up_to) i.
    intros acc Hi; apply Htmp; clear Htmp.
    xlet as;=> cond Hcond.
    xif;=> Hcond_vl; rewrite Hcond, istrue_isTrue_eq in Hcond_vl.
    - rewrite Hcond_vl; xvals.
    - xapp (Hf i acc); try math.
      intros res.
      xapp; try apply upto_intro; try math; xsimpl*.
  }
  xapp; auto; try math.
  xsimpl*.
Qed.
Arguments nat_fold_up_spec {A} {EA} from upto f init I Hf HI : rename.

Lemma nat_fold_down_spec :
  forall {A: Type} {EA: Enc A} (from: int) (downto: int) (f: func) (init: A)
         (I: int -> A -> hprop),
    (forall (i: int) (a: A), downto < i <= from ->
     SPEC (f i a)
     PRE (I i a)
     POST (fun (res: A) => I (i - 1) res)) ->
    (downto <= from) ->
  SPEC (nat_fold_down from downto f init)
    PRE (I from init)
    POST (fun (res: A) => I downto res).
Proof using.
  intros A EA from down_to f init I  Hf Hvld.
  xcf.
  xlet as;=> tmp Htmp.
  assert (
           forall (i: int) (acc: A),
             down_to <= i <= from ->
             SPEC (tmp i acc)
             PRE (I i acc)
             POST (fun (res: A) => I down_to res)
    ). {
    intros i; induction_wf IH: (downto down_to) i.
    intros acc Hi; apply Htmp; clear Htmp.
    xlet as;=> cond Hcond.
    xif;=> Hcond_vl; rewrite Hcond, istrue_isTrue_eq in Hcond_vl.
    - rewrite Hcond_vl; xvals.
    - xapp (Hf i acc); try math.
      intros res.
      xapp; try apply downto_intro; try math; xsimpl*.
  }
  xapp; auto; try math.
  xsimpl*.
Qed.
Arguments nat_fold_down_spec {A} {EA} from downto f init I Hf HI : rename.
