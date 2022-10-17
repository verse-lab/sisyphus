Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Utils Arr_ml.

Lemma array_iter_spec :
  forall A `{EA: Enc A} (f: func) (a: array A) (l: list A),
  forall (I: list A -> hprop),
  (forall v (t r: list A),
      (l = t++v::r) ->
     SPEC (f v)
     PRE (I t)
     POST (fun (_: unit) => I (t&v))) ->
  SPEC (array_iter f a)
    PRE (a ~> Array l \* I nil)
    POST (fun (_: unit) => a ~> Array l \* I l).
Proof using.
  intros A EA f a l I f_spec.
  xcf.
  xapp.
  xlet as;=> loop Hloop.
  assert (Hloop_spec: forall i (t r: list A),
             l = t ++ r ->
             i = LibListZ.length t ->
             SPEC (loop i)
               PRE (I t \* a ~> Array l)
               POST (fun (_: unit) => I l  \* a ~> Array l)
         ). {
    intros i; induction_wf IH: (upto (LibListZ.length l)) i.
    intros t r Hl Hi; apply Hloop; clear Hloop.
    assert (Higt0: 0 <= i) by (rewrite Hi; apply length_nonneg).
    xif;=> Hivl.
    - assert (IA: Inhab A). {
        destruct l; [rew_list in Hivl; math |].
        exact (Inhab_of_val a0).
      }
      xapp; [apply int_index_prove; try math | ].
      assert (Hl_eq: l = t ++ l[i] :: drop 1 r). {
        rewrite Hl; repeat f_equal.
        rewrite read_app, If_r; try math; rewrite Hi, minus_self.
        apply (eq_of_extens IA).
        - rew_list;
          rewrite ?length_drop; try math;
          rewrite Hl in Hivl; rew_list in Hivl; math.
        - intros j. rewrite index_eq_index_length, int_index_eq.
          intros Hlen. rewrite read_cons_case.
          case (Z.eqb_spec j 0); intros Hj;
            [rewrite If_l, Hj| rewrite If_r]; auto.
          rewrite read_drop; f_equal; try apply int_index_prove; math.
      }
      xapp (f_spec l[i] t (drop 1 r)); auto.
      xapp (IH (i + 1)).
      * apply upto_intro; try math.
      * rewrite app_last_l; apply Hl_eq.
      * rew_list; math.
      * xsimpl*.
    - xvals*. {
        cut (t = l). {
          intros ->; xsimpl*.
        }
        assert (HI: i >= LibListZ.length l) by math.
        rewrite Hl, Hi in HI; rew_list in HI.
        assert (LibListZ.length r = 0) by math.
        rewrite Hl, (length_zero_inv r); rew_list; auto.
      }
  }
  xapp (Hloop_spec (0) (nil) (l)); rew_list; auto.
  xsimpl*.
Qed.
Arguments array_iter_spec {A} {EA} f a l I Hf : rename.


Lemma array_take_spec :
  forall {A} `{EA: Enc A} (i: int) (a: array A) (l: list A), 0 <= i ->
  SPEC (array_take i a)
    PRE (a ~> Array l)
    POST (fun (arr: loc) => a ~> Array l \* arr ~> Array (take i l)).
Proof using.
  intros.
  xcf.
  xapp.
  xif;=> Hcond.
  - rewrite Px0__, istrue_isTrue_eq in Hcond; apply length_zero_inv in Hcond; rewrite Hcond, take_nil.
    xapp*;=> arr.
    xsimpl*.
  - rewrite Px0__, istrue_isTrue_eq in Hcond.
    assert (IA: Inhab A). {
      destruct l; rew_list in Hcond; try math.
      apply Inhab_of_val; auto.
    }
    xif;=> Hltn.
    + xval.
      xapp. { apply int_index_prove; try math. }
      xapp; try math; intros arr data Hdata.
      xapp;=> pos.
      xlet as;=> tmp Htmp.
      xapp (array_iter_spec tmp a l
              (fun (t: list A) =>
                  arr ~> Array (take i t ++ drop (length (take i t)) data) \*
                  pos ~~> length t
           )). {
        intros v t r Hvtr. apply Htmp; clear Htmp.
        xapp.
        xif;=> Htmp_cond.
        - xapp. {
            apply int_index_prove; try math.
            rewrite <- length_eq; rew_list.
            rewrite take_ge; try math.
            rewrite length_drop_nonneg; rewrite Hdata, length_make; try math.
          }
          xsimpl*; rew_list; try math.
          rewrite take_ge; try math.
          rewrite (@update_app_r _ _ 0 _ (length t)); auto; try math.
          rewrite take_ge; rew_list; try math.
          f_equal.
          apply (eq_of_extens IA).
          + rew_list; rewrite length_update, Hdata, ?length_drop_nonneg; rewrite ?length_make; try math.
          + intros j. rewrite index_eq_index_length, int_index_eq.
            rewrite length_update, length_drop_nonneg; rewrite Hdata, length_make; try math.
            intros Hlen. rewrite read_cons_case.
          case (Z.eqb_spec j 0); intros Hj;
            [rewrite If_l, Hj| rewrite If_r]; auto.
          rewrite read_update_same; auto; try apply int_index_prove; try math.
          rewrite <- length_eq, length_drop_nonneg; rewrite length_make; try math.
          rewrite read_update_neq, !read_drop; auto; try (f_equal; math).
          rewrite length_make; math.
          rewrite length_make; math.
          apply int_index_prove; try math.
          rewrite <- length_eq,  length_drop_nonneg, length_make; try math.
          rewrite length_make; math.
        - xvals*; rew_list; try math.
          rewrite length_take_nonneg; try math.
          rewrite length_take_nonneg; rew_list; try math.
          rewrite take_app_l; auto; try math.
      }
      rewrite take_nil, length_nil, drop_zero, app_nil_l; auto.
      xvals*.
      rewrite length_take_nonneg; try math.
      rewrite <- app_nil_r, Hdata; f_equal.
      rewrite <- (@length_make _ i l[0]) at 1; try math.
      rewrite drop_at_length; auto.
    + xval.
      xapp. { apply int_index_prove; try math. }
      xapp; try math; intros arr data Hdata.
      xapp;=> pos.
      xlet as;=> tmp Htmp.
      xapp (array_iter_spec tmp a l
              (fun (t: list A) =>
                  arr ~> Array (take i t ++ drop (length (take i t)) data) \*
                  pos ~~> length t
           )). {
        intros v t r Hvtr. apply Htmp; clear Htmp.
        xapp.
        xif;=> Htmp_cond.
        - xapp. {
            apply int_index_prove; try math.
            rewrite <- length_eq; rew_list.
            rewrite take_ge; try math.
            rewrite length_drop_nonneg; rewrite Hdata, length_make; try math.
          }
          xsimpl*; rew_list; try math.
          rewrite take_ge; try math.
          rewrite (@update_app_r _ _ 0 _ (length t)); auto; try math.
          rewrite take_ge; rew_list; try math.
          f_equal.
          apply (eq_of_extens IA).
          + rew_list; rewrite length_update, Hdata, ?length_drop_nonneg; rewrite ?length_make; try math.
          + intros j. rewrite index_eq_index_length, int_index_eq.
            rewrite length_update, length_drop_nonneg; rewrite Hdata, length_make; try math.
            intros Hlen. rewrite read_cons_case.
          case (Z.eqb_spec j 0); intros Hj;
            [rewrite If_l, Hj| rewrite If_r]; auto.
          rewrite read_update_same; auto; try apply int_index_prove; try math.
          rewrite <- length_eq, length_drop_nonneg; rewrite length_make; try math.
          rewrite read_update_neq, !read_drop; auto; try (f_equal; math).
          rewrite length_make; math.
          rewrite length_make; math.
          apply int_index_prove; try math.
          rewrite <- length_eq,  length_drop_nonneg, length_make; try math.
          rewrite length_make; math.
        - xvals*; rew_list; try math.
          assert (i >= length l) by math.
          assert (length l > length t) by (rewrite Hvtr; rew_list; try math).
          assert (i >= length t) by math.
          rewrite take_ge; try math.
      }
      rewrite take_nil, length_nil, drop_zero, app_nil_l; auto.
      xvals*.
      rewrite take_ge; try math.
      rewrite Hdata.
      rewrite <- (@length_make _ (length l) l[0]) at 1; try math.
      rewrite drop_at_length, app_nil_r; auto.
Qed.
Arguments array_take_spec {A} {EA} i a l Hi.
#[export] Hint Extern 1 (RegisterSpec array_take) => Provide array_take_spec.

Lemma array_iteri_spec :
  forall A `{EA: Enc A} (f: func) (a: array A),
  forall (I: list A -> hprop) (l: list A),
    (forall i v (t r: list A),
        i = length t ->
        (l = t++v::r) ->
        SPEC (f i v)
          PRE (I t)
          POST (fun (_: unit) => I (t&v))) ->
  SPEC (array_iteri f a)
    PRE (a ~> Array l \* I nil)
    POST (fun (_: unit) => a ~> Array l \* I l).
Proof using.
  xcf.
  xapp.
  xlet as;=> tmp Htmp.
  assert (forall i t r,
             i = length t ->
             l = t ++ r ->
             SPEC (tmp i)
               PRE (a ~> Array l \* I t)
               POST (fun _ : unit => a ~> Array l \* I l)
         ). {
    intros i; induction_wf IH: (upto (length l)) i.
    intros t r Hi Htr; apply Htmp; clear Htmp.
    xif;=> Hlen.
    - assert (length l > 0). { destruct l; rew_list in *; math. }
      assert (Inhab A). {
        destruct l; rew_list in *; try math; apply Inhab_of_val; auto.
      }
      xapp. { apply int_index_prove; rewrite <- ?length_eq; math. }
      destruct r as [| rh rt]; rew_list in *; simpl.
      + subst; math.
      + xapp (H i l[i] t rt); auto. {
          subst; rewrite read_app, If_r; try math.
          math_rewrite (length t - length t = 0).
          rewrite read_zero; auto.
        } {
          xapp (IH (i + 1)).
          apply upto_intro; math.
          rew_list; math.
          subst; rewrite read_app, If_r; try math.
          math_rewrite (length t - length t = 0).
          rewrite read_zero; auto.
          rew_list; f_equal.
          xsimpl*.
        }
    - xvals*.
      subst; rew_list in *.
      assert (length r = 0) by math.
      apply length_zero_inv in H0; rewrite H0; rew_list; xsimpl*.
  }
  xapp; rew_list; auto; xsimpl*.
Qed.
Arguments array_iteri_spec {A} {EA} f a I l HI.

Lemma array_to_list_spec :
  forall {A} `{EA: Enc A} (a: array A) (l: list A),
  SPEC (Array_ml.to_list a)
    PRE (a ~> Array l)
    POST (fun (ls: list A) => \[ls = l] \* a ~> Array l).
Proof using.
  xcf.
  xlet as;=> tmp Htmp.
  assert (forall (i: int) (acc: list A),
             -1 <= i < length l ->
             (acc = drop (i + 1) l) ->
             SPEC (tmp i acc)
             PRE (a ~> Array l)
             POST (fun (res: list A) => \[res = l] \* a ~> Array l)
         ). {
    intros i; induction_wf IH: (downto (-1)) i. 
    intros acc Hi Hacc; apply Htmp; clear Htmp.
    xif;=> cond.
    - xvals. { rewrite drop_neg in Hacc; subst; try math; auto.  }
    - assert (IA: Inhab A). {
        apply Inhab_of_val; destruct l as [| l ls]; rew_list in *; try math; auto.
      }
      xapp. { apply int_index_prove; math. }
      xapp (IH (i - 1)).
      + apply downto_intro; math.
      + math.
      + rewrite Hacc.
        math_rewrite (i - 1 + 1 = i).
        rewrite (@list_split_ith _ IA l i) at 3; try math.
        rewrite drop_app_l; rew_list; try (rewrite length_take_nonneg; math).
        rewrite drop_app_l; rew_list; try (rewrite length_take_nonneg; math).
        assert (Hil: i = length (take i l)) by (rewrite length_take_nonneg; math).
        rewrite Hil at 3; rewrite drop_at_length; rew_list; auto.
      + xsimpl*.
  }
  xapp.
  xapp. {
    math.
  } {
    math_rewrite (length l - 1 + 1 = length l); rewrite drop_at_length; auto.
  } {
    xsimpl*.
  }
Qed.
Arguments array_to_list_spec {A} {EA} a l.
#[export] Hint Extern 1 (RegisterSpec Array_ml.to_list) => Provide array_to_list_spec.

