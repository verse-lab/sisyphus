Set Implicit Arguments.

Require Import Bool.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.
Require Import Logic.FunctionalExtensionality.

From ProofsListPartition Require Import Verify_list_partition_utils.
From ProofsListPartition Require Import List_partition_old_ml.

Lemma MList_singleton : forall A `{EA: Enc A} (h: A) (r : Common_ml.mut_list_ A),
    r ~>
       (fun r0 : loc =>
        \exists q : loc,
          r0 ~~~> `{ Common_ml.hd' := Some h; Common_ml.tl' := Some q} \*
             q ~~~> `{ Common_ml.hd' := (@None A); Common_ml.tl' := (@None A)})
    =
      (r ~> MList (h :: nil)).
Proof. intros. apply himpl_antisym; xsimpl*. Qed.

Lemma MList_internal_unfold: forall A `{EA: Enc A} (tl: list A) (r: loc),
    r ~> MList_internal tl
      =
     \exists q : option loc,
          match q with
          | Some q0 => q0 ~> MList tl \* r ~~~> `{ Common_ml.hd' := (@None A); Common_ml.tl' := Some q0}
          | None => MList tl r
          end.
Proof. intros. apply himpl_antisym;  unfold MList_internal; rewrite repr_eq; xsimpl*. Qed.

Lemma MList_internal_coerce : forall A `{EA: Enc A} (l: list A) (r: loc),
    (r ~> MList l) ==> (r ~> MList_internal l).
Proof.
  intros.
  case l; [| intros];  simpl;  unfold MList_internal;  rewrite !repr_eq; xsimpl*; instantiate (1:= None); simpl; xsimpl*.
Qed.

Definition MList_tail A `{EA: Enc A} (ls: list A) (lst: loc) (q: option loc) :=
  match q with
  | None => MList_partial nil lst
  | Some q => q ~> MList_partial ls lst
  end.


Fixpoint list_part {A} (p: A -> bool) (l : list A) :=
  match l with
  | nil => (nil, nil)
  | x :: l' =>
      let (tl, fl) := list_part p l' in
      if p x then ((x :: tl), fl) else (tl, (x :: fl))
  end.

Lemma list_partition_spec : forall A `{EA:Enc A} (l:list A) (f: val) (f_p: A -> bool),
    (forall (x :A),
        SPEC_PURE (f x)
        POST (\[= f_p x])
    ) ->
  SPEC (list_partition f l)
    PRE (\[])
    POST (fun '((tl, fl): (list A * list A)) =>
            let (tl', fl') := list_part f_p l in
            \[tl' = tl /\ fl' = fl]).
Proof using.
  intros. xcf; auto.
  xletopaque loop Hloop.
  xapp; intros l_yes. xapp; intros l_no.
  (* naming: true record (tr), head (th) and list (tl), mutatis mutandis for false *)
  asserts Hind : (forall  (r t: list A) (tr fr: Common_ml.mut_list_ A) tl fl tq fq,
                     l = t ++ r ->
                     (let (tl', fl') := list_part f_p t in
                      tl = tl' /\ fl = fl') ->
                          SPEC (loop tr fr r)
                               PRE (( l_yes ~~~> `{ Common_ml.hd':= (@None A);  Common_ml.tl':= tq} \*
                                            MList_tail tl tr tq \*
                                            l_no ~~~> `{ Common_ml.hd':= (@None A);  Common_ml.tl':= fq} \*
                                            MList_tail fl fr fq))

                               POST (fun _ : unit  =>
                                       \exists tr' fr' ,
                                       let (tl', fl') := list_part f_p l in
                                        l_yes ~~~> `{ Common_ml.hd':= (@None A);  Common_ml.tl':= tq} \*
                                            MList_tail tl' tr' tq \*
                                            l_no ~~~> `{ Common_ml.hd':= (@None A);  Common_ml.tl':= fq} \*
                                            MList_tail fl' fr' fq)
                 ). {
    admit.
  }
  xapp Hloop.
  xmatch.
  + xvals. admit.
  + xapp; intros r. xapp (H h). xif; => Hpred.
    rewrite (@MList_eq_nil l_yes). xpull; intros. xapp. rewrite !repr_eq. xpull. intros.
    asserts Hlist : ((r ~~~> `{ Common_ml.hd' := Some h; Common_ml.tl' := Some x} \*
         x ~~~> `{ Common_ml.hd' := (@None A); Common_ml.tl' := (@None A)})
                    =
                      MList_tail (h :: nil) r (Some r)
                    ). { admit.  }
    rewrite hstar_comm.  rewrite <- hstar_assoc.
    rewrite Hlist.

    intros r. induction_wf IH: list_sub r; intros. apply Hloop.
    xmatch.
    + xvals. rew_list in H0. rewrite H0.
      destruct (list_part f_p t) as [tl' fl']. destruct H1 as [Htl Hfl]; rewrite Htl, Hfl. xsimpl*.
      rewrite MList_internal_unfold. evar (q : option loc). xsimpl*.  instantiate (1:= q). case q.
      ++ intros. rewrite MList_partial_is_MList.
      rewrite <- MList_partial_is_MList.
    + xapp; intros r. xapp. xif ;=> Hpred.
      +++ rewrite MList_internal_unfold. xpull. rewrite MList_internal_unfold. xpull.
          intros [q'| ]; intros [p' | ].
      * xapp. rewrite (repr_eq _ r).
        asserts Hq : (\exists q : loc,
         r ~~~> `{ Common_ml.hd' := Some h; Common_ml.tl' := Some q} \*
           q ~~~> `{ Common_ml.hd' := (@None A); Common_ml.tl' := (@None (Common_ml.mut_list_ A))} =
           r ~> MList (h :: nil)
                  ). { apply himpl_antisym; simpl; rewrite repr_eq; xsimpl*.  }
        rewrite Hq. clear Hq.

        asserts Hfr : ( p' ~> MList fl \* fr ~~~> `{ Common_ml.hd' := (@None A); Common_ml.tl' := Some p'}
                        =
                          fr ~> MList_internal fl
                      ). { admit. }
        rewrite Hfr; clear Hfr.
        xchange MList_internal_coerce. xchange MList_internal_coerce. xapp (IH h :: t0)
             ** auto.
             ** instantiate (1:=t & h). rew_list. apply H0.
             **
             **
               +++ rewrite !MList_eq. xapp. rewrite <- !MList_eq. xapp.





  }
