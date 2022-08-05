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
  | None => \[ls = (@nil A)]
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
                                       \exists tr' fr' l_yes_tail l_no_tail,
                                       let (tl', fl') := list_part f_p l in
                                        l_yes ~~~> `{ Common_ml.hd':= (@None A);  Common_ml.tl':= Some l_yes_tail} \*
                                            MList_tail tl' tr' (Some l_yes_tail) \*
                                            l_no ~~~> `{ Common_ml.hd':= (@None A);  Common_ml.tl':= (Some l_no_tail)} \*
                                            MList_tail fl' fr' (Some l_no_tail))
                 ). {
    admit.
  }
  asserts Hpre : (forall tr fr,
                    l_no ~> MList (@nil A) \* l_yes ~> MList (@nil A) =
                    l_yes ~~~> `{ Common_ml.hd' := (@None A); Common_ml.tl' := (@None loc)} \*
                          MList_tail (@nil A) tr (@None loc) \*
                          l_no ~~~> `{ Common_ml.hd' := (@None A); Common_ml.tl' := (@None loc)} \*
                          MList_tail (@nil A) fr (@None loc)). {
    intros. apply himpl_antisym; unfold MList_tail; rewrite !MList_eq_nil; xsimpl*.
  }
  rewrite (Hpre l_yes l_no).
  xapp (Hind).
  + instantiate (1:= nil). rew_list. auto.
  + simpl. eauto.
  + intros tr fr lyt lnt.
    case_eq (list_part f_p l); intros tl fl Hl.
    unfold MList_tail.
    do 2 xchange MList_is_MList_partial.





  }
