Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.
Require Import Utils Tactics.

Create HintDb filter_lemmas.
Create HintDb iff_lemmas.

#[export] Hint Resolve length_zero_inv: filter_lemmas.
#[export] Hint Resolve mem_filter : filter_lemmas.
#[export] Hint Resolve length_filter : filter_lemmas.
#[export] Hint Resolve mem_filter_inv : filter_lemmas.
#[export] Hint Resolve LibList.length_filter : filter_lemmas.
#[export] Hint Resolve Exists_filter_pred_incl : filter_lemmas.
#[export] Hint Resolve filter_length_partition : filter_lemmas.
#[export] Hint Resolve LibList.length_filter_eq_mem_ge_one : filter_lemmas.
#[export] Hint Resolve length_filter_eq_mem_ge_one : filter_lemmas.

#[export] Hint Rewrite filter_not_nil : filter_lemmas.
#[export] Hint Rewrite filter_not_rev : filter_lemmas.
#[export] Hint Rewrite LibList_length_filter_not : filter_lemmas.
#[export] Hint Rewrite length_filter_not : filter_lemmas.
#[export] Hint Rewrite filter_not_nil_eq_filter : filter_lemmas.
#[export] Hint Rewrite filter_not_app : filter_lemmas.
#[export] Hint Rewrite mem_filter_not_eq : filter_lemmas.
#[export] Hint Rewrite filter_not_length_partition : filter_lemmas.
#[export] Hint Rewrite filter_not_cons : filter_lemmas.
#[export] Hint Rewrite filter_not_last : filter_lemmas.
#[export] Hint Rewrite filter_nil : filter_lemmas.
#[export] Hint Rewrite filter_rev : filter_lemmas.
#[export] Hint Rewrite count_eq_length_filter : filter_lemmas.
#[export] Hint Rewrite LibList.count_eq_length_filter : filter_lemmas.
#[export] Hint Rewrite filter_not_nil_eq_filter : filter_lemmas.
#[export] Hint Rewrite mem_filter_eq : filter_lemmas.
#[export] Hint Rewrite filter_app : filter_lemmas.
#[export] Hint Rewrite LibList.filter_length_partition : filter_lemmas.
#[export] Hint Rewrite filter_cons : filter_lemmas.
#[export] Hint Rewrite LibList.filter_length_two_disjoint : filter_lemmas.
#[export] Hint Rewrite filter_length_two_disjoint : filter_lemmas.
#[export] Hint Rewrite filter_last : filter_lemmas.

#[export] Hint Rewrite If_istrue : iff_lemmas.
#[export] Hint Rewrite If_r : iff_lemmas.
#[export] Hint Rewrite If_l : iff_lemmas.

Ltac intros_then_apply H :=
  lazymatch goal with
  | [ |- forall (x: _), _] => let x := fresh x in intro x; intros_then_apply H; gen x
  | _ => H
  end.

Ltac sis_simplify_math_goal :=
  rew_list;
  repeat lazymatch goal with
    | [ |- context[?x - 0] ] => math_rewrite (x - 0 = x)
    | [ |- context[?x + 0] ] => math_rewrite (x + 0 = x)
    | [ |- context[?x - ?x] ] => math_rewrite (x - x = 0)
    | [ |- context[0 + ?x]] => math_rewrite (0 + x = x)
    | [ |- context[?x - 1 + 1]] => math_rewrite (x - 1 + 1 = x)
    | [ |- context[?x + 1 - 1]] => math_rewrite (x + 1 - 1 = x)
    | [ |- context[?x + 1 - 2 + 1]] => math_rewrite (x + 1 - 2 + 1 = x)
    | [ |- context [ (?x + 1 - ?y - 1) ]] =>
        math_rewrite (x + 1 - y - 1 = x - y)
    | [ |- context [ (?x + 1 + ?y - 1) ]] =>
        math_rewrite (x + 1 + y - 1 = x + y)
    | [ |- context [ (?x - 1 - ?y + 1) ]] =>
        math_rewrite (x - 1 - y + 1 = x - y)
    | [ |- context [ (?x - 1 + ?y + 1) ]] =>
        math_rewrite (x - 1 + y + 1 = x + y)
    | [ |- context [ (1 + ?x) ]] =>
        math_rewrite (1 + x = x + 1)
    | [ |- context [ ?x + (?y + 1) ]] =>
        math_rewrite (x + (y + 1) = (x + y) + 1)
    | [ |- context[(?z + ?x + ?y) - (?x + ?y)] ] =>
        math_rewrite (z + x + y - (x + y) = z)
    | [ |- context[ (?t + ?r - ?t)]] =>
        math_rewrite ((t + r - t) = r)
    | [ |- context[ (?t + ?r + ?z - ?t)]] =>
        math_rewrite ((t + r + z - t) = r + z)
    | [ |- context [(?x + 1 + 1 - 2)]] =>
        math_rewrite (x + 1 + 1 - 2 = x)
    | [ |- context[?r + 1 - (?t + 1)]] =>
        math_rewrite (r + 1 - (t + 1) = r - t)
    | [ |- context[?r - 1 + ?z + 1]] =>
        math_rewrite (r - 1 + z + 1 = r + z)
    | [ |- context[?b + ?x + ?y - ?x]] =>
        math_rewrite (b + x + y - x = b + y)
    | [ |- context[?x + 1 - 2 - ?z + 1] ] => math_rewrite (x + 1 - 2 - z + 1 = x - z)
    end.

Ltac sis_symexec :=
  repeat lazymatch goal with
      | [ |- @himpl (hpure _ ) _ ] =>
          let H := fresh "H" in
          xpullpure H
      | [ |- @himpl (hstar (hpure _) _) _ ] =>
          let H := fresh "H" in
          xpullpure H
      | [ |- @himpl ?pre
               (@Wptag
                  (@Wpgen_let_trm
                     (@Wptag (@Wpgen_app Z Enc_int Array_ml.get _))
                     ?ty ?enc_ty
                     ?rest) _ _ _) ] =>
          xapp; [ apply int_index_prove; try math | ]
      | [ IA: Inhab ?A |- @himpl ?pre
                            (@Wptag
                               (@Wpgen_let_trm
                                  (@Wptag (@Wpgen_app ?A _ Array_ml.get _))
                                  ?ty ?enc_ty
                                  ?rest) _ _ _) ] =>
          xapp; [ apply int_index_prove; try math | ]
      | [ |- @himpl ?pre
                            (@Wptag
                               (@Wpgen_let_trm
                                  (@Wptag (@Wpgen_app ?A _ Array_ml.get _))
                                  ?ty ?enc_ty
                                  ?rest) _ _ _) ] =>
          xinhab_inner A; xapp; [ apply int_index_prove; try math | ]
      | [ |- @himpl ?pre
               (@Wptag
                  (@Wpgen_let_trm
                     (@Wptag (@Wpgen_app _ _ _ _))
                     ?ty ?enc_ty
                     ?rest) _ _ _) ] =>
          xapp
      | [ |- @himpl _
               (@Wptag
                  (@Wpgen_seq (@Wptag (@Wpgen_if _ _ _)) _) _ _ _) ] =>
          let Hcond := fresh "Hcond" in
          xif as Hcond
      | [ |- @himpl _
               (@Wptag
                  (@Wpgen_let_val _ _
                     (fun binding => _)) _ _ _) ] =>
          xlet
      | [ |- @himpl ?pre
               (@Wptag (@Wpgen_app _ _ infix_colon_eq__ _) _ _ _) ] =>
          xapp
      | [ |- @himpl ?pre
               (@Wptag (@Wpgen_app _ _ infix_emark__ _) _ _ _) ] =>
          xapp
      | [ |- @himpl ?pre
               (@Wptag (@Wpgen_val _ _ _) _ _ _) ] =>
          xvals*
      | [ |- himpl (hstar _ _) (hstar _ _)] => xsimpl*
      end.

Ltac sis_solve_start :=
  repeat lazymatch goal with
  | [ |- forall (Heq: _ = _), _] => let x := fresh Heq in intro x
  | [ |- forall (x: _), _] => let x := fresh x in intro x
  | [ |- _ -> _ ] => let v := fresh "Hv" in intros v
  | [ H : Wpgen_body _ |- @Triple ?f ?r ?r2 ?P ?Q ] => apply H; clear H; xinhab; xgo*; try math
  end.

Ltac sis_handle_if :=
  lazymatch goal with
    | [ H : ?cond |- context [If ?cond then _ else _]] => rewrite If_l; auto
    | [ H : ?cond |- context [If (~ ?cond) then _ else _]] => rewrite If_r; auto
    | [ H : ~ ?cond |- context [If ?cond then _ else _]] => rewrite If_r; auto
    | _ => idtac
    end.  


Ltac sis_expand_rewrites :=
  repeat lazymatch goal with
    | [ H: ?x = _ |- context [?x]] => rewrite !H in *
    end.

Ltac sis_handle_int_index_prove :=
  lazymatch goal with
  | [ |- index _ _ ] => apply int_index_prove; try rewrite <- !length_eq; rew_list; try math
  | _ => idtac
  end.

Ltac sis_normalize_length :=
  lazymatch goal with
  | [ |- context [length (take _ _)] ] =>
      rewrite length_take_nonneg; sis_normalize_length; rew_list; try math
  | [ |- context [length (drop _ _)] ] =>
      rewrite length_drop_nonneg; sis_normalize_length; rew_list; try math
  | [ |- context [length (make _ _)] ] =>
      rewrite length_make; sis_normalize_length; rew_list; try math
  | [ H : _ = rev ?rest |- context[length ?rest] ] =>
      apply (f_equal (@rev _)) in H; rewrite rev_rev in H; rewrite <- H; rew_list;
      sis_normalize_length; rew_list; try math
  | [H: context[length (_ :: _)] |- _] => rew_list in H
  | [ H: length (filter_not ?f ?t) <= _ |- context[length (filter_not ?f ?t)] ] => idtac
  | [ |- context[length (filter_not ?f ?t)] ] => 
      pose proof (Hft:= length_filter_not t f); try math; sis_normalize_length 
  | [ H: length (filter ?f ?t) <= _ |- context[length (filter ?f ?t)] ] => idtac
  | [ |- context[length (filter ?f ?t)] ] => 
      pose proof (Hft:= length_filter t f); try math; sis_normalize_length 
  | _ => idtac
  end.

Ltac sis_list_solver :=
  repeat lazymatch goal with
    | [ H : 0 = length _ |- _ ] =>
        symmetry in H; apply length_zero_inv in H; try rewrite H in *; rew_list in *; auto
    | [ H : length _ = 0  |- _ ] =>
        apply length_zero_inv in H; try rewrite H in *; rew_list in *; auto
    | [ H: istrue (?f ?v) |-
          context[filter (fun x: _ => istrue (?f x)) (?t & ?v)]] =>
        rewrite filter_last, If_l; [| solve [auto]]; rew_list; try math
    | [ H: istrue (?f ?v) |-
          context[filter_not (fun x: _ => istrue (?f x)) (?t & ?v)]] =>
        rewrite filter_not_last, If_l; [| solve [auto]]; rew_list; try math
    | [ H: ~ (istrue (?f ?v)) |-
          context[filter (fun x: _ => istrue (?f x)) (?t & ?v)]] =>
        rewrite filter_last, If_r; [| solve [auto]]; rew_list; try math
    | [ H: ~ (istrue (?f ?v)) |-
          context[filter_not (fun x: _ => istrue (?f x)) (?t & ?v)]] =>
        rewrite filter_not_last, If_r; [| solve [auto]]; rew_list; try math
    | [ H: istrue (?f ?v) |-
          context[filter (fun x: _ => istrue (?f x)) (?v :: ?t)]] =>
        rewrite filter_cons, If_l; [| solve [auto]]; rew_list; try math
    | [ H: istrue (?f ?v) |-
          context[filter_not (fun x: _ => istrue (?f x)) (?v :: ?t)]] =>
        rewrite filter_not_cons, If_l; [| solve [auto]]; rew_list; try math
    | [ H: ~ (istrue (?f ?v)) |-
          context[filter (fun x: _ => istrue (?f x)) (?v :: ?t)]] =>
        rewrite filter_cons, If_r; [| solve [auto]]; rew_list; try math
    | [ H: ~ (istrue (?f ?v)) |-
          context[filter_not (fun x: _ => istrue (?f x)) (?v :: ?t)]] =>
        rewrite filter_not_cons, If_r; [| solve [auto]]; rew_list; try math
    | [ |- context [rev (filter ?f (rev ?ls))]] =>
        rewrite filter_rev, rev_rev
    | [ |- context [rev (filter_not ?f (rev ?ls))]] =>
        rewrite filter_not_rev, rev_rev
    | [|- context [take (length ?l) (?l ++ _)] ] =>
          rewrite take_prefix_length
    | [ |- context[ take 0 _ ] ] =>
        rewrite take_zero in *; rew_list; simpl
    | [ |- context[ take (length ?l) ?l ] ] =>
        rewrite take_full_length; rew_list; simpl
    | [ H: context[ take (length ?l) ?l ] |- _ ] =>
        rewrite take_full_length in H; rew_list in H; simpl in H
    | [ |- context[ drop (length ?l) ?l ] ] =>
        rewrite drop_at_length; rew_list; simpl
    | [ H: context[ drop (length ?l) ?l ] |- _ ] =>
        rewrite drop_at_length in H; rew_list in H; simpl in H
    | [ |- context[drop 1 (?hd :: _)]] =>
        rewrite (drop_cons_pos hd); [math_rewrite (1 - 1 = 0)| math];
        rewrite drop_zero
    | [ |- context[drop 1 (?hd :: _ ++ _)]] =>
        rewrite (drop_cons_pos hd); [math_rewrite (1 - 1 = 0)| math];
        rewrite drop_zero
    | [ |- context[drop 0 _]] =>
        rewrite drop_zero
    | [ |- context[make 0 _]] =>
        rewrite make_zero
    | [ |- context[(?l ++ ?r)[length ?l := _]]] =>
        rewrite (@update_app_r _ r 0 l (length l) (length l));
        [  | math | math | math ]
    | [ |- context[(?t ++ ?r)[length ?t := _]]] =>
        rewrite (@update_app_r _ r 0 t (length t)); [ | auto | math | math ]
    | [ |- context[(make (?l + 1) ?vl)[0:=?nvl]]] =>
        rewrite make_succ_l, update_zero; [| math]
    | [ |- ?vl :: _ = take (_ + 1) (?vl :: _)] =>
        rewrite take_cons; [| math]; f_equal
    | [ |- context[take (length ?l) (rev ?l)]] =>
        let H := fresh "H" in
        let Heqn := fresh "Heqn" in
        remember (length l) as H eqn:Heqn;
        rewrite <- length_rev in Heqn;
        rewrite Heqn; clear H Heqn;
        rewrite take_full_length
    | [ |- context[take (length ?l + 1) (rev ?l & ?v)]] =>
        let Heqn := fresh "Heqn" in
        assert (Heqn: length l + 1 = length (rev l & v)) by (rew_list; math);
        rewrite Heqn; clear Heqn; rewrite take_full_length
    | [ |- make ?oi ?v = make ?ni ?v ] => f_equal; try math
    | [ |- filter ?f ?ls ++ _ = filter ?f ?ls ++ _] => f_equal; try math
    | [ |- filter_not ?f ?ls ++ _ = filter_not ?f ?ls ++ _] => f_equal; try math
    | [ |- drop ?len ?ls = drop ?olen ?ls] => f_equal; try math
    | [ |- make ?i ?v ++ _ = make ?i ?v ++ _ ] => f_equal
    | [ |- _ :: _ & ?v = _ & ?v ] => rewrite <- last_cons; f_equal
    end.

Ltac sis_list_deep_solver :=
  repeat match goal with 
    | [ |- context[drop ?x (make ?z _ ++ _)]] =>
        let H := fresh "Hvalid" in
        assert (H: x >= z)
          by (subst; rew_list; sis_normalize_length; math);
        rewrite drop_app_r; [clear H|sis_normalize_length; math]
    | [ |- context[drop _ (make _ _)]] =>
        rewrite drop_make_eq; [|subst;rew_list; sis_normalize_length; math]
    | [ |- context[drop ?d (rev ?r ++ _)]] =>
        let H := fresh "Hlen" in
        assert (H: length (rev r) <= d) by (rew_list; math);
        rewrite drop_app_r; [clear H; rew_list| rew_list; math]
    | [ H: nil = rev ?x |- _ ] =>
        apply nil_eq_rev_inv in H; try (subst; rew_list; auto; fail)
    | [ |- context [(make (?i + 1) _ ++ _)[?i := _]]] =>
        rewrite make_succ_r; [ | math]; rew_list; rewrite update_middle; [|sis_normalize_length]
    | [ |- make (?i + 1) ?vl = make ?i ?vl & ?vl] =>
        rewrite make_succ_r; [ | math]; rew_list; auto
    | [ H: _ :: ?rest = ?ls |- context [length ?rest] ] =>
        let H_len := fresh "Hlen" in
        assert (H_len: length rest = length ls - 1) by (rewrite <- H; rew_list; math);
        rewrite H_len; clear H_len; rew_list
    | [  H: existsb ?fp (take ?i ?l) = false |-
           context[existsb ?fp (take (?i + 1) ?l)] ] =>
        unfold existsb in *; rewrite (take_pos_last _); [|apply int_index_prove; math];
        math_rewrite (i + 1 - 1 = i); 
        rewrite list_existsb_app, !or_orb_eq, H; simpl
    | [ H: List.existsb ?fp (take ?i ?l) = false |-
          context[List.existsb ?fp (take (?i + 1) ?l)] ] =>
        rewrite (take_pos_last _); [|apply int_index_prove; math];
        math_rewrite (i + 1 - 1 = i); 
        rewrite list_existsb_app, !or_orb_eq, H; simpl
    | [H: existsb ?f (take ?i ?l) = true, Hi: ?i <= length ?l |- context Hctx[existsb ?f ?l]] =>
        let Hleq := fresh "Hleq" in
        pose proof (Hleq := @list_eq_take_app_drop _ i l Hi);
        apply (f_equal (existsb f)) in Hleq; rewrite <- Hleq; clear Hleq;
        unfold existsb in *; rewrite list_existsb_app, H
    | [H: existsb ?f (take ?i ?l) = true, Hi: _ <= ?i <= length ?l |-
         context Hctx[existsb ?f ?l]] =>
        let Hleq := fresh "Hleq" in
        let Hlen := fresh "Hlen" in
        assert (Hlen: i <= length l) by math;
        pose proof (Hleq := @list_eq_take_app_drop _ i l Hlen);
        apply (f_equal (existsb f)) in Hleq; rewrite <- Hleq; clear Hleq;
        unfold existsb in *; rewrite list_existsb_app, H
    | [H: List.existsb ?f (take ?i ?l) = true, Hi: ?i <= length ?l |-
         context Hctx[List.existsb ?f ?l]] =>
        let Hleq := fresh "Hleq" in
        pose proof (Hleq := @list_eq_take_app_drop _ i l Hi);
        apply (f_equal (List.existsb f)) in Hleq; rewrite <- Hleq; clear Hleq;
        rewrite list_existsb_app, H
    | [H: List.existsb ?f (take ?i ?l) = true, Hi: _ <= ?i <= length ?l |-
         context Hctx[List.existsb ?f ?l]] =>
        let Hleq := fresh "Hleq" in
        let Hlen := fresh "Hlen" in
        assert (Hlen: i <= length l) by math;
        pose proof (Hleq := @list_eq_take_app_drop _ i l Hlen);
        apply (f_equal (List.existsb f)) in Hleq; rewrite <- Hleq; clear Hleq;
        rewrite list_existsb_app, H
    | [ H: is_some (list_findi ?fp (take ?i ?l)) = false |-
          context[list_findi ?fp (take (?i + 1) ?l)] ] =>
        rewrite (take_pos_last _ (i + 1)); [|apply int_index_prove; math];
        math_rewrite (i + 1 - 1 = i); 
        rewrite !findi_unfold in *; rewrite findi_app_r
    | [  H: istrue (?fp ?i ?vl) |-  context[list_findi_internal ?i ?fp (?vl :: _)] ] =>
        simpl list_findi_internal; rewrite H
    | [  H: ~ istrue (?fp ?i ?vl) |-  context[list_findi_internal ?i ?fp (?vl :: _)] ] =>
        simpl list_findi_internal;  apply not_is_false in H; rewrite H
    | [ H: is_some (list_findi ?fp (take ?i ?l)) = true |-
          context H [list_findi ?fp ?l]
      ] =>
        let Hv := fresh "Hv" in
        let Hveq := fresh "Hveq" in
        remember (list_findi fp l) as Hv eqn:Hveq;
        rewrite <- (@list_eq_take_app_drop _ i l) in Hveq; [| math];
        rewrite Hveq; clear Hv Hveq;
        rewrite !findi_unfold, findi_app_l in *; auto; simpl
    | [ H: None = (list_findi ?fp (take ?i ?l)) |-
          context H [list_findi ?fp (take (?i + 1) ?l)]
      ] =>
        rewrite (take_pos_last _ (i + 1));
        [|apply int_index_prove; math];
        math_rewrite (i + 1 - 1 = i);
        rewrite !findi_unfold in *; rewrite findi_app_r;
        simpl list_findi_internal
    | [ H: Some (?vl, ?vr) = (list_findi ?fp (take ?i ?l)) |-
          context [list_findi ?fp ?l]
      ] =>
        let Hv := fresh "Hv" in
        let Hveq := fresh "Hveq" in
        remember (list_findi fp l) as Hv eqn:Hveq;
        rewrite <- (@list_eq_take_app_drop _ i l) in Hveq; [| math];
        rewrite Hveq; clear Hv Hveq;
        rewrite !findi_unfold in *; rewrite findi_app_l; [auto| rewrite <- H]
    | [ H: None = (list_findi ?fp (take ?i ?l)) |- context [list_findi ?fp ?l] ] =>
        let Hv := fresh "Hv" in
        let Hveq := fresh "Hveq" in
        remember (list_findi fp l) as Hv eqn:Hveq;
        rewrite <- (@list_eq_take_app_drop _ i l) in Hveq; [| math];
        rewrite Hveq; clear Hv Hveq;
        rewrite !findi_unfold in *; rewrite findi_app_r; [ | rewrite <- H; auto]
    | [ |- context[?f ?i ?vl (list_foldi (take ?i ?l) ?init ?f)]] =>
        let _ :=
          lazymatch goal with[|-context[list_foldi(take(i + 1)l)init f]] => true end in
        rewrite (@foldi_rcons _ _ f init (take i l) (l[i]) (take (i + 1) l));
        [| rewrite (take_pos_last _ (i + 1)); [| apply int_index_prove; math];
           do 3 f_equal; math ]
    | [ |- context[?f (length ?t) ?v (list_foldi ?t ?init ?f)]] =>
        let _ :=
          lazymatch goal with[|-context[list_foldi (t & v) init f]] => true end in
        rewrite (@foldi_rcons _ _ f init t v (t & v)); auto
    | [ H : context [drop ?i ?l] |- context[drop (?i - 1) ?l] ] =>
        rewrite (@drop_cons_unfold _ _ l (i - 1)); [| math];
        math_rewrite (i - 1 + 1 = i)
    | [ H: ?vl <= ?gvl |- context[is_sorted (?vl :: ?tl)] ] =>
        rewrite (@is_sorted_gen vl tl); [ auto | auto; sis_normalize_length | auto | auto ]
    | [ H: ~ (?vl > ?gvl) |- istrue (is_sorted (?vl :: ?tl))] =>
        apply (@is_sorted_gen vl tl); [
          sis_normalize_length | auto
        | rewrite read_drop; [ sis_simplify_math_goal; math
                             | math
                             | apply int_index_prove; math] ]
    | [ |- context [(drop ?i ?l)[0]]] =>
        rewrite read_drop, Z.add_0_r;
        [ | math | apply int_index_prove; math ];
        auto
    | [ H: ~ (?vl <= ?gvl) |- is_sorted (?vl :: ?tl) = false] =>
        apply not_is_false; apply (@not_is_sorted_gen (vl :: tl) 1); [
          rew_list; sis_normalize_length; math
        | rew_list; sis_normalize_length; math
        | math_rewrite (1 - 1 = 0); rewrite read_zero, read_cons_pos; [ | math] ]
    | [ H: ?vl > ?gvl |- ~ istrue (is_sorted (?vl :: ?tl))] =>
        apply (@not_is_sorted_gen (vl :: tl) 1); [
          rew_list; sis_normalize_length; math
        | rew_list; sis_normalize_length; math
        |  ];
        math_rewrite (1 - 1 = 0); rewrite read_zero, read_cons_pos; [ | math];
        math_rewrite (1 - 1 = 0); rewrite read_drop; [
          sis_simplify_math_goal; math
        | math
        | apply int_index_prove; math ]          

    | [ |- context[is_sorted (drop (length ?l - 1) ?l)]] =>
        rewrite (is_sorted_last_elt l); [ auto | math ]
    | [H: is_sorted (drop ?i ?l) = false |- is_sorted ?l = false] =>
        let v := fresh "v" in
        let Hv := fresh "Hv" in
        remember (is_sorted l) as v eqn:Hv;
        rewrite <- (@list_eq_take_app_drop _ i l) in Hv; [| math];
        rewrite Hv; clear v Hv;
        apply is_sorted_app_r; auto
    | [ H: None = (list_find_mapi ?fp (take ?i ?l)) |-
          context [list_find_mapi ?fp (take (?i + 1) ?l)] ] =>
        rewrite !find_mapi_unfold in *;
        rewrite (take_pos_last _ (i + 1));
        [| apply int_index_prove; sis_normalize_length; math];
        math_rewrite (i + 1 - 1 = i);
        rewrite find_mapi_app_r; [ | auto];
        sis_simplify_math_goal;
        rewrite length_take_nonneg; [| rew_list; sis_normalize_length; math];
        rewrite find_mapi_singleton; auto; math
    | [ Hv: Some _ = (list_find_mapi ?fp (take ?i ?l)) |-
          context [list_find_mapi ?fp ?l] ] =>
        let H := fresh "H" in
        let Heq := fresh "Heq" in
        rewrite !find_mapi_unfold in *;
        remember (list_find_mapi_internal 0 fp l) as H eqn:Heq;
        rewrite <- (@list_eq_take_app_drop _ i l) in Heq;
        [| rew_list; sis_normalize_length; math];
        rewrite find_mapi_app_l in Heq; [| subst; rewrite <- Hv; auto; math];
        rewrite Heq; clear H Heq; auto; math
    | [ H: is_some (list_find_mapi ?f (take ?i ?l)) = false,
          Hvl: istrue (is_some (?f ?i ?l[?i])) |-
          context[list_find_mapi ?f (take (?i + 1) ?l)] ] =>
        rewrite !find_mapi_unfold in *;
        rewrite (take_pos_last _ (i + 1));
        [| apply int_index_prove; sis_normalize_length; math];
        rewrite find_mapi_app_r; math_rewrite (i + 1 - 1 = i);
        sis_simplify_math_goal;
        [ rewrite find_mapi_singleton; rew_list; sis_normalize_length | ];
        auto
    | [ H: is_some (list_find_mapi ?f (take ?i ?l)) = false,
          Hvl: ~ istrue (is_some (?f ?i ?l[?i])) |-
          context[list_find_mapi ?f (take (?i + 1) ?l)] ] =>
        rewrite !find_mapi_unfold in *;
        rewrite (take_pos_last _ (i + 1));
        [| apply int_index_prove; sis_normalize_length; math];
        rewrite find_mapi_app_r; math_rewrite (i + 1 - 1 = i);
        sis_simplify_math_goal;
        [ rewrite find_mapi_singleton; rew_list; sis_normalize_length | ];
        auto
    | [ H: is_some (list_find_mapi ?f (take ?i ?l)) = true |-
            context[list_find_mapi ?f ?l] ] =>
          let H := fresh "H" in
          let Heqn := fresh "Heqn" in
          rewrite !find_mapi_unfold in *;
          remember (list_find_mapi_internal 0 f l) as H eqn:Heqn;
          rewrite <- (@list_eq_take_app_drop _ i l) in Heqn;
          [| rew_list; sis_normalize_length; math ];
          rewrite find_mapi_app_l in Heqn; [| auto];
          rewrite Heqn; clear H Heqn; auto
    | [ |- context [drop ?i (drop ?j ?ls)]] =>
        rewrite (@drop_drop _ ls i j); [ | rew_list in *; math | rew_list in *; math ]
    | [ |- context[take ?i (make ?j ?v)]] =>
        let Hv := fresh "Hv" in
        assert (Hv: 0 <= i <= j) by math;
        rewrite (@take_make_eq _ i j v Hv);
        clear Hv
    | [ |- context[(drop ?i ?l)[?ind]]] =>
        let Hv := fresh "Hv" in
        assert (Hv: 0 <= i <= length l) by (rew_list; sis_normalize_length; math);
        rewrite (read_drop _ l Hv);
        [ | apply int_index_prove; rew_list; sis_normalize_length; math ]
    | [ |- context [rev (take ?i (?h :: ?t))]] =>
        rewrite (@take_cons_pos _ h t); [ | math ];
        rewrite rev_cons
    | [ |- (?h :: ?l)[_ - ?i] :: rev (take (?j - (?i + 1)) ?l) =
             rev (take (?j - ?i) ?l) ] =>
        rewrite (read_cons_pos _ h l); [ | math ];
        rewrite (@rev_cons_unfold _ _ (take (j - i) l));
        sis_normalize_length;
        rewrite read_take; [ | math | apply int_index_prove; math ];
        f_equal;
        math_rewrite (j - (i + 1) = (j - i) - 1);
        rewrite (@rev_take_drop_unfold _ _ l (j - i) 1);
        try math; auto
    | [ |- length (filter ?f ?t) < _ ] =>
        pose proof (Hft:= length_filter t f);
        math
    | [ |- length (filter ?f ?t) <= _ ] =>
        pose proof (Hft:= length_filter t f);
        math
    | [ |- _ <= length (filter ?f ?t) <= _ ] =>
        pose proof (Hft:= length_filter t f);
        math
    | [ |- length (filter_not ?f ?t) < _ ] =>
        pose proof (Hft:= length_filter_not t f);
        math
    | [ |- length (filter_not ?f ?t) <= _ ] =>
        pose proof (Hft:= length_filter_not t f);
        math
    | [ |- _ <= length (filter_not ?f ?t) <= _ ] =>
        pose proof (Hft:= length_filter_not t f);
        math
    | [|- (make ?i ?vl)[0:= ?nvl] = (?nvl :: _)] =>
        rewrite (@make_write_zero _ i vl);
        [f_equal | rew_list; sis_normalize_length; math]
    end.  

Ltac sis_dispatch_filter_goal :=
  match goal with
  | [ |- context [ length (filter ?f ?ls) ]] =>
      pose proof (length_filter ls f); math
  end.

Ltac sis_handle_list_update :=
  lazymatch goal with
  | [ |- context [ (?l ++ _)[length ?l := _] ]] =>
      rewrite (@update_app_r _ _ 0 _ (length l)); try math
  end.

Ltac sis_normalize_succs :=
  repeat lazymatch goal with
    | [ |- context [ (1 + ?x) ]] =>
        math_rewrite (1 + x = x + 1)
    | [ |- context [ ?x + (?y + 1) ]] =>
        math_rewrite (x + (y + 1) = (x + y) + 1)
    end.

Ltac sis_normalize_opt_of_bool :=
  repeat lazymatch goal with
    | [ H:  None = opt_of_bool _ |- _ ] =>
        apply opt_of_bool_none in H
    | [ H:  Some tt = opt_of_bool _ |- _ ] =>
        apply opt_of_bool_some in H
    | [  |- Some tt = opt_of_bool _ ] =>
        apply opt_of_bool_some_intro
    | [ |- None = opt_of_bool _ ] =>
        apply opt_of_bool_none_intro
    | [ |- context [is_some (opt_of_bool _)]] =>
        rewrite is_some_opt_of_bool_eq
    | [ |- option_value_snd ?vl ?ls = option_value_snd ?vl ?ols ] =>
        f_equal
    | [ |- option_value_fst ?vl ?ls = option_value_fst ?vl ?ols ] =>
        f_equal
    | [ H: is_some (?ls) = false |- ?ls = None ] =>
        apply not_is_some_eq; auto
    | [ H: is_some (?ls) = false |- None = ?ls ] =>
        symmetry; apply not_is_some_eq; auto
    | [ H: ~ (istrue (is_some ?vl)) |- _ = ?vl ] =>
        apply not_is_false in H; apply not_is_some_eq in H;
        rewrite H; auto
    | [ |- Some (option_value_fst _ ?exp, option_value_snd _ ?exp) = ?exp] =>
        let p1 := fresh "p1" in
        let p2 := fresh "p2" in
        case (exp) as [[p1 p2] | ];
        simpl option_value_snd; simpl option_value_fst; auto
    | [ H: is_some None = true |- _ ] =>
            simpl in H; inversion H; auto
    | [H: None = ?exp |- is_some ?exp = false ] =>
        rewrite <- H; simpl is_some
    | [H: istrue (is_some (?v)) |- context[negb (is_some ?v)]] =>
        rewrite H; simpl negb
    | [ H : context[is_some (Some _)] |- _ ] =>
        simpl is_some in H
    | [ |- context[is_some (Some _)] ] =>
        simpl is_some
    | [ H : context[is_some None] |- _ ] =>
        simpl is_some in H
    | [ |- context[is_some None] ] =>
        simpl is_some 
    | [ H: context[opt_of_bool false] |- _ ] =>
        simpl opt_of_bool in H
    | [ H: context[opt_of_bool true] |- _ ] =>
        simpl opt_of_bool in H
    | [ H: is_some ?o = false |- ?o = None ] =>
          apply not_is_some_eq; auto
    end.

Ltac sis_normalize_boolean_goals :=
  repeat lazymatch goal with
    | [ H : true = false |- _ ] => inversion H
    | [ H : false = true |- _ ] => inversion H
    | [ H : true = true |- _ ] => clear H
    | [ H : false = false |- _ ] => clear H
    | [ H : false = _ |- _ ] => symmetry in H
    | [ H : true = _ |- _ ] => symmetry in H
    | [ H : negb _ = false |- _ ] =>
        apply (f_equal negb) in H; rewrite Bool.negb_involutive in H; simpl negb in H
    | [ H : negb _ = true |- _ ] =>
        apply (f_equal negb) in H; rewrite Bool.negb_involutive in H; simpl negb in H
    | [ |- negb _ = false ] =>
        rewrite (Bool.negb_involutive_reverse false); apply f_equal; simpl negb
    | [ |- negb _ = true ] =>
        rewrite (Bool.negb_involutive_reverse true); apply f_equal; simpl negb
    | [  |- true = true ] => auto
    | [  |- false = false ] => auto
    | [  |- true = false ] => fail
    | [  |- false = true ] => fail
    | [  |- true = _ ] => symmetry
    | [  |- false = _ ] => symmetry
    | [ |- negb _ = negb _ ] => f_equal
    | [ |- context[negb (_ || _)%bool] ] => rewrite Bool.negb_orb
    | [ |- context[negb false] ] => simpl negb
    | [ |- context[negb true] ] => simpl negb
    | [ |- context[(_ && true)%bool] ] => rewrite Bool.andb_true_r
    | [ |- context[(_ || false)%bool] ] => rewrite Bool.orb_false_r
    | [ |- context[(true && _)%bool] ] => simpl andb
    | [ |- context[(false || _)%bool] ] => simpl orb
    | [ |- context[(false && _)%bool] ] => simpl andb
    | [ |- context[(true || _)%bool] ] => simpl orb
    | [ H: context[implb true _] |- _ ] => simpl in H
    | [ H : context [negb (negb _)] |- _ ] =>
        rewrite Bool.negb_involutive in H
    | [ |- context [negb (negb _)] ] =>
        rewrite Bool.negb_involutive 
    | [H: istrue ?exp |- context[if ?exp then _ else _] ] => rewrite H
    | [ H: istrue (Z.eqb ?l ?r) |- _] =>
        let H_eq := fresh H in
        assert (H_eq: l = r) by (apply Z.eqb_eq; auto);
        clear H; rename H_eq into H; rewrite H in *
    | [H: ~ (istrue ?exp) |- context[if ?exp then _  else _]] =>
        apply negb_iff in H; rewrite H
    | [H: ~ (istrue ?f) |- ?f = false] => destruct f; simpl; auto; contradiction H; auto
    | [ |- context[! _] ] => rewrite <- negb_eq_neg
    | [ H: context[! _] |- _ ] => rewrite <- negb_eq_neg in H
    | [H: _ /\ _ |- _] =>
        let H1 := fresh "H1" in
        let H2 := fresh "H2" in
        destruct H as [H1 H2]
    | [H: context[negb true] |- _ ] => simpl negb in H
    | [H: context[negb false] |- _ ] => simpl negb in H
    end.  

Ltac sis_handle_take_splitting_goals :=
  lazymatch goal with
    | [ H: context [take ?x _] |- context[take (?x - 1) _] ] =>
        gen H; erewrite take_pos_last; sis_handle_int_index_prove; auto; intros H
  | [ |- context [(take ?i _ ++ _)[?i := _]]] =>
      rewrite (@update_app_r _ _ 0 (take i _) i i); try math
  end.

Ltac sis_handle_take_drop_full_length :=
  lazymatch goal with
  | [ Heq: length ?x = length ?y |-
        context [ take (length ?x) (map2 ?fp (combine ?x ?y))]] =>
      let H := fresh "H" in
      assert (H: length x = length (map2 fp (combine x y))) 
        by (unfold map2; rewrite length_map, !length_eq, length_combine; gen Heq; rewrite !length_eq; math);
      rewrite H, ?take_full_length, ?drop_at_length
  | [  |- context [ drop (length ?x) (make (length ?x) ?vl)]] =>
      let H := fresh "H" in
      assert (H: length x = length (make (length x) vl))
        by (rewrite length_make; math);
      rewrite H at 1; rewrite drop_at_length
  end.

Ltac sis_solver_hook := fail.

Ltac sis_pre_solver_steps :=
  match goal with
  | _ => sis_solver_hook
  | _ => idtac
  end.

Ltac sis_generic_solver :=
  sis_pre_solver_steps;
  lazymatch goal with
  | [ |- context[@Triple _]] =>
      intros_then_apply sis_simplify_math_goal; sis_solve_start; sis_generic_solver
  | [ |- index _ _] => sis_handle_int_index_prove; sis_generic_solver
  | _ => sis_normalize_boolean_goals; sis_normalize_opt_of_bool; subst; rew_list; try math;
         repeat (sis_normalize_length;
                 sis_normalize_boolean_goals;
                 sis_normalize_opt_of_bool;
                 sis_list_solver;
                 sis_list_deep_solver;
                 sis_simplify_math_goal; auto)
  end.
