From SLF Require Import LibTactics.

From Stdlib Require Import ZArith String List.
From Stdlib Require Import Classes.RelationClasses.
From Stdlib Require Morphisms Program.Basics.
Import ListNotations.

Inductive val :=
| VInt : Z -> val
| VFun : string -> val.

Inductive term :=
| TEnsure : (val -> Prop) -> term
| TExists : (val -> term) -> term
| TBind : term -> (val -> term) -> term
| TApply : val -> val -> term
| TShift : (val -> term) -> term
| TReset : term -> term.

Definition store := list (string * (val -> term)).

Fixpoint store_lookup (x : string) (s : store) : option (val -> term) :=
  match s with
  | [] => None
  | (x', t) :: s' => if string_dec x x' then Some t else store_lookup x s'
  end.

(*
Fixpoint store_In (x : string) (s : store) : Prop :=
  match s with
  | [] => False
  | (x', _) :: s' => x = x' \/ store_In x s'
  end.
*)

(* need some condition along the line of "the diff in s1 is not in *)

Inductive result :=
| RVal : val -> result
| RBubble : (val -> term) -> (val -> term) -> result.

Inductive satisfies : nat -> store -> store -> result -> term -> Prop :=
(*| s_bottom : forall s1 s2 r t,
    satisfies O s1 s2 r t*)
| s_ensure : forall n Q s v,
    Q v ->
    satisfies (S n) s s (RVal v) (TEnsure Q)
| s_exists : forall n t s1 s2 r v,
    satisfies n s1 s2 r (t v) ->
    satisfies (S n) s1 s2 r (TExists t)
| s_bind_val : forall n t1 t2 s1 s2 r s3 v,
    satisfies n s1 s3 (RVal v) t1 ->
    satisfies n s3 s2 r (t2 v) ->
    satisfies (S n) s1 s2 r (TBind t1 t2)
| s_bind_bubble : forall n t1 t2 s1 s2 b k,
    satisfies n s1 s2 (RBubble b k) t1 ->
    satisfies (S n) s1 s2 (RBubble b (fun v => TBind (k v) t2)) (TBind t1 t2)
| s_apply : forall n x v s1 s2 r t,
    store_lookup x s1 = Some t ->
    satisfies n s1 s2 r (t v) ->
    satisfies (S n) s1 s2 r (TApply (VFun x) v)
| s_shift : forall n t s,
    satisfies (S n) s s (RBubble t (fun v => TEnsure (fun r => r = v))) (TShift t)
| s_reset_val : forall n t s1 s2 v,
    satisfies n s1 s2 (RVal v) t ->
    satisfies (S n) s1 s2 (RVal v) (TReset t)
| s_reset_bubble : forall n t s1 s2 f k s3 x v,
    satisfies n s1 s3 (RBubble f k) t ->
    store_lookup x s3 = None ->
    satisfies n ((x, fun v' => TReset (k v')) :: s3) s2 (RVal v) (TReset (f (VFun x))) ->
    satisfies (S n) s1 s2 (RVal v) (TReset t).

(*
Lemma satisfies_mono_aux :
  forall n s1 s2 r t,
    satisfies n s1 s2 r t ->
    satisfies (Nat.pred n) s1 s2 r t.
Proof.
  intros n s1 s2 r t H_sat.
  induction H_sat as
    [
    | n Q s v HQ
    | (* exists *)
    | (* bind_val *)
    | (* bind_bubble *)
    | n x v s1 s2 r t H_lookup H_sat IHH_sat (* apply *)
    | (* shift *)
    | (* reset_val *)
    | n t s1 s2 f k s3 x v H_sat1 IHH_sat1 H_lookup H_sat2 IHH_sat2
    ].
  - eapply s_bottom.
  - destruct n as [| n'].
    + eapply s_bottom.
    + eapply s_ensure.
      exact HQ.
  - destruct n as [| n'].
    + eapply s_bottom.
    + eapply s_exists.
      exact IHH_sat.
  - destruct n as [| n'].
    + eapply s_bottom.
    + eapply s_bind_val.
      * exact IHH_sat1.
      * exact IHH_sat2.
  - destruct n as [| n'].
    + eapply s_bottom.
    + eapply s_bind_bubble.
      exact IHH_sat.
  - destruct n as [| n'].
    + eapply s_bottom.
    + eapply s_apply.
      * exact H_lookup.
      * exact IHH_sat.
  - destruct n as [| n'].
    + eapply s_bottom.
    + eapply s_shift.
  - destruct n as [| n'].
    + eapply s_bottom.
    + eapply s_reset_val.
      exact IHH_sat.
  - destruct n as [| n'].
    + eapply s_bottom.
    + eapply s_reset_bubble.
      * exact IHH_sat1.
      * exact H_lookup.
      * exact IHH_sat2.
Qed.

Theorem satisfies_mono :
  forall n s1 s2 r t,
    satisfies (S n) s1 s2 r t ->
    satisfies n s1 s2 r t.
Proof.
  intros n.
  exact (satisfies_mono_aux (S n)).
Qed.
*)

Definition entails_store_aux (rec : term -> term -> Prop) (s s' : store) : Prop :=
  forall x f,
    store_lookup x s = Some f ->
    exists f',
      store_lookup x s' = Some f' /\
      forall v, rec (f v) (f' v).

Definition entails_result_aux (rec : term -> term -> Prop) (r r' : result) : Prop :=
  (exists v, r = RVal v /\ r' = RVal v) \/
  (exists b b' k k',
      r = RBubble b k /\
      r' = RBubble b' k' /\
      (forall v, rec (b v) (b' v)) /\
      (forall v, rec (k v) (k' v))).

(*
Fixpoint entails (n : nat) (t t' : term) : Prop :=
  match n with
  | O => True
  | S n' =>
      entails n' t t' /\
      (forall s1 s1' s2 s2' r r',
        entails_store_aux (entails n') s1 s1' ->
        entails_store_aux (entails n') s2 s2' ->
        entails_result_aux (entails n') r r' ->
        satisfies n s1 s2 r t ->
        satisfies n s1' s2' r' t')
  end.
*)

Definition substore (s1 s2 : store) :=
  forall x f, store_lookup x s1 = Some f -> store_lookup x s2 = Some f.

Instance substore_refl : Reflexive substore.
Proof. unfold Reflexive, substore. auto. Qed.

Instance substore_trans : Transitive substore.
Proof. unfold Transitive, substore. auto. Qed.

Fixpoint store_diff (s1 s2 : store) :=
  match s1 with
  | [] => []
  | (x, f) :: s1' =>
      match store_lookup x s2 with
      | None => (x, f) :: store_diff s1' s2
      | Some _ => store_diff s1' s2
      end
  end.

Definition store_union (s1 s2 : store) :=
  s1 ++ s2.

Definition well_formed (s1 s2 s1' : store) :=
  forall x f,
    store_lookup x s1 = None ->
    store_lookup x s2 = Some f ->
    store_lookup x s1' = None.

Fixpoint entails (n : nat) (t t' : term) : Prop :=
  match n with
  | O => True
  | S n' =>
      entails n' t t' /\
      (forall s1 s2 r s1',
          satisfies n s1 s2 r t ->
          entails_store_aux (entails n') s1 s1' ->
          well_formed s1 s2 s1' ->
          exists s2' r',
            entails_store_aux (entails n') s2 s2' /\
            entails_result_aux (entails n') r r' /\
            satisfies n s1' s2' r' t')
  end.

Definition entails_store (n : nat) :=
  entails_store_aux (entails n).

Definition entails_result (n : nat) :=
  entails_result_aux (entails n).

Lemma entails_mono :
  forall n t t',
    entails (S n) t t' ->
    entails n t t'.
Proof. simpl. intuition idtac. Qed.

Lemma entails_store_mono :
  forall n s s',
    entails_store (S n) s s' ->
    entails_store n s s'.
Proof.
  unfold entails_store.
  unfold entails_store_aux.
  intros n s s' H_entails x f H_lookup.
  specialize (H_entails x f H_lookup) as (f' & H_lookup' & Hf').
  exists f'. split.
  - exact H_lookup'.
  - intros v. specialize (Hf' v).
    exact (entails_mono _ _ _ Hf').
Qed.

Lemma entails_result_RVal :
  forall n v, entails_result n (RVal v) (RVal v).
Proof.
  unfold entails_result, entails_result_aux.
  intros n v. left.
  exists v. auto.
Qed.

Lemma store_lookup_cons :
  forall x s f,
    store_lookup x s = Some f ->
    forall x',
      store_lookup x' s = None ->
      forall f', store_lookup x ((x', f') :: s) = Some f.
Proof.
Admitted. (* should be provable *)

Lemma satisfies_in_out :
  forall n s1 s2 r t,
    satisfies n s1 s2 r t ->
    substore s1 s2.
Proof.
  unfold substore.
  intros n.
  induction n as [| n' IHn']; intros s1 s2 r t H_sat x f H_lookup.
  { inverts H_sat. }
  inverts H_sat as.
  - eauto.
  - eauto.
  - eauto.
  - eauto.
  - eauto.
  - eauto.
  - eauto.
  - intros bubble_body k s4 kont_name H_sat1 H_notin H_sat2.
    assert (H_lookup1 := IHn' _ _ _ _ H_sat1 _ _ H_lookup).
    assert (H_lookup2 := store_lookup_cons _ _ _ H_lookup1 _ H_notin (fun v' => TReset (k v'))).
    assert (H_lookup3 := IHn' _ _ _ _ H_sat2 _ _ H_lookup2).
    exact H_lookup3.
Qed.

Lemma lookup_well_formed :
  forall s1 s2 s1',
    well_formed s1 s2 s1' ->
    forall x f,
      store_lookup x s1' = Some f ->
      store_lookup x (store_union (store_diff s2 s1) s1') = Some f.
Proof.
Admitted.

Lemma lookup_union_diff :
  forall s1 s2 s1' x f,
    store_lookup x s1 = None ->
    store_lookup x s2 = Some f ->
    store_lookup x (store_union (store_diff s2 s1) s1') = Some f.
Proof.
Admitted.

(*
(* if in s1 then use H_s1' *)
(* if notin s1 then must be in the diff of s2 and s1 and thus in the union of (diff s2 s1) and s1' *)

  H_s1' :
    forall (x : string) (f : val -> term),
    store_lookup x s1 = Some f -> exists f' : val -> term, store_lookup x s1' = Some f' /\ (forall v : val, entails n' (f v) (f' v))
  H_wf : well_formed s1 s2 s1'
  v : val
  H_sat' : satisfies n' s1 s2 r (t0 v)
  x : string
  f : val -> term
  H_lookup : store_lookup x s2 = Some f
  ============================
  exists f' : val -> term, store_lookup x (store_union (store_diff s2 s1) s1') = Some f' /\ (forall v0 : val, entails n' (f v0) (f' v0))
*)

Lemma store_diff_same :
  forall s, store_diff s s = [].
Proof.
Admitted.

Lemma split_well_formed :
  forall s1 s2 s1',
    well_formed s1 s2 s1' ->
    forall s3,
      substore s1 s3 ->
      substore s3 s2 ->
      well_formed s1 s3 s1' /\
      well_formed s3 s2 s1'.
Proof.
Admitted.

Lemma store_union_assoc :
  forall s1 s2 s3, store_union (store_union s1 s2) s3 = store_union s1 (store_union s2 s3).
Proof.
  unfold store_union.
  intros s1 s2 s3.
  rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma store_union_store_diff_trans :
  forall s1 s2 s3,
    substore s1 s2 ->
    substore s2 s3 ->
    store_union (store_diff s3 s2) (store_diff s2 s1) = store_diff s3 s1.
Proof.
Admitted.

Lemma entails_refl_obligation1 :
  forall n s1 s2 s1' r t,
    entails_store_aux (entails n) s1 s1' ->
    well_formed s1 s2 s1' ->
    satisfies n s1 s2 r t ->
    satisfies n s1' (store_union (store_diff s2 s1) s1') r t.
Proof.
  intros n s1 s2 s1' r t H_s1' H_wf H_sat.
  revert s1' H_wf H_s1'.
  induction H_sat; intros s1' H_wf H_s1'.
  - rewrite -> store_diff_same.
    simpl. eapply s_ensure.
    exact H.
  - eapply s_exists.
    apply IHH_sat; auto.
    apply entails_store_mono; auto.
  - apply entails_store_mono in H_s1'.
    assert (H_sub1 := satisfies_in_out _ _ _ _ _ H_sat1).
    assert (H_sub2 := satisfies_in_out _ _ _ _ _ H_sat2).
    destruct (split_well_formed _ _ _ H_wf _ H_sub1 H_sub2) as [H_wf1 H_wf2].
    specialize (IHH_sat1 s1' H_wf1 H_s1').
    assert (H_wf3 : well_formed s3 s2 (store_union (store_diff s3 s1) s1')).
    { admit. }
    assert (H_s3' : entails_store_aux (entails n) s3 (store_union (store_diff s3 s1) s1')).
    { admit. }
    specialize (IHH_sat2 (store_union (store_diff s3 s1) s1') H_wf3 H_s3').
    rewrite <- store_union_assoc in IHH_sat2.
    rewrite -> store_union_store_diff_trans in IHH_sat2 by auto.
    eapply s_bind_val; eauto.
  - apply entails_store_mono in H_s1'.
    eapply s_bind_bubble. auto.
  - unfold entails_store_aux in H_s1'.
    specialize (H_s1' _ _ H) as (f' & H_lookup & H_entails).
    eapply s_apply.
    { exact H_lookup. }

Instance entails_refl : forall n, Reflexive (entails n).
Proof.
  unfold Reflexive.
  intros n.
  induction n as [| n' IHn']; intros t.
  { simpl. auto. } (* base case *)
  simpl. split.
  { auto. }
  intros s1 s2 r s1' H_sat H_s1' H_wf.
  exists (store_union (store_diff s2 s1) s1'), r.
  splits.
    + unfold entails_store_aux in H_s1' |- *.
      intros x f H_lookup.
      destruct (store_lookup x s1) as [f' |] eqn:H_lookup1.
      * rewrite -> (satisfies_in_out _ _ _ _ _ H_sat _ _ H_lookup1) in H_lookup.
        injection H_lookup as ->.
        specialize (H_s1' _ _ H_lookup1) as (f' & H_lookup2 & H_f').
        exists f'.
        rewrite -> (lookup_well_formed _ _ _ H_wf _ _ H_lookup2). auto.
      * exists f.
        rewrite -> (lookup_union_diff _ _ _ _ _ H_lookup1 H_lookup). auto.
    + unfold entails_result_aux.
      destruct r as [v' | b k].
      * left. exists v'. auto.
      * right. exists b, b, k, k. auto.
    + inverts H_sat as.
  - intros HQ. (*eapply s_ensure. exact HQ.*) admit.
  - intros v H_sat'.
    eapply s_exists.
      unfold entails_store_aux in H_s1'.
      

    + (* reflexivity of result *) admit.
    + eapply s_exists.
      unfold entails_store_aux in H_s1'.
      (* we need to extend here! *)
    unfold entails in IHn'.
    Check (IHn' (t0 v)).
  + discriminate.
  + exists s1', (RVal v).
    splits.
      * auto.
      * unfold entails_result_aux.
        left. exists v. auto.
      * eapply s_ensure.
        auto.
  + specialize (IHH_sat Eq_n H_s1') as (s2' & r' & H_s2' & H_r' & H_t).
    exists s2', r'.
    splits.
    * auto.
      * auto.
      * eapply s_exists.
        eauto.
  + admit.
  + admit.
  + admit.
  + admit.
  + specialize (IHH_sat Eq_n H_s1') as (s2' & r' & H_s2' & H_r' & H_t).
    exists s2', r'.
    splits.
    * auto.
    * auto.
      * admit.
  + specialize (IHH_sat1 Eq_n H_s1') as (s2' & r' & H_s2' & H_r' & H_t).
    destruct H_r' as [H_r' | H_r'].
    { admit. }
      destruct H_r' as (b & b' & k0 & k' & H_eq & H_r' & Hb & Hk).
    Search s1'.
    admit.
Admitted.
*)
(*
    exists s2, r.
    split; [| split].
    + unfold entails_store_aux.
      intros x f H_lookup1.
      exists f.
      split; [auto |].
      intros n.
      auto.
    + unfold entails_result_aux.
      destruct r as [v | b k].
      * left. exists v. auto.
      * right. exists b, b, k, k. auto.
    + unfold entails_store_aux in H_s1'.
      auto.
Qed.*)
Admitted.

(*
Instance entails_trans : forall n, Transitive (entails n).
Proof.
  unfold Transitive.
  intros n.
  induction n as [| n' IHn']; intros t1 t2 t3 H_sat12 H_sat23.
  { simpl. exact I. }
  simpl.
  destruct H_sat12 as [H_sat12_pred H_sat12_succ].
  destruct H_sat23 as [H_sat23_pred H_sat23_succ].
  split.
  { eauto. }
  intros s1 s2 r H_sat.
  clear H_sat12_pred H_sat23_pred.
  specialize (H_sat12_succ _ _ _ H_sat).
  destruct H_sat12_succ as (s1' & s2' & r' & H_s1 & H_s2 & H_r & H_sat').
  specialize (H_sat23_succ _ _ _ H_sat').
  destruct H_sat23_succ as (s1'' & s2'' & r'' & H_s1' & H_s2' & H_r' & H_sat'').
  exists s1'', s2'', r''.
  split; [| split; [| split]].
  - unfold entails_store_aux in H_s1, H_s1' |- *.
    intros x f H_lookup.
    specialize (H_s1' _ _ H_lookup) as (f' & H_lookup' & H_f).
    specialize (H_s1 _ _ H_lookup') as (f'' & H_lookup'' & H_f').
    exists f''. eauto.
  - unfold entails_store_aux in H_s2, H_s2' |- *.
    intros x f H_lookup.
    specialize (H_s2 _ _ H_lookup) as (f' & H_lookup' & H_f).
    specialize (H_s2' _ _ H_lookup') as (f'' & H_lookup'' & H_f').
    exists f''. eauto.
  - unfold entails_result_aux in H_r, H_r' |- *.
    destruct H_r as [H_r | H_r]; destruct H_r' as [H_r' | H_r'].
    + destruct H_r as (v & Hv1 & Hv2).
      destruct H_r' as (v' & Hv'1 & Hv'2).
      left. exists v. split; congruence.
    + destruct H_r as (v & Hv1 & Hv2).
      destruct H_r' as (b & b' & k & k' & Hbk & Hb'k' & Hb & Hk).
      congruence.
    + destruct H_r' as (v & Hv1 & Hv2).
      destruct H_r as (b & b' & k & k' & Hbk & Hb'k' & Hb & Hk).
      congruence.
    + destruct H_r as (b & b' & k & k' & Hbk & Hb'k' & Hb & Hk).
      destruct H_r' as (b1 & b1' & k1 & k1' & Hbk1 & Hb'k1' & Hb1 & Hk1).
      right. exists b, b1', k, k1'.
      split; [| split; [| split]].
      * auto.
      * auto.
      * subst.
        injection Hbk1 as H_eq_b H_eq_k. subst.
        eauto.
      * subst.
        injection Hbk1 as H_eq_b H_eq_k. subst.
        eauto.
  - exact H_sat''.
Qed.
*)
(*
Instance entails_store_refl : forall n, Reflexive (entails_store n).
Proof.
  unfold Reflexive, entails_store, entails_store_aux.
  intros n s1 x f H_lookup.
  exists f.
  split; [exact H_lookup | reflexivity].
Qed.

Instance entails_store_trans : forall n, Transitive (entails_store n).
Proof.
  unfold Transitive, entails_store, entails_store_aux.
  intros n s1 s2 s3 H_s1_s2 H_s2_s3 x f H_lookup.
  specialize (H_s1_s2 x f H_lookup) as (f' & H_lookup' & H_entails).
  specialize (H_s2_s3 x f' H_lookup') as (f'' & H_lookup'' & H_entails').
  exists f''.
  split; [exact H_lookup'' | etransitivity; eauto].
Qed.
*)
Infix "====>" := Morphisms.respectful (at level 80, right associativity).
Notation Proper := Morphisms.Proper.
Notation respectful := Morphisms.respectful.
Notation impl := Program.Basics.impl.
Notation flip := Basics.flip.

(*
Lemma input_store_strengthening : forall n s1 s1' s2 r t,
    entails_store n s1 s1' ->
    satisfies (S n) s1 s2 r t ->
    satisfies (S n) s1' s2 r t.
Proof.
  unfold entails_store, entails_store_aux.
  intros n' s1 s1' s2 r t H_store H_sat.
  remember (S n') as m eqn:Eq.
  induction H_sat.
  - constructor.
  - eapply s_ensure.
*)

(*
Instance Proper_entails_entails :
  forall n,
    Proper
      (flip (entails n) ====> (entails n) ====> impl)
      (entails n).
Proof.
  unfold Proper, respectful, impl, flip.
  intros n.
  intros x y H_yx x0 y0 H_x0y0 H_xx0.
  transitivity x.
  { exact H_yx. }
  transitivity x0.
  { exact H_xx0. }
  { exact H_x0y0. }
Qed.
*)
Instance Proper_bind_entails :
  forall n,
    Proper (entails n ====> Morphisms.pointwise_relation val (entails n) ====> (entails n)) TBind.
Proof.
  unfold Proper, respectful, Morphisms.pointwise_relation.
  intros n.
  induction n as [| n' IHn']; intros x y H_entails x0 y0 H_entails0.
  { exact I. }
  simpl in *.
  destruct H_entails as [H_entails H_entails_succ].
  (*destruct H_entails0 as [H_entails0 H_entails0_succ].*)
  split.
  { apply (IHn' _ _ H_entails).
    intros a.
    specialize (H_entails0 a) as [H_entails0 _].
    exact H_entails0. }
  intros s1 s2 r s1' H_sat H_s1'.
  clear H_entails.
  inverts H_sat as.
  - intros s4 v H_sat H_sat0.
    specialize (H_entails_succ _ _ _ _ H_sat H_s1') as (s2' & r' & H_s2' & H_r' & H_sat').
    specialize (H_entails0 v) as [_ H_entails0].
    specialize (H_entails0 _ _ _ _ H_sat0 H_s2') as (s2'' & r'' & H_s2'' & H_r'' & H_sat'').
    sort.
    exists s2'', r''.
    splits.
    + exact H_s2''.
    + exact H_r''.
    + unfold entails_result_aux in H_r'.
      destruct H_r' as [H_r' | H_r'].
      { destruct H_r' as (v0 & ? & ?).
      subst.
      eapply s_bind_val.
      * exact H_sat'.
      * injection H as ->.
        exact H_sat''. }
      { admit. (* absurd case *) }
  - intros H_sat.
    specialize (H_entails_succ _ _ _ _ H_sat H_s1') as (s2' & r' & H_s2' & H_r' & H_sat').
    unfold entails_result_aux in H_r'.
    destruct H_r' as [H_r' | H_r'].
    { admit. }
    { destruct H_r' as (b0 & b' & k0 & k' & Eq & H_r' & Hb & Hk).
      injection Eq as -> ->.
      exists s2', (RBubble b' (fun v => TBind (k' v) y0)).
      splits.
      + exact H_s2'.
      + right.
        exists b0, b', (fun v : val => TBind (k0 v) x0), (fun v => TBind (k' v) y0).
        splits; auto.
        intros v.
        apply IHn'.
        auto.
        intros a.
        specialize (H_entails0 a) as (H_entails0 & _).
        exact H_entails0.
      + eapply s_bind_bubble.
        rewrite <- H_r'.
        exact H_sat'.
Admitted.
