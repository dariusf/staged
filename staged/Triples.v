
From Staged Require Import Logic.
(* Automation *)
Local Open Scope string_scope.

Import Soundness.
Import HistoryTriples.

Lemma sem_padd: forall x y,
  spec_assert (padd (pval (vint x)) (pval (vint y)))
    (ens (fun r => \[r = vint (x+y)])).
Proof.
  unfold spec_assert, pair_valid_under. intros.
  inverts H0.
  applys s_ens. exs.
  splits*.
  hintro. reflexivity.
  fmap_eq.
Qed.

Lemma hist_padd: forall x y fh,
  hist_triple fh (padd (pval (vint x)) (pval (vint y)))
    (fh;; ens (fun r => \[r = vint (x+y)])).
Proof.
  intros.
  applys hist_frame_sem (@sem_padd x).
Qed.

(** Simpler, more elementary alternative to biabduction *)
Lemma norm_ens_forall_req: forall l v f,
  entails (ens_ (l ~~> v);; ∀ y, req (l ~~> y) f) f.
Proof.
  unfold entails. intros.
  inverts H.
  inverts H7. specializes H4 v.
  inverts H6. destr H5. hinv H0. hinv H0.
  inverts H4. specializes H13 x0 h1.
Qed.

(** Like [norm_ens_forall_req] but for a dependent body *)
Lemma norm_ens_forall_req_dep: forall l v f,
  entails (ens_ (l ~~> v);; ∀ y, req (l ~~> y) (f y)) (f v).
Proof.
  unfold entails. intros.
  inverts H.
  inverts H7. specializes H4 v.
  inverts H6. destr H5. hinv H0. hinv H0.
  inverts H4. specializes H13 x0 h1.
Qed.

(* this is not true generally for heaps, unless e does not access H *)
Lemma hist_triple_req_ens: forall f H e fh,
  hist_triple (fh;; ens_ H) e f ->
  hist_triple fh e (req H f).
Proof.
  intros.
  applys hist_pre_result.
  unfold hist_triple in *. intros.
  applys s_req. intros.
  specializes H0 penv env h0 (h1 \u hp) (norm vunit).
  forward H0.
  {
    (* hp satisfies H.
      need to show that e's execution does not rely on hp.
      so (h1-hp)-e->(h2-hp) still gives the same result.
    *)
    admit.
  }
Abort.

(* Move pure req into history *)
Lemma hist_triple_req_ens_pure: forall f P e fh,
  hist_triple (fh;; ens_ \[P]) e f ->
  hist_triple fh e (req \[P] f).
Proof.
  intros.
  applys hist_pre_result.
  unfold hist_triple in *. intros.
  applys s_req. intros. hinv H3.
  specializes H penv env h0 h1 h2.
  specializes H v (norm vunit).
  forward H.
  {
    inverts H0.
    inverts H14. destr H11. hinv H7. hinv H7. hinv H9.
    applys s_seq H13.
    subst. rew_fmap *.
    applys* ens_void_pure_intro P. }
  specializes H H1 H2.
  subst. rew_fmap *.
Qed.

Lemma hist_triple_passign_update: forall a l v,
  hist_triple (ens_ (l ~~> a))
    (passign (pval (vloc l)) (pval v))
    (ens_ (l ~~> v)).
Proof.
  unfold hist_triple, pair_valid_under. intros.
  inverts H1.
  inverts H. destr H6. hinv H1. hinv H1.
  hinv H3.
  subst. rew_fmap *.
  clear H5 H7.
  rewrites (>> union_comm_of_disjoint H4).
  rewrite <- Fmap.update_eq_union_single.
  rewrite update_precedence.
  apply Fmap.disjoint_sym in H4.
  lets: Fmap.disjoint_single_set v H4.
  applys s_ens.
  exists vunit, (Fmap.single l v). splits*.
  hintro. splits*.
  applys hsingle_intro.
  unfold Fmap.update.
  applys union_comm_of_disjoint H.
Qed.

Example ex0: forall a l,
  hist_triple (ens_ (l~~>vint a))
    (plet "x" (pderef (pval (vloc l)))
      (plet "y" (padd (pval (vint 1)) (pvar "x"))
        (passign (pval (vloc l)) (pvar "y"))))
    (ens_ (l~~>vint (a+1))).
Proof.
  intros.
  applys hist_plet.
  applys hist_pderef.
  {
    instantiate (1 := vint a).
    unfold flow_res.
    intros. inverts H.
    inverts H6. destr H4. hinv H0. hinv H0.
    inverts H7. specializes H13 (vint a).
    inverts H13.
    specializes H12 x0 h1 H2.
    subst. forward H12. fmap_eq.
    forward H12. fmap_disjoint.
    inverts H12. destr H7.
    hinv H0. hinv H0. subst. congruence.
  }
  simpl.

  applys hist_plet.
  applys hist_padd.
  {
    instantiate (1 := vint (1+a)).
    unfold flow_res.
    intros. inverts H.
    inverts H7. destr H4.
    inverts H0.
    auto.
  }
  simpl.
  rewrite <- hist_pre_result.
  applys hist_conseq.

  rewrite norm_ens_forall_req_dep.
  rewrite norm_ens_ens_combine.

  assert (entails (ens (fun r => \exists r1, (\[r1 = vint a] \* l ~~> vint a) \* \[r = vint (1 + a)]);; empty) (ens_ (l~~>vint a))).
  {
    unfold entails.
    intros.
    inverts H.
    inverts H6.
    inverts H7.
    heaps.
    applys s_ens.
    zap. hintro.
    zap. hintro.
  }
  rewrite H.
  reflexivity.
  reflexivity.

  applys_eq hist_triple_passign_update.
  f_equal. f_equal. f_equal. lia.
Qed.
