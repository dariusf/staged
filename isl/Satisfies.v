
From ISL Require Import Basics.

(** * Lemmas about satisfies *)
Lemma ens_void_pure_intro : forall P s h,
  P -> satisfies s s h h (norm vunit) (ens_ \[P]).
Proof.
  intros.
  unfold ens_.
  constructor.
  exists vunit.
  exists empty_heap.
  splits*.
  { rewrite hstar_hpure_r.
    intuition.
    apply hpure_intro.
    reflexivity. }
Qed.

Lemma ens_pure_intro : forall P s h r,
  P r -> satisfies s s h h (norm r) (ens (fun v => \[P v])).
Proof.
  intros.
  constructor.
  exists r.
  exists empty_heap.
  hint hpure_intro.
  splits*.
Qed.

Lemma ens_void_pure_inv : forall P s1 s2 h1 h2 R,
  satisfies s1 s2 h1 h2 R (ens_ \[P]) ->
  P /\ h1 = h2 /\ s1 = s2 /\ R = norm vunit.
Proof.
  intros.
  inverts H as H. destr H.
  rewrite hstar_hpure_l in H. destr H.
  apply hpure_inv in H4. destr H4. subst.
  intuition.
Qed.

Lemma empty_intro : forall s1 h1,
  satisfies s1 s1 h1 h1 (norm vunit) empty.
Proof.
  intros.
  unfold empty, ens_.
  constructor.
  exists vunit.
  exists empty_heap.
  splits*.
  { rewrite hstar_hpure_l.
    intuition.
    apply hpure_intro.
    constructor. }
Qed.

Lemma empty_inv : forall s1 s2 h1 h2 R,
  satisfies s1 s2 h1 h2 R empty ->
  s1 = s2 /\ h1 = h2 /\ R = norm vunit.
Proof.
  unfold empty.
  intros.
  apply ens_void_pure_inv in H.
  intuition.
Qed.

Lemma ens_store_frame : forall s1 s2 h1 h2 R x uf Q,
  satisfies s1 s2 h1 h2 R (ens Q) ->
  satisfies (Fmap.update s1 x uf) (Fmap.update s2 x uf) h1 h2 R (ens Q).
Proof.
  intros.
  inverts H as H. destr H.
  subst.
  apply s_ens. exs.
  intuition eauto.
Qed.

Lemma ens_req_inv : forall s1 s2 h1 h2 R H f,
  satisfies s1 s2 h1 h2 R (ens_ H;; req H f) ->
  satisfies s1 s2 h1 h2 R f.
Proof.
  intros.
  inverts H0 as H0.
  inverts H0 as H0. destr H0. hinv H0. hinv H0.
  inverts H8 as H15. specializes H15 H3.
  subst. rew_fmap *.
Qed.

Lemma req_empty_inv : forall s1 s2 h1 h2 R f,
  satisfies s1 s2 h1 h2 R (req \[] f) ->
  satisfies s1 s2 h1 h2 R f.
Proof.
  intros.
  inverts H as H6. specializes H6 empty_heap h1 ___.
  apply hempty_intro.
Qed.

Lemma req_empty_intro : forall s1 s2 h1 h2 R f,
  satisfies s1 s2 h1 h2 R f ->
  satisfies s1 s2 h1 h2 R (req \[] f).
Proof.
  intros.
  apply s_req. intros.
  hinv H0.
  subst. rew_fmap *.
Qed.

Lemma ens_empty_intro : forall s1 h1 r,
  satisfies s1 s1 h1 h1 (norm r) (ens (fun r => \[])).
Proof.
  intros.
  apply s_ens.
  exists r empty_heap.
  intuition fmap_eq.
  constructor.
Qed.

Lemma ens_void_empty_intro : forall s1 h1,
  satisfies s1 s1 h1 h1 (norm vunit) (ens_ \[]).
Proof.
  intros.
  constructor.
  exs.
  splits*.
  hintro.
  splits*.
  hintro.
  rew_fmap.
  reflexivity.
Qed.

Lemma satisfies_ens_void : forall H1 H2 s1 s2 h1 h2 R,
  H1 ==> H2 ->
  satisfies s1 s2 h1 h2 R (ens_ H1) ->
  satisfies s1 s2 h1 h2 R (ens_ H2).
Proof.
  intros.
  inverts H0 as H3. destruct H3 as (v&h3&?&?&?&?).
  constructor. exists v. exists h3.
  intuition.
  rewrite hstar_hpure_l in H3.
  rewrite hstar_hpure_l.
  intuition.
Qed.

Lemma ens_inv : forall s1 s2 h1 h2 R Q,
  satisfies s1 s2 h1 h2 R (ens Q) ->
  s1 = s2.
Proof.
  intros.
  inverts H as H. destr H.
  reflexivity.
Qed.

Lemma unk_inv : forall s1 s2 h1 h2 R x a uf,
  Fmap.read s1 x = uf ->
  satisfies s1 s2 h1 h2 R (unk x a) ->
  satisfies s1 s2 h1 h2 R (uf a).
Proof.
  intros.
  inverts H0 as H0.
  rewrite H in H0.
  assumption.
Qed.

Lemma satisfies_ens_ens_void_split : forall H1 H2 s1 s2 h1 h2 R,
  satisfies s1 s2 h1 h2 R (ens_ (H1 \* H2)) ->
  satisfies s1 s2 h1 h2 R (ens_ H1;; ens_ H2).
Proof.
  intros.
  inverts H as H. destruct H as (v&h3&H3&H4&H5&H6).
  rewrite hstar_hpure_l in H4. destruct H4 as (H4&H7).
  (* h3 is the heap that H1 and H2 together add *)
  (* find the intermediate heap *)
  apply hstar_inv in H7. destruct H7 as (h0&h4&H8&H9&H10&H11).
  (* H1 h0, H2 h4 *)
  applys s_seq.
  { constructor. exists vunit. exists h0. intuition. rewrite hstar_hpure_l. intuition. }
  { constructor. exists v. exists h4. intuition. rewrite hstar_hpure_l. intuition. }
Qed.

Lemma satisfies_ens_ens_void_combine : forall H1 H2 s1 s2 h1 h2 R,
  satisfies s1 s2 h1 h2 R (ens_ H1;; ens_ H2) ->
  satisfies s1 s2 h1 h2 R (ens_ (H1 \* H2)).
Proof.
  intros.
  inverts H as H. destr H.
  (* give up on careful reasoning *)
  inverts H as H. destr H.
  inverts H9 as H9. destr H9.
  hinv H. hinv H. hinv H6. hinv H6.
  applys_eq s_ens_. injects H0. subst. reflexivity.
  exists (h0 \u h4).
  splits*.
  subst.
  hintro; jauto.
  rew_fmap *.
  rew_fmap *.
Qed.

Lemma fall_intro : forall s1 s2 h1 h2 R A (fctx:A -> flow),
  (forall b, satisfies s1 s2 h1 h2 R (fctx b)) ->
  satisfies s1 s2 h1 h2 R (∀ b, fctx b).
Proof.
  intros.
  constructor.
  auto.
Qed.

Lemma req_pure_inv: forall s1 s2 h1 h2 R P f,
  P ->
  satisfies s1 s2 h1 h2 R (req \[P] f) ->
  satisfies s1 s2 h1 h2 R f.
Proof.
  intros.
  inverts H0 as H7.
  specializes H7 empty_heap h1. apply H7.
  hintro. assumption. fmap_eq. fmap_disjoint.
Qed.

Lemma req_pure_intro : forall s1 s2 h1 h2 R P f,
  (P -> satisfies s1 s2 h1 h2 R f) ->
  satisfies s1 s2 h1 h2 R (req \[P] f).
Proof.
  intros.
  apply s_req. intros.
  hinv H0. subst. rew_fmap.
  apply* H.
Qed.
