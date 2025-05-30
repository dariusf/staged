
From ShiftReset Require Import Basics Norm ShiftFree Satisfies.

(** * Entailment sequent *)

(* For applying *)
Lemma ent_seq_defun_idem : forall s x uf f1 f2,
  Fmap.indom s x ->
  Fmap.read s x = uf ->
  entails_under s f1 f2 ->
  entails_under s (defun x uf;; f1) f2.
Proof.
  intros.
  rewrite* entails_under_seq_defun_idem.
Qed.

Lemma ent_seq_ens_pure_l : forall s1 f f1 (P:val->Prop),
  (forall r, P r -> entails_under s1 f1 f) ->
  entails_under s1 (ens (fun r => \[P r]);; f1) f.
Proof.
  unfold entails_under. intros.
  inverts H0 as H0; no_shift.
  inverts H0. heaps.
Qed.

Lemma ent_seq_defun_ens_pure_l : forall (f:var) u s1 f2 f1 (P:val->Prop),
  (forall r, P r -> entails_under s1 (defun f u;; f1) f2) ->
  entails_under s1 (defun f u;; ens (fun r => \[P r]);; f1) f2.
Proof.
  unfold entails_under. intros.
  inverts* H0.
  inverts H8.
  inverts* H9.
  inverts H7. heaps.
  applys* H.
  applys* s_seq.
  applys* s_defun.
Qed.

Lemma ent_seq_ens_void_pure_l : forall s1 f f1 P,
  (P -> entails_under s1 f1 f) ->
  entails_under s1 (ens_ \[P];; f1) f.
Proof.
  unfold entails_under. intros.
  inverts H0 as H0; no_shift.
  inverts H0. heaps.
Qed.

Lemma ent_seq_defun_ens_void_pure_l : forall s1 (f:var) u f2 f1 P,
  (P -> entails_under s1 (defun f u;; f1) f2) ->
  entails_under s1 (defun f u;; ens_ \[P];; f1) f2.
Proof.
  unfold entails_under. intros.
  inverts* H0.
  inverts H8.
  inverts* H9.
  inverts H7. heaps.
  applys* H.
  applys* s_seq.
  applys* s_defun.
Qed.

Lemma ent_req_req : forall f1 f2 H1 H2 env,
  H2 ==> H1 ->
  entails_under env f1 f2 ->
  entails_under env (req H1 f1) (req H2 f2).
Proof.
  unfold entails_under. intros.
  constructor. intros.
  inverts H3. specializes H14 H6; auto.
Qed.

Lemma ent_all_r : forall f A (fctx:A -> flow) env,
  (forall b, entails_under env f (fctx b)) ->
  entails_under env f (∀ b, fctx b).
Proof.
  unfold entails_under. intros.
  constructor. intros b.
  auto.
Qed.

Lemma ent_all_r1 : forall f A (fctx:A -> flow) s1,
  (forall b, entails_under s1 f (fctx b)) ->
  entails_under s1 f (∀ b, fctx b).
Proof.
  unfold entails_under. intros.
  constructor. intros b.
  auto.
Qed.

(* Converse is not true because f1 could depend on b *)
(* Lemma ent_seq_all_r : forall f f1 A (fctx:A -> flow) env,
  shift_free f1 ->
  entails_under env f (f1;; ∀ b, fctx b) ->
  entails_under env f (∀ b, f1;; fctx b).
Proof.
  unfold entails_under. intros.
  specializes H0 H1.
  apply fall_intro. intros.
  inverts H0 as H0. 2: { apply H in H0. false. }
  inverts H9 as H9. specializes H9 b.
  apply* s_seq.
Qed. *)

Lemma ent_all_l : forall f A (fctx:A -> flow) s1,
  (exists b, entails_under s1 (fctx b) f) ->
  entails_under s1 (∀ b, fctx b) f.
Proof.
  unfold entails_under. intros.
  destr H.
  apply H1.
  inverts H0 as H0. specializes H0 b.
  assumption.
Qed.

Lemma ent_ex_l : forall f A (fctx:A -> flow) s1,
  (forall b, entails_under s1 (fctx b) f) ->
  entails_under s1 (fex (fun b => fctx b)) f.
Proof.
  unfold entails_under. intros.
  inverts H0 as H0. destr H0.
  specializes H H1.
  auto.
Qed.

Lemma ent_ex_r : forall f A (fctx:A -> flow) s1,
  (exists b, entails_under s1 f (fctx b)) ->
  entails_under s1 f (fex (fun b => fctx b)).
Proof.
  unfold entails_under. intros.
  destr H.
  constructor. exists b.
  auto.
Qed.

Lemma ent_seq_all_l : forall f f1 A (fctx:A -> flow) s1,
  (exists b, entails_under s1 (fctx b;; f1) f) ->
  entails_under s1 ((∀ b, fctx b);; f1) f.
Proof.
  unfold entails_under. intros.
  destr H.
  apply H1.
  inverts H0 as H0.
  { inverts H0 as H0. specializes H0 b.
    applys* s_seq. }
  { inverts H0 as H0. specializes H0 b.
    apply* s_bind_sh. }
Qed.

Lemma ent_seq_ex_l : forall f f1 A (fctx:A -> flow) s1,
  (forall b, shift_free (fctx b)) ->
  (forall b, entails_under s1 (fctx b;; f1) f) ->
  entails_under s1 ((∃ b, fctx b);; f1) f.
Proof.
  unfold entails_under. intros.
  inverts H1 as H1.
  2: { inverts H1 as H1. destr H1. specializes H H2. false. }
  inverts H1 as H1. destr H1.
  applys H0 b.
  apply* s_seq.
Qed.

Lemma ent_seq_ex_r : forall f f1 A (fctx:A -> flow) s1,
  (forall b, shift_free (fctx b)) ->
  (exists b, entails_under s1 f (fctx b;; f1)) ->
  entails_under s1 f ((∃ b, fctx b);; f1).
Proof.
  unfold entails_under. intros.
  destr H0.
  specializes H2 H1.
  inverts H2 as H2. 2: { apply H in H2. false. }
  eapply s_seq.
  apply s_fex.
  exists b.
  eassumption.
  assumption.
Qed.

Lemma ent_req_l : forall f f1 P env,
  P ->
  entails_under env f1 f ->
  entails_under env (req \[P] f1) f.
Proof.
  unfold entails_under. intros.
  inverts H1.
  applys H0.
  applys H9.
  hintro. assumption.
  fmap_eq.
  fmap_disjoint.
Qed.

Lemma ent_defun_req_l : forall (f:var) u f1 f2 P env,
  P ->
  entails_under env (defun f u;; f1) f2 ->
  entails_under env (defun f u;; req \[P] f1) f2.
Proof.
  unfold entails_under. intros.
  inverts* H1.
  inverts H9.
  inverts H10.
  specializes H8.
  hintro. assumption.
  fmap_eq. reflexivity.
  fmap_disjoint.
  applys H0.
  applys* s_seq.
  applys* s_defun.
Qed.

Lemma ent_req_r : forall f f1 H env,
  entails_under env (ens_ H;; f) f1 ->
  entails_under env f (req H f1).
Proof.
  unfold entails_under. intros.
  constructor. intros.
  apply H0.
  applys s_seq (hr \+ hp) (vunit).
  { constructor. exists vunit. exists hp.
    intuition.
    rewrite hstar_hpure_l. intuition. }
  { rewrite <- H3. assumption. }
Qed.

Lemma ent_ens_void_l : forall env f P,
  (P -> entails_under env empty f) ->
  entails_under env (ens_ \[P]) f.
Proof.
  unfold entails_under. intros.
  inverts H0 as H0. destr H0.
  hinv H0. hinv H0. hinv H3.
  apply H.
  assumption.
  subst. rew_fmap. apply empty_intro.
Qed.

Lemma ent_ens_single_pure : forall env P P1,
  (P1 -> P) ->
  entails_under env (ens_ \[P1]) (ens_ \[P]).
Proof.
  unfold entails_under. intros.
  inverts H0 as H0. destr H0. hinv H0. hinv H3. hinv H0.
  constructor. exists vunit. exists empty_heap.
  splits*.
  subst*.
  hintro.
  split*.
  hintro. auto.
Qed.

Lemma ent_ens_void_single : forall env H H1,
  (H1 ==> H) ->
  entails_under env (ens_ H1) (ens_ H).
Proof.
  unfold entails_under. intros.
  inverts H2 as H2. destr H2.
  rewrite hstar_hpure_l in H2. destruct H2.
  apply H0 in H5.
  constructor. exists v. exists h3.
  intuition.
  rewrite hstar_hpure_l. intuition.
Qed.

Lemma ent_ens_single : forall env Q Q1,
  (Q1 ===> Q) ->
  entails_under env (ens Q1) (ens Q).
Proof.
  unfold entails_under. intros.
  inverts H0. destr H7.
  applys s_ens.
  exs. splits*.
  applys* H.
Qed.

Lemma ent_seq_disj_l : forall s f1 f2 f3,
  entails_under s f1 f3 ->
  entails_under s f2 f3 ->
  entails_under s (disj f1 f2) f3.
Proof.
  unfold entails_under. intros.
  inverts* H1.
Qed.

Lemma ent_seq_disj_r_l : forall s f1 f2 f3 f4,
  entails_under s f3 (f1;; f4) ->
  entails_under s f3 (disj f1 f2;; f4).
Proof.
  unfold entails_under. intros.
  specializes H H0.
  inverts H.
  { applys s_seq H9.
    applys* s_disj_l. }
  { applys s_bind_sh.
    applys* s_disj_l. }
Qed.

Lemma ent_seq_disj_r_r : forall s f1 f2 f3 f4,
  entails_under s f3 (f2;; f4) ->
  entails_under s f3 (disj f1 f2;; f4).
Proof.
  unfold entails_under. intros.
  specializes H H0.
  inverts H.
  { applys s_seq H9.
    applys* s_disj_r. }
  { applys s_bind_sh.
    applys* s_disj_r. }
Qed.

Lemma ent_disj_r_l : forall s f1 f2 f3,
  entails_under s f3 f1 ->
  entails_under s f3 (disj f1 f2).
Proof.
  unfold entails_under. intros.
  applys* s_disj_l.
Qed.

Lemma ent_disj_r_r : forall s f1 f2 f3,
  entails_under s f3 f2 ->
  entails_under s f3 (disj f1 f2).
Proof.
  unfold entails_under. intros.
  applys* s_disj_r.
Qed.

Lemma ent_disj_l : forall f1 f2 f3 env,
  entails_under env f1 f3 ->
  entails_under env f2 f3 ->
  entails_under env (disj f1 f2) f3.
Proof.
  unfold entails_under. intros.
  inverts H1 as H1; auto.
Qed.

Lemma ent_defun_req_req: forall (f:var) u f1 f2 H1 H2 env,
  H2 ==> H1 ->
  entails_under env (defun f u;; f1) f2 ->
  entails_under env (defun f u;; req H1 f1) (req H2 f2).
Proof.
  unfold entails_under. intros.
  applys s_req. intros.
  inverts* H3.
  inverts H14.
  applys H0.
  applys* s_seq.
  applys* s_defun.
  inverts H15.
  apply H in H4.
  symmetry in TEMP.
  specializes H12 H4 TEMP.
Qed.