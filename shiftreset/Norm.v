
From ShiftReset Require Import Basics ShiftFree Satisfies Propriety Reduction ReductionOld.
(* From Staged Require Import ExtraTactics. *)

Implicit Types a v r : val.

(** * Entailment, entailment sequent, normalization *)
Lemma norm_reassoc : forall H f1 f2,
  (* shift_free f1 -> *)
  entails (req H f1;; f2) (req H (f1;; f2)).
Proof.
  unfold entails.
  intros.
  inverts H0 as H0.
  2: { (* handle shift. it may be possible to relax this *)
    apply s_req. intros.
    inverts H0 as H4.
    specializes H4 H1 H2 H3.
    apply s_bind_sh.
    assumption.
    (* apply H0 in H1. *)
    (* false. *)
  }

  (* destr H1. *)

  (* find out about req *)
  constructor. intros hp hr. intros.

  (* prove the req *)
  inverts H0 as H4.
  specializes H4 hp hr H2 ___.
  applys* s_seq h3.
Qed.

Lemma ent_seq_defun_both : forall s x uf f2 f1,
  entails_under (Fmap.update s x uf) f1 f2 ->
  entails_under s (defun x uf;; f1) (defun x uf;; f2).
Proof.
  unfold entails_under. intros.
  inverts H0 as H0. 2: { no_shift. }
  pose proof H0.
  inverts H0 as H0.
  apply H in H8.
  applys* s_seq.
Qed.

(* For rewriting *)
Lemma entails_under_seq_defun_idem : forall s x uf f1,
  Fmap.indom s x ->
  Fmap.read s x = uf ->
  entails_under s (defun x uf;; f1) f1.
Proof.
  unfold entails_under. intros.
  inverts H1. 2: { no_shift. }
  inverts H9.
  lets: update_idem H H0.
  rewrite H1 in H10.
  assumption.
Qed.

Lemma norm_ens_ens_void_split : forall H1 H2,
  entails (ens_ (H1 \* H2)) (ens_ H1;; ens_ H2).
Proof.
  unfold entails. apply satisfies_ens_ens_void_split.
Qed.

Lemma norm_ens_ens_void_combine : forall H1 H2,
  entails (ens_ H1;; ens_ H2) (ens_ (H1 \* H2)).
Proof.
  unfold entails; apply satisfies_ens_ens_void_combine.
Qed.

Lemma norm_ens_ens_void : forall H1 H2,
  bientails (ens_ (H1 \* H2)) (ens_ H1;; ens_ H2).
Proof.
  intros; split.
  - apply norm_ens_ens_void_split.
  - apply norm_ens_ens_void_combine.
Qed.

Lemma entails_under_unk : forall s (x:var) a uf,
  Fmap.read s x = uf ->
  entails_under s (unk x a) (uf a).
Proof.
  unfold entails_under. intros.
  eapply unk_inv.
  exact H.
  assumption.
Qed.

Lemma norm_rs_rs : forall f r,
  entails (rs (rs f)) (rs f).
Proof.
  unfold entails. intros.
  inverts H as H.
  false sf_rs H.
  assumption.
Qed.

Lemma norm_bind_assoc_sf: forall f fk fk1,
  shift_free f ->
  entails (bind (bind f fk) fk1)
    (bind f (fun r => bind (fk r) fk1)).
Proof.
  unfold entails. intros * Hsf * H.
  inverts H.
  { inverts H7.
    applys s_bind H6.
    applys* s_bind H9. }
  { inverts H6.
    - applys s_bind H7. applys* s_bind_sh.
    - (* we are stuck as entails does not let us
      reassociate the continuation *)
      false Hsf H4. }
Qed.

Lemma norm_bind_assoc_sf_conv: forall f fk fk1,
  shift_free f ->
  entails (bind f (fun r => bind (fk r) fk1))
    (bind (bind f fk) fk1).
Proof.
  unfold entails. intros * Hsf Hsf2 * H.
  inverts H.
  { inverts H8.
    { applys s_bind H9.
      applys s_bind H7 H6. }
    { applys s_bind_sh. applys* s_bind. } }
  { (* need to predict *)
    false Hsf H6. }
Qed.

Lemma norm_seq_assoc1 : forall f1 f2 f3,
  shift_free f1 ->
  entails (f1;; (f2;; f3)) ((f1;; f2);; f3).
Proof.
  introv Hsf1 H.
  applys* norm_bind_assoc_sf_conv.
Qed.

Lemma norm_seq_assoc2 : forall f1 f2 f3,
  shift_free f1 ->
  entails ((f1;; f2);; f3) (f1;; (f2;; f3)).
Proof.
  introv Hsf1 H.
  applys* norm_bind_assoc_sf.
Qed.

Lemma norm_seq_assoc : forall f1 f2 f3,
  shift_free f1 ->
  bientails (f1;; f2;; f3) ((f1;; f2);; f3).
Proof.
  introv Hsf1. iff H.
  - applys* norm_seq_assoc1 H.
  - applys* norm_seq_assoc2 H.
Qed.

(** Compare with [norm_bind_assoc_sf].

  Where we apply the IH shows where we need to reassociate
  the continuation. When the other arguments have shifts, we don't
  actually need to reassociate.

  Consider how these evaluate:

  Sh(...); f2; f3 ⊑ (Sh(...); f2); f3

  L: shft(..., λ x. id; f2; f3)
  R: shft(..., λ x. (id; f2); f3)
*)
Lemma norm_bind_assoc: forall n f fk fk1,
  gentails n (bind (bind f fk) fk1)
    (bind f (fun r => bind (fk r) fk1)).
Proof.
  intros n. induction n; intros.
  { applys ge_base. intros.
    inverts H.
    inverts H7.
    applys* s_bind.
    applys* s_bind. }
  { applys ge_shift. intros.
    inverts H.
    { inverts H7.
      exists fb fk0.
      splits.
      - applys* s_bind.
        applys* s_bind.
      - reflexivity.
      - reflexivity. }
    { inverts H5.
      { exists fb. exs.
        splits.
        - applys* s_bind.
          applys* s_bind_sh.
        - reflexivity.
        - reflexivity. }
      { exists fb. exs.
        splits.
        - applys* s_bind_sh.
        - reflexivity.
        - intros. simpl. applys IHn. } } }
Qed.

(* A pure fact about a result on the left of a seq doesn't contribute anything *)
Lemma norm_seq_pure_l : forall p f,
  entails (ens (fun r => \[p r]);; f) f.
Proof.
  unfold entails. intros.
  inverts H as H. 2: { no_shift. }
  inverts H. heaps.
Qed.

Lemma norm_ens_pure : forall f P,
  P -> entails (ens_ \[P];; f) f.
Proof.
  unfold entails. intros.
  inverts H0. 2: no_shift.
  inverts H8; heaps.
Qed.

Lemma norm_seq_empty : forall f,
  bientails (empty;; f) f.
Proof.
  iff H.
  { inverts H as H.
    - inverts* H. heaps.
    - no_shift. }
  { applys s_seq H. applys* empty_intro. }
Qed.

Lemma norm_seq_ens_req : forall f f1 H,
  entails (ens_ H;; f1) f ->
  entails f1 (req H f).
Proof.
  unfold entails. intros.
  apply s_req. intros.
  apply H0.
  eapply s_seq.
  apply s_ens. exists vunit hp. heaps. subst*.
Qed.

(* Lemma ent_seq_ens_dep_l : forall env f f1 p,
  (forall r1, p r1 -> entails_under env env f1 f) ->
  entails_under env env (ens (fun r => \[p r]);; f1) f.
Proof.
  unfold entails_under. intros.
  inverts H0 as H0; no_shift. destr H0.
  inverts H0 as H0. destr H0.
  hinv H0. injects H1. subst.
  rew_fmap *.
Qed. *)

Lemma norm_ens_ens_void_l : forall H Q,
  bientails (ens_ H;; ens Q) (ens (Q \*+ H)).
Proof.
  unfold entails.
  iff H0.
  { inverts H0 as H0. 2: { no_shift. }
    inverts H0 as H0.
    destr H0. hinv H0. hinv H0. injects H1.
    inverts H8 as H8. destr H8.
    applys s_ens.
    exists v (h4 \u x0).
    splits*.
    subst. rew_fmap *.
    apply* hstar_intro. }
  { inverts H0 as H0. destr H0. hinv H0.
    eapply s_seq.
    eapply s_ens.
    exists vunit.
    exists x0.
    splits*.
    { hintro. jauto. }
    { constructor. exists v x. jauto. } }
Qed.

Lemma norm_req_sep_combine : forall H1 H2 f,
  entails (req H1 (req H2 f)) (req (H1 \* H2) f).
Proof.
  unfold entails.
  intros.
  (* contravariance means we start reasoning from the assumptions in the goal *)
  apply s_req.
  intros hb hr. intros.
  apply hstar_inv in H0 as (hH1&hH2&?&?&?&?).

  (* start reasoning forward *)
  inverts H as H14.
  forwards: (H14 hH1 (hr \u hH2) H0).
  fmap_eq.
  fmap_disjoint.

  inverts H as H16.
  specializes H16 hr H5.
Qed.

Lemma norm_req_sep_split : forall H1 H2 f,
  entails (req (H1 \* H2) f) (req H1 (req H2 f)).
Proof.
  unfold entails.
  intros.

  apply s_req.
  intros hH1 hH2r. intros.
  apply s_req.
  intros hH2 hr. intros.

  inverts H as H14.
  specialize (H14 (hH1 \u hH2) hr ltac:(apply hstar_intro; auto)).
  forwards: H14.
  fmap_eq.
  fmap_disjoint.
  auto.
Qed.

Lemma norm_req_req : forall H1 H2 f,
  bientails (req (H1 \* H2) f) (req H1 (req H2 f)).
Proof.
  intros.
  split.
  - apply norm_req_sep_split.
  - apply norm_req_sep_combine.
Qed.

Lemma norm_rs_req : forall H f,
  entails (rs (req H f)) (req H (rs f)).
Proof.
  unfold entails. intros.
  apply s_req. intros.
  inverts H0 as H0.
  { eapply s_rs_sh.
    inverts H0 as H11. specializes H11 H1 H2 H3.
    eassumption. }
  { inverts H0 as H10. specializes H10 H1 H2 H3.
    apply* s_rs_val. }
Qed.

Lemma norm_rs_seq_ens : forall Q f,
  entails (rs (ens Q;; f)) (ens Q;; (rs f)).
Proof.
  unfold entails. intros.
  apply red_skip.
  apply sf_ens.
  assumption.
Qed.

Lemma norm_rs_seq_ens_void : forall H f,
  entails (rs (ens_ H;; f)) (ens_ H;; (rs f)).
Proof.
  unfold entails. intros.
  apply red_skip.
  apply sf_ens.
  assumption.
Qed.

Lemma norm_seq_req_emp : forall f,
  bientails (req \[] f) f.
Proof.
  unfold entails. split; intros.
  { apply req_empty_inv in H. assumption. }
  { apply req_empty_intro. assumption. }
Qed.

Lemma entails_ens_seq : forall H1 H2 f1 f2,
  H1 ==> H2 ->
  entails f1 f2 ->
  entails (ens_ H1;; f1) (ens_ H2;; f2).
Proof.
  unfold entails.
  intros.
  inverts H3 as H3; no_shift. destr H3.
  lets: satisfies_ens_void H H3.
  applys* s_seq h3.
Qed.

(* This is not very useful for rewriting.
  The sequent form [ent_req_req] is more interesting. *)
Lemma entails_req1 : forall H1 H2 f1 f2,
  H2 ==> H1 ->
  entails f1 f2 ->
  entails (req H1 f1) (req H2 f2).
Proof.
  unfold entails. intros.
  apply s_req. intros.
  apply H in H4.
  inverts H3.
  specializes H14 hr H4.
Qed.

Lemma entails_seq : forall f f1 f2,
  shift_free f ->
  entails f1 f2 ->
  entails (f;; f1) (f;; f2).
Proof.
  unfold entails.
  intros.
  inverts H1 as H1. 2: { apply H in H1. false. }
  apply* s_seq.
Qed.

Lemma norm_seq_ens_empty : forall f,
  bientails (ens_ \[];; f) f.
Proof.
  unfold bientails. intros.
  iff H.
  { inverts H as H; no_shift.
    inverts H as H. destr H.
    hinv H. hinv H. hinv H2.
    subst. rew_fmap *. }
  { eapply s_seq.
    eapply ens_void_empty_intro.
    assumption. }
Qed.

Lemma norm_seq_ens_sl_ex: forall A (c:A->hprop) f,
  entails (ens_ (\exists b, c b);; f)
    (∃ b, ens_ (c b);; f).
Proof.
  unfold entails. intros.
  inverts H as H. 2: no_shift.
  inverts H as H. destr H.
  hinv H. hinv H.
  apply hexists_inv in H2. destr H2.
  constructor. exists x1.
  applys* s_seq s3 (h1 \u x0) vunit.
  - constructor. exs. splits*. hintro; jauto.
  - subst. rew_fmap *.
Qed.

Lemma norm_seq_all_r: forall (A:Type) (f:A->flow) f1,
  shift_free f1 ->
  entails (f1;; (∀ x:A, f x)) (∀ x:A, f1;; f x).
Proof.
  unfold entails. introv Hsf H0.
  inverts H0. 2: { false Hsf H6. }
  applys s_fall. intros.
  inverts H8. specializes H5 b.
  applys* s_seq.
Qed.

Lemma norm_rs_ex : forall A ctx,
  entails (rs (∃ (x:A), ctx x)) (∃ (x:A), rs (ctx x)).
Proof.
  unfold entails. intros.
  inverts H as H.
  {
    inverts H as H. destr H.
    constructor. exists b.
    eapply s_rs_sh; jauto. }
  { inverts H as H. destr H.
    constructor. exists b.
    apply s_rs_val.
    assumption. }
Qed.

Lemma norm_rs_all : forall A ctx,
  entails (rs (∀ (x:A), ctx x)) (∀ (x:A), rs (ctx x)).
Proof.
  unfold entails. intros.
  inverts H as H.
  { constructor. intros b.
    inverts H as H. specializes H b.
    eapply s_rs_sh; jauto. }
  { constructor. intros b.
    inverts H as H. specializes H b.
    apply s_rs_val.
    assumption. }
Qed.

(* norm_req_ex can't be proved *)
Lemma norm_req_all : forall H (A:Type) (fctx:A->flow),
  entails (req H (∀ b, fctx b)) (∀ b, req H (fctx b)).
Proof.
  unfold entails. intros.
  applys s_fall. intros.
  applys s_req. intros.
  inverts H0. specializes H11 H1 H2 H3.
  inverts* H11.
Qed.

Lemma norm_req_pure_l : forall P f,
  P -> bientails (req \[P] f) f.
Proof.
  unfold bientails. intros.
  iff H0.
  { apply req_pure_inv in H0.
    assumption.
    assumption. }
  { apply req_pure_intro. auto. }
Qed.

Lemma norm_seq_ex_l : forall f1 (A:Type) (fctx:A->flow),
  entails ((∃ b, fctx b);; f1) (∃ b, fctx b;; f1).
Proof.
  unfold entails. intros.
  inverts H.
  { inverts H7. destr H5.
    applys s_fex. exists b.
    applys* s_seq. }
  { inverts H6. destr H5.
    applys s_fex. exists b.
    applys* s_bind_sh. }
Qed.

Lemma norm_seq_ex_r: forall (A:Type) (f:A->flow) f1,
  shift_free f1 ->
  entails (f1;; (∃ x:A, f x)) (∃ x:A, f1;; f x).
Proof.
  unfold entails. introv Hsf H0.
  inverts H0. 2: { false Hsf H6. }
  inverts H8. destr H5.
  applys s_fex. exists b.
  applys* s_seq.
Qed.

Lemma norm_rs_seq_ex_r : forall f1 A (fctx:A -> flow),
  shift_free f1 ->
  entails (rs (f1;; (∃ b, fctx b)))
    (∃ b, rs (f1;; (fctx b))).
Proof.
  intros.
  rewrite norm_seq_ex_r.
  2: { assumption. }
  lets H1: norm_rs_ex.
  specializes H1 A (fun b => f1;; fctx b).
Qed.

Lemma norm_rs_seq_distr : forall f1 f2,
  shift_free f1 ->
  entails (rs (f1;; f2)) (rs f1;; rs f2).
Proof.
  unfold entails. intros.
  inverts H0 as H0.
  { (* f1;; f2 has a shift *)
    inverts H0 as H0.
    2: { false H H0. }
    eapply s_seq.
    apply s_rs_val. eassumption.
    eapply s_rs_sh. eassumption.
    eassumption. }
  { inverts H0 as H0.
    eapply s_seq.
    apply s_rs_val.
    eassumption.
    apply s_rs_val.
    eassumption. }
Qed.

Lemma norm_ens_ens_void_swap : forall H Q f,
  bientails (ens Q;; ens_ H;; f) (ens_ H;; ens Q;; f).
Proof.
  iff H0.
  { inverts H0. 2: { inverts H7. destr H6. discriminate. }
    inverts H8. destr H6. injects H0.
    inverts H9. 2: { inverts H10. destr H9. discriminate. }
    inverts H11. destr H9. injects H0. hinv H3. hinv H0.
    applys s_seq.
    applys s_ens.
    { exists vunit x0. splits*. hintro. splits*. }
    applys s_seq H12.
    applys s_ens.
    { exists v0 h0. splits*. } }
  { inverts H0. 2: { inverts H7. destr H6. discriminate. }
    inverts H8. destr H6. injects H0.
    inverts H9. 2: { inverts H10. destr H9. discriminate. }
    inverts H11. destr H9. injects H0. hinv H1. hinv H0.
    applys s_seq.
    applys s_ens.
    { exists v1 h5. splits*. }
    applys s_seq H12.
    applys s_ens.
    { exists vunit x0. splits*. hintro. splits*. } }
Qed.

Lemma norm_bind_seq : forall f fk v,
  shift_free f ->
  det f ->
  flow_res f v ->
  entails (bind f fk) (f;; fk v).
Proof.
  unfold flow_res, entails. intros * Hsf Hd Hfr * H.
  inverts H. 2: { false Hsf H6. }
  specializes Hfr s1 s3 h1 h3.
  specializes Hd H7 Hfr. injects Hd.
  applys s_seq H7.
  assumption.
Qed.

Lemma norm_bind_seq1 : forall f fk v,
  shift_free f ->
  flow_res1 f v ->
  entails (bind f fk) (f;; fk v).
Proof.
  unfold entails. intros * Hsf Hfr * H.
  inverts H. 2: { false Hsf H6. }
  specializes Hfr H7.
  subst.
  applys* s_seq H7.
Qed.

(** Similar to [norm_seq_assoc].
  We only need one [shift_free] premise here
  because we're rewriting only in one direction. *)
Lemma norm_bind_seq_assoc : forall fk f1 f2,
  shift_free f1 ->
  entails (bind (f1;; f2) fk) (f1;; bind f2 fk).
Proof.
  unfold entails. intros * Hsf1 * H.
  inverts H.
  { inverts H7.
    applys s_seq H6.
    applys* s_bind. }
  { inverts H6.
    - applys s_seq H7.
      applys* s_bind_sh.
    - false Hsf1 H4. }
Qed.

(* TODO can this be generalised (to [norm_bind_pure])? *)
Lemma norm_bind_val : forall fk v,
  entails (bind (ens (fun r => \[r = v])) fk) (fk v).
Proof.
  unfold entails. intros * H.
  inverts H. 2: { false sf_ens H6. }
  inverts H7. destr H5. injects H. hinv H0. subst. rew_fmap.
  assumption.
Qed.

(* TODO something more general would be to push disjunction out *)
Lemma norm_bind_disj_val : forall fk v1 v2,
  entails (bind (ens (fun r => \[r = v1 \/ r = v2])) fk)
    (disj (fk v1) (fk v2)).
Proof.
  unfold entails. intros * H.
  inverts H. 2: { false sf_ens H6. }
  inverts H7. heaps.
  destruct H; subst.
  - apply* s_disj_l.
  - apply* s_disj_r.
Qed.

(* Lemma norm_bind_pure : forall fk (P:val->Prop) Q,
  entails (bind (ens (fun r => \[P r])) (fun v => ens (Q)))
    (ens (fun r => Q r * \[P r])).
Proof.
  unfold entails. intros * H.
  inverts H. 2: { false sf_ens H6. }
  inverts H7. destr H5. injects H. hinv H0. subst. rew_fmap.
  assumption.
Qed. *)

Lemma norm_bind_ens_void : forall fk H,
  entails (bind (ens_ H) fk) (seq (ens_ H) (fk vunit)).
Proof.
  unfold entails. intros * H.
  inverts H.
  { pose proof H8.
    inverts H8. destr H7. hinv H2. hinv H2. injects H1. subst.
    applys* s_seq. }
  { false sf_ens_ H7. }
Qed.

Lemma norm_bind_req : forall H f fk,
  entails (bind (req H f) fk) (req H (bind f fk)).
Proof.
  unfold entails. intros * H.
  applys s_req. intros.
  inverts H.
  2: { inverts H10. specializes H11 H1 H2 H3. applys* s_bind_sh. }
  { inverts H11. specializes H10 H1 H2 H3.
    applys* s_bind. }
Qed.

Lemma norm_bind_disj: forall f1 f2 fk,
  entails (bind (disj f1 f2) fk) (disj (bind f1 fk) (bind f2 fk)).
Proof.
  unfold entails. intros.
  inverts H.
  { inverts H7.
    - applys s_disj_l. applys* s_bind.
    - applys s_disj_r. applys* s_bind. }
  {
    inverts H6.
    - applys s_disj_l. applys* s_bind_sh.
    - applys s_disj_r. applys* s_bind_sh. }
Qed.

Lemma norm_rs_disj: forall f1 f2,
  entails (rs (disj f1 f2)) (disj (rs f1) (rs f2)).
Proof.
  applys red_rs_float2.
Qed.

Lemma norm_seq_disj_r : forall f1 f2 f3,
  shift_free f1 ->
  entails (f1;; disj f2 f3)
    (disj (f1;; f2) (f1;; f3)).
Proof.
  unfold entails. introv Hsf H.
  inverts H. 2: { false Hsf H6. }
  inverts H8.
  - applys s_disj_l; applys* s_seq.
  - applys s_disj_r; applys* s_seq.
Qed.

Lemma norm_seq_ens_ens_pure : forall H P,
  entails (ens_ H;; ens_ \[P]) (ens_ \[P];; ens_ H).
Proof.
  unfold entails. intros.
  inverts H0. 2: no_shift.
  inverts H8.
  inverts H9.
  applys s_seq; applys s_ens; heaps.
Qed.

Lemma norm_bind_all_l : forall (A:Type) (fk1:A->flow) fk,
  entails (bind (∀ (b:A), fk1 b) fk) (∀ (b:A), bind (fk1 b) fk).
Proof.
  unfold entails. introv H.
  inverts H.
  { inverts H7. applys s_fall. intros b. specializes H5 b.
    applys* s_bind. }
  { inverts H6. applys s_fall. intros b. specializes H5 b.
    applys* s_bind_sh. }
Qed.

Lemma norm_bind_ex_l : forall (A:Type) (fk1:A->flow) fk,
  entails (bind (∃ (b:A), fk1 b) fk) (∃ (b:A), bind (fk1 b) fk).
Proof.
  unfold entails. introv H.
  inverts H.
  { inverts H7. applys s_fex. destruct H5 as (b&?). exists b.
    applys* s_bind. }
  { inverts H6. applys s_fex. destruct H5 as (b&?). exists b.
    applys* s_bind_sh. }
Qed.

(* unsure about 2-parameter statement *)
Lemma norm_bind_all_r : forall (A:Type) f (fk:A->val->flow),
  shift_free f ->
  entails (bind f (fun r => ∀ (x:A), fk x r)) (∀ (x:A), bind f (fk x)).
Proof.
  unfold entails. introv Hsf H.
  inverts H. 2: { false Hsf H6. }
  inverts H8.
  applys s_fall. intros b. specializes H5 b. apply* s_bind.
Qed.

Lemma norm_bind_ex_r : forall (A:Type) f (fk:A->val->flow),
  shift_free f ->
  entails (bind f (fun r => ∃ (x:A), fk x r)) (∃ (x:A), bind f (fk x)).
Proof.
  unfold entails. introv Hsf H.
  inverts H. 2: { false Hsf H6. }
  inverts H8.
  applys s_fex. destruct H5 as (b&?). exists b. apply* s_bind.
Qed.

Lemma norm_rearrange_ens : forall H P (P1:val->Prop),
  entails (ens (fun r => H \* \[P /\ P1 r]))
  (ens_ \[P];; ens_ H;; ens (fun r => \[P1 r])).
Proof.
  unfold entails. intros.
  inverts H0.
  heaps.
  applys s_seq.
  { applys s_ens. heaps. }
  applys s_seq.
  { applys s_ens. heaps. }
  { applys s_ens. heaps. }
Qed.

Lemma norm_bind_seq_def: forall f1 f2,
  entails (bind f1 (fun _ => f2)) (f1;; f2).
Proof.
  intros.
  fold (f1;; f2).
  reflexivity.
Qed.

Lemma norm_ens_pure_conj: forall (P:val->Prop) (P1:Prop),
  entails
    (ens (fun r => \[P1 /\ P r]))
    (ens_ \[P1];; ens (fun r => \[P r])).
Proof.
  unfold entails. intros.
  inverts H.
  heaps.
  applys s_seq.
  applys s_ens_. heaps.
  applys s_ens. heaps.
Qed.

Lemma norm_ens_void_hstar_pure_l: forall P H,
  entails
    (ens_ (\[P] \* H))
    (ens_ \[P];; ens_ H).
Proof.
  unfold entails. intros.
  inverts H0.
  applys s_seq.
  - applys s_ens_. heaps.
  - applys s_ens. heaps.
Qed.

Lemma norm_ens_void_hstar_pure_r: forall P H,
  entails
    (ens_ (H \* \[P]))
    (ens_ \[P];; ens_ H).
Proof.
  unfold entails. intros.
  inverts H0.
  applys s_seq.
  - applys s_ens_. heaps.
  - applys s_ens. heaps.
Qed.

Lemma norm_ens_pure_ex: forall (A:Type) (P:A->val->Prop),
  entails
    (ens (fun r => \[exists b, P b r]))
    (∃ b, ens (fun r => \[P b r])).
Proof.
  unfold entails. intros.
  inverts H.
  heaps.
  applys s_fex. exists b.
  applys s_ens.
  heaps.
Qed.

Lemma norm_defun_discard_id: forall s f u,
  ~ Fmap.indom s f ->
  entails_under s (defun f u;; discard f) empty.
Proof.
  unfold entails_under. intros.
  inverts H0. 2: no_shift.
  inverts H8.
  inverts H9.
  rewrites* remove_update.
  applys empty_intro.
Qed.

Lemma norm_seq_defun_ens: forall f u Q,
  entails (defun f u;; ens_ Q) (ens_ Q;; defun f u).
Proof.
  unfold entails. intros.
  inverts H. 2: no_shift.
  inverts H7.
  inverts H8. destr H5. hinv H0. hinv H0.
  applys s_seq.
  - applys s_ens. heaps.
  - heaps. applys* s_defun.
Qed.

Lemma norm_seq_defun_req: forall f u f1 H,
  entails (defun f u;; req H f1) (req H (defun f u;; f1)).
Proof.
  unfold entails. intros.
  inverts H0. 2: no_shift.
  inverts H8.
  applys s_req. intros.
  inverts H9. specializes H11 H0 H1 H2.
  applys* s_seq.
  applys* s_defun.
Qed.

Lemma norm_disj_defun_l: forall f1 f2 f u,
  entails
    (defun f u;; disj f1 f2)
    (disj (defun f u;; f1) (defun f u;; f2)).
Proof.
  unfold entails. intros.
  inverts H. 2: no_shift.
  inverts H7.
  inverts H8.
  - applys s_disj_l.
    applys* s_seq.
    applys* s_defun.
  - applys s_disj_r.
    applys* s_seq.
    applys* s_defun.
Qed.

Lemma norm_seq_defun_unk: forall f u v,
  entails (defun f u;; unk f v) (defun f u;; u v).
Proof.
  unfold entails. intros.
  inverts H. 2: no_shift.
  inverts H7.
  inverts H8.
  applys s_seq.
  - applys* s_defun.
  - rewrite fmap_read_update in H7.
    assumption.
Qed.
