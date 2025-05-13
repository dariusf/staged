
From ShiftReset Require Import Basics Norm ShiftFree.

(* sadly this has to be proven from scratch *)
Lemma gent_seq_defun_idem : forall n s x uf f1 f2,
  Fmap.indom s x ->
  Fmap.read s x = uf ->
  gentails_under s n f1 f2 ->
  gentails_under s n (defun x uf;; f1) f2.
Proof.
  intros.
  inverts H1.
  { apply geu_base. intros.
    inverts H1.
    inverts H10.
    lets: update_idem H H0.
    rewrite H1 in H11.
    jauto. }
  { apply geu_shift. intros.
    inverts H1. 2: { no_shift. }
    inverts H10.
    rewrites (>> update_idem H H0) in H11.
    specializes H2 H11.
    assumption. }
Qed.

Lemma gent_seq_ens_pure_l : forall n s1 f f1 (P:val->Prop),
    (forall r, P r -> gentails_under s1 n f1 f) ->
    gentails_under s1 n (ens (fun r => \[P r]);; f1) f.
Proof.
  intros n s1 f f1 P H_implies.
  (* we need imformation about the *n* *)
  destruct n as [| n'].
  - apply geu_base.
    intros s2 h1 h2 v H_sat.
    inverts H_sat as.
    intros s3 h3 v0 H_sat1 H_sat2.
    inverts H_sat1 as.
    intros (v1 & h4 & H_eq & H_v1 & H_union & H_disjoint).
    apply hpure_inv in H_v1 as [H_v1 H_h4].
    specialize (H_implies v1 H_v1).
    inverts H_implies as.
    intros H_entails.
    specialize (H_entails s2 h3 h2 v H_sat2).
    rewrite -> H_h4 in H_union.
    rewrite -> union_empty_r in H_union.
    rewrite -> H_union in H_entails.
    exact H_entails.
  - apply geu_shift.
    intros s2 h1 h2 k fb fk H_sat.
    inverts H_sat as.
    * intros s3 h3 v H_sat1 H_sat2.
      inverts H_sat1 as.
      intros (v1 & h4 & H_eq & H_v1 & H_union & H_disjoint).
      apply hpure_inv in H_v1 as [H_v1 H_h4].
      specialize (H_implies v1 H_v1).
      inverts H_implies as.
      intros H_entails.
      specialize (H_entails s2 h3 h2 k fb fk H_sat2).
      rewrite -> H_h4 in H_union.
      rewrite -> union_empty_r in H_union.
      rewrite -> H_union in H_entails.
      exact H_entails.
    * intros H_sat.
      inverts H_sat as.
      intros (v & _ & H_absurd & _).
      discriminate H_absurd.
Qed.

Lemma gent_seq_ens_void_pure_l : forall n s1 f f1 P,
  (P -> gentails_under s1 n f1 f) ->
  gentails_under s1 n (ens_ \[P];; f1) f.
Proof.
  unfold ens_.
  intros n s1 f f1 P H_implies.
  rewrite -> hstar_pure_post_pure.
  apply (gent_seq_ens_pure_l n s1 f f1 (fun r => r = vunit /\ P)).
  { intros r [_ p]. exact (H_implies p). }
Qed.

Lemma gent_req_req : forall n f1 f2 H1 H2 env,
  H2 ==> H1 ->
  gentails_under env n f1 f2 ->
  gentails_under env n (req H1 f1) (req H2 f2).
Proof.
  intros n f1 f2 H1 H2 env H_himpl H_gentails.
  (* rewrite doesn't seems to work here *)
  destruct n as [| n'].
  - apply geu_base.
    intros s2 h1 h2 v H_sat.
    inverts H_sat as H_sat.
    constructor.
    intros hp hr H_hp H_union H_disjoint.
    specialize (H_sat hp hr (H_himpl hp H_hp) H_union H_disjoint).
    inverts H_gentails as H_gentails.
    exact (H_gentails s2 hr h2 v H_sat).
  - apply geu_shift.
    intros s2 h1 h2 k fb fk H_sat.
    inverts H_sat as H_sat.
    inverts H_gentails as H_gentails.
    (* Stuck here. We need to specialize H_gentails to get fb1 and fk1.
       To specialize H_gentails, we need satisfies f1. To get satisfies f1,
       we need to specialize H_sat. To specialize H_sat, we need hp and hr,
       which we should get we constructing satisfies (req H2 f2). But to
       construct this satisfies (req H2 f2), we need to provides the value
       for fb1 and fk1.
       =>
       So we have a cycle: to get fb1 and fk1, we need to provide fb1 and fk1.
       Impossible to proceed!
     *)
Abort.

Lemma gent_all_r : forall n f A (fctx:A -> flow) env,
  (forall b, gentails_under env n f (fctx b)) ->
  gentails_under env n f (∀ b, fctx b).
Proof.
  intros n f A fctx env H_gentails.
  induction n as [| n' IHn'].
  - apply geu_base.
    intros s2 h1 h2 v H_sat.
    apply s_fall.
    intros b.
    specialize (H_gentails b).
    inverts H_gentails as H_gentails.
    exact (H_gentails s2 h1 h2 v H_sat).
  - apply geu_shift.
    (* the IH cannot be used, as H_gentails is index at (S n') and the IH
       require n'. The notation does not show the index, which may be quite
       misleading *)
    intros s2 h1 h2 k fb fk H_sat.
    (* stuck. Same problem as above *)
Abort.

Lemma gent_all_r1 : forall n f A (fctx:A -> flow) s1,
  (forall b, gentails_under s1 n f (fctx b)) ->
  gentails_under s1 n f (∀ b, fctx b).
Proof.
  intros n f A fctx s1 H_gentails.
  destruct n as [| n'].
  - apply geu_base.
    introv H_sat.
    constructor.
    intros b.
    specialize (H_gentails b).
    inverts H_gentails as H_gentails.
    auto.
  - apply geu_shift.
    introv H_sat.
    exists fb fk.
    splits.
    + constructor.
      intros b.
      specialize (H_gentails b).
      inverts H_gentails as H_gentails.
      (* stuck, circular problem again *)
Abort.

Lemma gent_all_l : forall n f A (fctx:A -> flow) s1,
  (exists b, gentails_under s1 n (fctx b) f) ->
  gentails_under s1 n (∀ b, fctx b) f.
Proof.
  intros n f A fctx s1 [b H_gentails].
  destruct n as [| n'].
  - apply geu_base.
    intros s2 h1 h2 v H_sat.
    inverts H_sat as H_sat.
    specialize (H_sat b).
    inverts H_gentails as H_gentails.
    auto.
  - apply geu_shift.
    introv H_sat.
    inverts H_sat as H_sat.
    specialize (H_sat b).
    inverts H_gentails as H_gentails.
    auto.
Qed.

Lemma gent_ex_l : forall n f A (fctx:A -> flow) s1,
  (forall b, gentails_under s1 n (fctx b) f) ->
  gentails_under s1 n (fex (fun b => fctx b)) f.
Proof.
Admitted.

Lemma gent_ex_r : forall n f A (fctx:A -> flow) s1,
  (exists b, gentails_under s1 n f (fctx b)) ->
  gentails_under s1 n f (fex (fun b => fctx b)).
Proof.
Admitted.

Lemma gent_seq_all_l : forall n f f1 A (fctx:A -> flow) s1,
  (exists b, gentails_under s1 n (fctx b;; f1) f) ->
  gentails_under s1 n ((∀ b, fctx b);; f1) f.
Proof.
Admitted.

Lemma gent_seq_ex_l : forall n f f1 A (fctx:A -> flow) s1,
  (forall b, shift_free (fctx b)) ->
  (forall b, gentails_under s1 n (fctx b;; f1) f) ->
  gentails_under s1 n ((∃ b, fctx b);; f1) f.
Proof.
Admitted.

Lemma gent_seq_ex_r : forall n f f1 A (fctx:A -> flow) s1,
  (forall b, shift_free (fctx b)) ->
  (exists b, gentails_under s1 n f (fctx b;; f1)) ->
  gentails_under s1 n f ((∃ b, fctx b);; f1).
Proof.
Admitted.

Lemma gent_req_l : forall n f f1 P env,
  P ->
  gentails_under env n f1 f ->
  gentails_under env n (req \[P] f1) f.
Proof.
Admitted.

Lemma gent_req_r : forall n f f1 H env,
  gentails_under env n (ens_ H;; f) f1 ->
  gentails_under env n f (req H f1).
Proof.
Admitted.

Lemma gent_ens_void_l : forall n env f P,
  (P -> gentails_under env n empty f) ->
  gentails_under env n (ens_ \[P]) f.
Proof.
Admitted.

Lemma gent_ens_single_pure : forall n env P P1,
  (P1 -> P) ->
  gentails_under env n (ens_ \[P1]) (ens_ \[P]).
Proof.
Admitted.

Lemma gent_ens_void_single : forall n env H H1,
  (H1 ==> H) ->
  gentails_under env n (ens_ H1) (ens_ H).
Proof.
Admitted.

Lemma gent_ens_single : forall n env Q Q1,
  (Q1 ===> Q) ->
  gentails_under env n (ens Q1) (ens Q).
Proof.
Admitted.

Lemma gent_seq_disj_l : forall n s f1 f2 f3,
  gentails_under s n f1 f3 ->
  gentails_under s n f2 f3 ->
  gentails_under s n (disj f1 f2) f3.
Proof.
Admitted.

Lemma gent_seq_disj_r_l : forall n s f1 f2 f3 f4,
  gentails_under s n f3 (f1;; f4) ->
  gentails_under s n f3 (disj f1 f2;; f4).
Proof.
Admitted.

Lemma gent_seq_disj_r_r : forall n s f1 f2 f3 f4,
  gentails_under s n f3 (f2;; f4) ->
  gentails_under s n f3 (disj f1 f2;; f4).
Proof.
Admitted.

Lemma gent_disj_r_l : forall n s f1 f2 f3,
  gentails_under s n f3 f1 ->
  gentails_under s n f3 (disj f1 f2).
Proof.
  intros.
  inverts H.
  { applys geu_base. intros.
    applys* s_disj_l. }
  { applys geu_shift. intros.
    specializes H0 H.
    zap. applys* s_disj_l. }
Qed.

Lemma gent_disj_r_r : forall n s f1 f2 f3,
  gentails_under s n f3 f2 ->
  gentails_under s n f3 (disj f1 f2).
Proof.
  intros n s f1 f2 f3 H_gentails.
  inverts H_gentails as.
  - introv H_gentails.
    apply geu_base.
    introv H_sat.
    apply s_disj_r. auto.
  - introv H_gentails.
    apply geu_shift.
    introv H_sat.
    specialize (H_gentails s2 h1 h2 k fb fk H_sat) as (fb1 & fk1 & H_sat' & H_extra).
    exists fb1 fk1.
    split.
    * apply s_disj_r. exact H_sat'.
    * exact H_extra.
Qed.

Lemma gent_disj_l : forall n f1 f2 f3 env,
  gentails_under env n f1 f3 ->
  gentails_under env n f2 f3 ->
  gentails_under env n (disj f1 f2) f3.
Proof.
Admitted.
