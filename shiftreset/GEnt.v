
From ShiftReset Require Import Basics Norm ShiftFree.

(*
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
Abort.

Lemma gent_seq_ens_void_pure_l : forall n s1 f f1 P,
  (P -> gentails_under s1 n f1 f) ->
  gentails_under s1 n (ens_ \[P];; f1) f.
Proof.
Abort.

Definition precise (H:hprop) :=
  forall h1 h2, H h1 -> H h2 -> h1 = h2.

Lemma gent_req_req : forall n f1 f2 H1 H2 env,
  precise H1 ->
  req_provable H1 ->
  H2 ==> H1 ->
  gentails_under env n f1 f2 ->
  gentails_under env n (req H1 f1) (req H2 f2).
Proof.
  intros n. induction n; introv Hprecise Hreq He H.
  { applys geu_base. introv Hf1.
    applys s_req. intros * HH2 **.
    apply He in HH2.
    inverts Hf1 as Hf1. specializes* Hf1.
    inverts* H. }
  { applys geu_shift. intros.
    specializes Hreq h1. destr Hreq. inverts H0. specializes* H13.
    inverts H. specializes H7 H13.
    zap.
    applys s_req. intros.
    apply He in H5.
    specializes Hprecise H3 H5.
    subst. lets*: Fmap.union_eq_inv_of_disjoint H8. subst*. }
Qed.
*)

Lemma gent_all_r : forall n f A (fctx:A -> flow),
  (forall b, gentails n f (fctx b)) ->
  gentails n f (∀ b, fctx b).
Proof.
  intros n f A fctx H_gentails.
  induction n as [n IH] using lt_wf_ind.
  destruct n as [| n'].
  - applys ge_base.
    introv Hf.
    applys s_fall.
    intros b.
    specialize (H_gentails b).
    inverts H_gentails as H_gentails.
    auto.
  - applys ge_shift.
    + intros m Hm.
      assert (H_gentails' : forall b, gentails m f (fctx b)).
      { intros b.
        specialize (H_gentails b).
        inverts H_gentails as H_gentails_mono _.
        exact (H_gentails_mono m Hm). }
      rewrite <- Nat.lt_succ_r in Hm.
      exact (IH m Hm H_gentails').
    + introv Hf.
      (* no b : A in scope to instantiate H_gentails. Cannot be proven *)
      exists fb, fk.
      splits.
      * applys s_fall.
        intros b.
        specialize (H_gentails b).
        inverts H_gentails as _ H_gentails_succ.
        specializes H_gentails_succ Hf.
        destruct H_gentails_succ as (fb' & fk' & H_fctx & H_fb & H_fk).
        admit.
      * admit.
      * admit.
Abort.

Lemma gent_all_l : forall n f A (fctx:A -> flow),
  (exists b, gentails n (fctx b) f) ->
  gentails n (∀ b, fctx b) f.
Proof.
  intros n f A fctx H_gentails.
  destruct H_gentails as [b H_gentails].
  induction n as [n IH] using lt_wf_ind.
  inverts H_gentails as.
  - introv H_gentails.
    applys ge_base.
    introv H_fctx.
    inverts H_fctx as H_fctx.
    auto.
  - introv H_gentails_mono H_gentails_succ.
    applys ge_shift.
    + intros m Hm.
      assert (H_gentails' : gentails m (fctx b) f).
      { exact (H_gentails_mono m Hm). }
      rewrite <- Nat.lt_succ_r in Hm.
      exact (IH m Hm H_gentails').
    + introv H_fctx.
      inverts H_fctx as H_fctx.
      specialize (H_fctx b).
      specializes H_gentails_succ H_fctx.
      destruct H_gentails_succ as (fb' & fk' & Hf & H_fb & H_fk).
      exists fb', fk'.
      auto.
Qed.

Lemma gent_ex_l : forall n f A (fctx:A -> flow),
  (forall b, gentails n (fctx b) f) ->
  gentails n (fex fctx) f.
Proof.
  intros n f A fctx H_gentails.
  induction n as [n IH] using lt_wf_ind.
  destruct n as [| n'].
  - applys ge_base.
    introv H_fctx.
    inverts H_fctx as H_fctx.
    destruct H_fctx as [b H_fctx].
    specialize (H_gentails b).
    inverts H_gentails as H_gentails.
    auto.
  - applys ge_shift.
    + intros m Hm.
      assert (H_gentails' : forall b, gentails m (fctx b) f).
      { intros b.
        specialize (H_gentails b).
        inverts H_gentails as H_gentails_mono _.
        exact (H_gentails_mono m Hm). }
      rewrite <- Nat.lt_succ_r in Hm.
      exact (IH m Hm H_gentails').
    + introv H_fctx.
      inverts H_fctx as H_fctx.
      destruct H_fctx as [b H_fctx].
      specialize (H_gentails b).
      inverts H_gentails as _ H_gentails_succ.
      specializes H_gentails_succ H_fctx.
      destruct H_gentails_succ as (fb' & fk' & Hf & H_fb & H_fk).
      exists fb', fk'.
      auto.
Qed.

Lemma gent_ex_r : forall n f A (fctx:A -> flow),
  (exists b, gentails n f (fctx b)) ->
  gentails n f (fex fctx).
Proof.
  intros n f A fctx H_gentails.
  destruct H_gentails as [b H_gentails].
  induction n as [n IH] using lt_wf_ind.
  inverts H_gentails as.
  - introv H_gentails.
    applys ge_base.
    introv Hf.
    applys s_fex.
    exists b. auto.
  - introv H_gentails_mono H_gentails_succ.
    applys ge_shift.
    + intros m Hm.
      assert (H_gentails' : gentails m f (fctx b)).
      { exact (H_gentails_mono m Hm). }
      rewrite <- Nat.lt_succ_r in Hm.
      exact (IH m Hm H_gentails').
    + introv Hf.
      specializes H_gentails_succ Hf.
      destruct H_gentails_succ as (fb' & fk' & H_fctx & H_fb & H_fk).
      exists fb', fk'.
      splits; [applys s_fex | |]; eauto.
Qed.

(*
Lemma gent_seq_all_l : forall n f f1 A (fctx:A -> flow) s1,
  (exists b, gentails_under s1 n (fctx b;; f1) f) ->
  gentails_under s1 n ((∀ b, fctx b);; f1) f.
Proof.
Abort.

Lemma gent_seq_ex_l : forall n f f1 A (fctx:A -> flow) s1,
  (forall b, shift_free (fctx b)) ->
  (forall b, gentails_under s1 n (fctx b;; f1) f) ->
  gentails_under s1 n ((∃ b, fctx b);; f1) f.
Proof.
Abort.

Lemma gent_seq_ex_r : forall n f f1 A (fctx:A -> flow) s1,
  (forall b, shift_free (fctx b)) ->
  (exists b, gentails_under s1 n f (fctx b;; f1)) ->
  gentails_under s1 n f ((∃ b, fctx b);; f1).
Proof.
Abort.
*)

Lemma gent_req_l : forall n f f1 P,
  P ->
  gentails n f1 f ->
  gentails n (req \[P] f1) f.
Proof.
  intros n f f1 P HP H_gentails.
  induction n as [n IH] using lt_wf_ind.
  inverts H_gentails as.
  - introv H_gentails.
    applys ge_base.
    introv H_req.
    inverts H_req as H_req.
    applys H_gentails.
    applys H_req; heaps.
  - introv H_gentails_mono H_gentails_succ.
    applys ge_shift.
    + intros m Hm.
      assert (H_gentails' := H_gentails_mono m Hm).
      rewrite <- Nat.lt_succ_r in Hm.
      exact (IH m Hm H_gentails').
    + introv H_req.
      inverts H_req as H_req.
      applys H_gentails_succ.
      applys H_req; heaps.
Qed.

Lemma gent_req_r : forall n f f1 H,
  gentails n (ens_ H;; f) f1 ->
  gentails n f (req H f1).
Proof.
  intros n f f1 H H_gentails.
  induction n as [n IH] using lt_wf_ind.
  inverts H_gentails as.
  - introv H_gentails.
    applys ge_base.
    introv Hf.
    applys s_req.
    introv H_hp H_union H_disjoint.
    applys H_gentails.
    applys s_seq.
    * applys s_ens.
      exists vunit hp.
      heaps.
    * rewrite <- H_union.
      exact Hf.
  - introv H_gentails_mono H_gentails_succ.
    applys ge_shift.
    + intros m Hm.
      assert (H_gentails' := H_gentails_mono m Hm).
      rewrite <- Nat.lt_succ_r in Hm.
      exact (IH m Hm H_gentails').
    + introv Hf.
      assert (satisfies s1 s2 h1 h2 (shft k fb fk) (ens_ H;; f)).
      { applys s_seq.
        * applys s_ens.
          exists vunit.
          (* cannot be proven, need H hp but we can
             only get it after inverting req H f1,
             which is under exists *)
          admit.
        * admit. }
      admit.
Abort.

Lemma gent_ens_void_l : forall n f P,
  (P -> gentails n empty f) ->
  gentails n (ens_ \[P]) f.
Proof.
  intros n f P H_gentails.
  induction n as [n IH] using lt_wf_ind.
  destruct n as [| n'].
  - applys ge_base.
    introv H_ens.
    inverts H_ens as H_ens.
    destruct H_ens as (v' & h3 & Hv & HP & H_union & H_disjoint).
    rewrite -> hstar_hpure_conj in HP.
    apply hpure_inv in HP as [[Hv' HP] H_h3].
    specialize (H_gentails HP).
    inverts H_gentails as H_gentails.
    applys H_gentails.
    rewrite -> H_h3 in H_union.
    rewrite -> union_empty_r in H_union.
    rewrite -> H_union.
    rewrite -> Hv' in Hv.
    injection Hv as ->.
    apply Satisfies.empty_intro.
  - applys ge_shift.
    + intros m Hm.
      assert (H_gentails' : P -> gentails m empty f).
      { intros HP.
        specialize (H_gentails HP).
        inverts H_gentails as H_gentails_mono _.
        exact (H_gentails_mono m Hm). }
      rewrite <- Nat.lt_succ_r in Hm.
      exact (IH m Hm H_gentails').
    + introv H_ens.
      inverts H_ens as H_ens.
      destruct H_ens as (v & _ & H_absurd & _ & _).
      discriminate.
Qed.

Lemma gent_ens_single : forall n Q Q1,
  (Q1 ===> Q) ->
  gentails n (ens Q1) (ens Q).
Proof.
  intros n Q Q1 H_ent.
  induction n as [n IH] using lt_wf_ind.
  destruct n as [| n'].
  - applys ge_base.
    introv H_Q1.
    inverts H_Q1 as H_Q1.
    destruct H_Q1 as (v' & h3 & Hv & H_Q1 & H_union & H_disjoint).
    apply H_ent in H_Q1.
    applys s_ens.
    exists v', h3; eauto.
  - applys ge_shift.
    + intros m Hm.
      rewrite <- Nat.lt_succ_r in Hm.
      exact (IH m Hm).
    + introv H_absurd.
      inverts H_absurd as H_absurd.
      destruct H_absurd as (v & _ & H_absurd & _ & _ & _).
      discriminate.
Qed.

Lemma gent_ens_void_single : forall n H H1,
  (H1 ==> H) ->
  gentails n (ens_ H1) (ens_ H).
Proof.
  intros n H H1 H_ent.
  applys gent_ens_single.
  xsimpl; auto.
Qed.

Lemma gent_ens_single_pure : forall n P P1,
  (P1 -> P) ->
  gentails n (ens_ \[P1]) (ens_ \[P]).
Proof.
  intros n P P1 H_ent.
  applys gent_ens_void_single.
  xsimpl; auto.
Qed.

Lemma gent_seq_disj_l : forall n s f1 f2 f3,
  gentails_under s n f1 f3 ->
  gentails_under s n f2 f3 ->
  gentails_under s n (disj f1 f2) f3.
Proof.
Abort.

Lemma gent_seq_disj_r_l : forall n s f1 f2 f3 f4,
  gentails_under s n f3 (f1;; f4) ->
  gentails_under s n f3 (disj f1 f2;; f4).
Proof.
Abort.

Lemma gent_seq_disj_r_r : forall n s f1 f2 f3 f4,
  gentails_under s n f3 (f2;; f4) ->
  gentails_under s n f3 (disj f1 f2;; f4).
Proof.
Abort.

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
Abort.

Lemma gent_disj_l : forall n f1 f2 f3 env,
  gentails_under env n f1 f3 ->
  gentails_under env n f2 f3 ->
  gentails_under env n (disj f1 f2) f3.
Proof.
Abort.
*)
