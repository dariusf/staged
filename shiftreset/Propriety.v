
From Stdlib Require Import Classes.RelationClasses.
From Stdlib Require Morphisms Program.Basics.

From ShiftReset Require Import Basics ShiftFree.

Local Open Scope string_scope.

(* From Staged Require Export HeapF.
From Staged Require Export LibFmap.
From Staged Require Export ExtraTactics. *)


Infix "====>" := Morphisms.respectful (at level 80, right associativity).
Notation Proper := Morphisms.Proper.
Notation respectful := Morphisms.respectful.
Notation impl := Program.Basics.impl.
Notation flip := Basics.flip.

(** Incantations for setoid rewriting *)
Section Propriety.

  (*
    We have to prove (at most) m*n instances,
    for the m things we want to rewrite with,
    and the n things we want to rewrite in:

    |     | ⊑ | ⊢ ⊑ | <-> | ⊑ n | ⊢ ⊑ n | req | seq | bind | rs | ... | (n) |
    |   ⊑ |   |     |     |     |       |     |     |      |    |     |     |
    | ⊢ ⊑ |   |     |     |     |       |     |     |      |    |     |     |
    | <-> |   |     |     |     |       |     |     |      |    |     |     |
    | ... |   |     |     |     |       |     |     |      |    |     |     |
    | (m) |   |     |     |     |       |     |     |      |    |     |     |

    The definitions here are grouped by column.
    The naming convention is Proper_[col]_[row].

  *)

  #[global]
  Instance Proper_entails_entails : Proper
    (flip entails ====> entails ====> impl)
    entails.
  Proof.
    unfold flip, Proper, respectful, impl.
    unfold entails. intros. auto.
  Qed.

  Example rewrite :
    entails (ens_ \[1 = 1]) (ens_ \[2 = 2]) ->
    entails (ens_ \[1 = 1]) empty.
  Proof.
    intros H.
    rewrite H.
  Abort.

  #[global]
  Instance Proper_entails_bientails : Proper
    (bientails ====> bientails ====> iff)
    entails.
  Proof.
    unfold bientails, entails, Proper, respectful, impl.
    split; intros.
    { apply H0. apply H1. apply H. auto. }
    { apply H0. apply H1. apply H. auto. }
  Qed.

  #[global]
  Instance Proper_entails_gentails : forall n, Proper
    (flip (gentails n) ====> (gentails n) ====> impl)
    entails.
  Proof.
    unfold Proper, respectful, impl, flip, entails.
    intros n. induction n; intros.
    (* this should not be provable *)
  Abort.

  #[global]
  Instance Proper_gentails_entails : forall n, Proper
    (flip entails ====> entails ====> impl)
    (gentails n).
  Proof.
    unfold Proper, respectful, impl, flip.
    intros n. induction n as [n IH] using lt_wf_ind.
    intros x y.
    destruct n as [| n'].
    { intros H_entails x0 y0 H_entails0 H_gentails.
      inverts H_gentails as H_gentails_norm H_gentails_shft.
      applys ge_base.
      - auto.
      - introv Hy.
        specializes H_entails Hy.
        specializes H_gentails_shft H_entails.
        destruct H_gentails_shft as (fb' & fk' & Hx).
        exists fb' fk'.
        auto. }
    { intros H_entails x0 y0 H_entails0 H_gentails.
      inverts H_gentails as H_gentails_mono H_gentails_succ.
      applys ge_shift.
      - intros m Hm.
        specialize (H_gentails_mono m Hm).
        rewrite* <- Nat.lt_succ_r in Hm.
      - introv Hy.
        specializes H_entails Hy.
        specializes H_gentails_succ H_entails.
        clear Hy H_entails.
        destruct H_gentails_succ as (fb' & fk' & Hx0 & H_fb' & H_fk').
        exists fb', fk'.
        splits*. }
  Qed.

  #[global]
  Instance Proper_gentails_gentails : forall n, Proper
    (flip (gentails n) ====> (gentails n) ====> impl)
    (gentails n).
  Proof.
    unfold Proper, respectful, impl, flip.
    intros n x y H_yx x0 y0 H_x0y0 H_xx0.
    transitivity x.
    { exact H_yx. }
    transitivity x0.
    { exact H_xx0. }
    { exact H_x0y0. }
  Qed.

  #[global]
  Instance Proper_gentails_under_bientails : forall n,
    Proper (bientails ====> bientails ====> iff) (gentails n).
  Proof.
    unfold Proper, respectful, impl.
    intros n x y H_xy x0 y0 H_x0y0.
    apply bientails_split in H_xy as [H_xy1 H_xy2].
    apply bientails_split in H_x0y0 as [H_x0y01 H_x0y02].
    splits; apply Proper_gentails_entails; auto.
  Qed.

  (** entails is proper wrt satisfies *)
  #[global]
  Instance Proper_satisfies_entails : Proper
    (eq ====> eq ====> eq ====> eq ====> eq ====> entails ====> impl)
    satisfies.
  Proof.
    unfold entails, Proper, respectful, impl.
    intros. subst.
    auto.
  Qed.

  #[global]
  Instance Proper_satisfies_bientails : Proper
    (eq ====> eq ====> eq ====> eq ====> eq ====> bientails ====> impl)
    satisfies.
  Proof.
    unfold bientails, entails, Proper, respectful, impl.
    intros. subst.
    apply H4.
    auto.
  Qed.

  (* A weaker Proper instance that only allows rewriting in the left
     side of a seq. Intuitively, we can no longer rely on the right side
     being weaker because it may change entirely, if we rewrite to a
     [shft] on the left which then consumes the right side into its
     continuation. *)
  #[global]
  Instance Proper_seq_entails_l : Proper (entails ====> eq ====> entails) seq.
  Proof.
    unfold Proper, entails, respectful.
    intros.
    subst.
    inverts H1 as H1; destr H1.
    { applys* s_bind. }
    { applys* s_bind_sh. }
  Qed.

  #[global]
  Instance Proper_seq_entails_fail : Proper (entails ====> entails ====> entails) seq.
  Proof.
    unfold Proper, entails, respectful.
    intros.
    inverts H1 as H1; destr H1.
    { apply* s_bind. }
    { apply H in H1.
      pose proof s_bind_sh.
      specializes H2 H1.
      applys_eq H2. clear H2.
      f_equal.
      (* the proof is stuck here because we want y0 and x0 to be related by
         something weaker than equality (entailment), but the relation
         between results in the semantics is equality *)
      admit.
      (* TODO what if we can assume shift-freedom to get rid of this case? *)
    }
  Abort.

  #[global]
  Instance Proper_seq_entails_sf f :
    ShiftFree f ->
    Proper (entails ====> entails) (@seq f).
  Proof.
    unfold Proper, respectful.
    unfold entails. intros.
    inverts H1. 2: { no_shift. }
    applys* s_seq.
  Qed.

  #[global]
  Instance Proper_seq_bientails_l : Proper (bientails ====> eq ====> bientails) seq.
  Proof.
    unfold Proper, bientails, respectful. intros.
    split; intros.

    { pose proof Proper_seq_entails_l.
      unfold Proper, entails, respectful in H2.
      applys H2 H1; auto.
      intros.
      apply~ H. }

    { pose proof Proper_seq_entails_l.
      unfold Proper, entails, respectful in H2.
      applys H2 H1; auto.
      intros.
      apply~ H. }
  Qed.

  #[global]
  Instance Proper_seq_sf : forall f1,
    (* shift_free f1 -> *)
    ShiftFree f1 ->
    Proper (entails ====> entails) (seq f1).
  Proof.
    unfold Proper, entails, respectful.
    intros.
    inverts H1 as H1; destr H1.
    { apply* s_seq. }
    { apply H in H1. false. }
  Qed.

  #[global]
  Instance Proper_seq_sf1 : forall f1,
    (* shift_free f1 -> *)
    ShiftFree f1 ->
    Proper (bientails ====> bientails) (seq f1).
  Proof.
    unfold Proper, bientails, respectful.
    intros.
    iff H1.
    { inverts H1 as H1. 2: { apply H in H1. false. }
      apply* s_seq.
      rewrite* <- H0. }
    { inverts H1 as H1. 2: { apply H in H1. false. }
      apply* s_seq.
      rewrite* H0. }
  Qed.

  #[global]
  Instance Proper_bind_entails_l : Proper (entails ====> eq ====> entails) bind.
  Proof.
    unfold Proper, entails, respectful. intros.
    inverts H1.
    { subst. applys* s_bind. }
    { specializes H H8.
      applys_eq s_bind_sh.
      2: { applys H. }
      congruence. }
  Qed.

  #[global]
  Instance Proper_bind_bientails_left : Proper (bientails ====> eq ====> bientails) bind.
  Proof.
    unfold Proper, bientails, respectful.
    intros.
    split; intros.

    { pose proof Proper_bind_entails_l.
      unfold Proper, entails, respectful in H2.
      applys H2 H1; auto.
      intros.
      apply~ H. }

    { pose proof Proper_bind_entails_l.
      unfold Proper, entails, respectful in H2.
      applys H2 H1; auto.
      intros.
      apply~ H. }
  Qed.

  (* Definition cont_entails fk1 fk2 := forall v, entails (fk1 v) (fk2 v).

  #[global]
  Instance Proper_bind_sf : forall f1,
    ShiftFree f1 ->
    Proper (cont_entails ====> entails) (bind f1).
  Proof.
    unfold Proper, cont_entails, entails, respectful.
    intros.
    inverts H1 as H1; destr H1.
    { apply* s_bind. }
    { apply H in H1. false. }
  Qed.

  #[global]
  Instance Proper_bind_sf2 : forall f1,
    ShiftFree f1 ->
    Proper ((fun fk2 fk3 =>
        forall v env, entails_under env (fk2 v) (fk3 v)) ====>
      (fun f2 f3 => forall env, entails_under env f2 f3)) (bind f1).
  Proof.
    unfold Proper, entails_under, entails, respectful.
    intros.
    inverts H1. 2: { apply H in H8. false. }
    applys* s_bind.
  Qed. *)

  Example rewrite :
    entails (ens_ \[1 = 1]) (ens_ \[2 = 2]) ->
    entails
      (bind (ens_ \[1 = 1]) (fun v => empty))
      empty.
  Proof.
    intros H.
    rewrite H.
  Abort.

  #[global]
  Instance Proper_bind_bientails_r f1 :
    Proper (Morphisms.pointwise_relation val eq ====> bientails)
      (@bind f1).
  Proof.
    unfold Proper, respectful, Morphisms.pointwise_relation, bientails. intros.
    iff H0.
    { inverts H0.
      { applys* s_bind. rewrite* H in H9. }
      { applys_eq s_bind_sh. 2: { eassumption. }
        f_equal.
        applys fun_ext_dep.
        eauto. } }
    { inverts H0.
      { applys* s_bind. rewrite* H. }
      { applys_eq s_bind_sh. 2: { eassumption. }
        f_equal.
        applys fun_ext_dep.
        eauto. } }
  Qed.

  #[global]
  Instance Proper_bind_entails_under_r f1 :
    Proper (Morphisms.pointwise_relation val eq ====> entails)
      (@bind f1).
  Proof.
    unfold Proper, respectful, Morphisms.pointwise_relation, entails.
    intros.
    inverts H0.
    { applys* s_bind. rewrite* H in H9. }
    { applys_eq s_bind_sh. 2: { eassumption. }
      f_equal.
      applys fun_ext_dep.
      eauto. }
  Qed.

  #[global]
  Instance Proper_bind_entails_sf f1 :
    ShiftFree f1 ->
    Proper (Morphisms.pointwise_relation val entails ====> entails)
      (@bind f1).
  Proof.
    unfold Proper, respectful, Morphisms.pointwise_relation, entails.
    intros * Hsf **.
    inverts H0.
    2: { destruct Hsf as (Hsf). false Hsf H7. }
    applys* s_bind.
  Qed.

  Example rewrite :
    entails (ens_ \[1 = 1]) (ens_ \[2 = 2]) ->
    entails
      (bind empty (fun v => ens_ \[1 = 1]))
      empty.
  Proof.
    intros H.
    setoid_rewrite H.
  Abort.

  #[global]
  Instance Proper_bind_gentails : forall n,
    Proper (gentails n ====> Morphisms.pointwise_relation val (gentails n) ====> (gentails n)) bind.
  Proof.
    unfold Proper, respectful, Morphisms.pointwise_relation.
    intros n.
    induction n as [n IH] using lt_wf_ind.
    intros x y H_entails x0 y0 H_entails0. (* necessary to 'descent' into the body of the continuation, which contains 'bind' *)
    destruct n as [| n'].
    { inverts H_entails as H_entails_norm H_entails_shft.
      applys ge_base.
      - introv Hx.
        inverts Hx as Hx Hx0.
        specializes H_entails_norm Hx.
        applys* s_bind.
        specializes H_entails0 v0.
        inverts H_entails0 as H_entails0.
        auto.
      - introv H_bind.
        inverts H_bind as.
        + introv Hx Hx0.
          specializes H_entails_norm Hx.
          specialize (H_entails0 v).
          inverts H_entails0 as _ H_entails0_shft.
          specializes H_entails0_shft Hx0.
          destruct H_entails0_shft as (fb' & fk' & Hy0).
          exists fb', fk'.
          applys s_bind; eauto.
        + introv Hx.
          specializes H_entails_shft Hx.
          destruct H_entails_shft as (fb' & fk' & Hy).
          exists fb' (fun v => bind (fk' v) y0).
          applys s_bind_sh.
          exact Hy. }
    { inverts H_entails as H_entails_mono H_entails_succ.
      applys ge_shift.
      - intros m Hm.
        specializes H_entails_mono Hm.
        assert (H_entails0_mono : forall a, gentails m (x0 a) (y0 a)).
        { intros a.
          specialize (H_entails0 a).
          inverts H_entails0 as H_entails0_mono _.
          applys* H_entails0_mono. }
        rewrite* <- Nat.lt_succ_r in Hm.
      - introv Hx.
        inverts Hx as.
        + introv Hx Hx0. (* shift on the right *)
          clear H_entails_succ. (* clear the hypothesis *)
          specialize (H_entails_mono O (Nat.le_0_l _)).
          inverts H_entails_mono as H_entails_mono.
          specialize (H_entails0 v).
          inverts H_entails0 as H_entails0_mono H_entails0_succ.
          clear H_entails0_mono.
          specializes H_entails0_succ Hx0.
          destruct H_entails0_succ as (fb' & fk' & Hy0 & H_fb' & H_fk').
          exists fb', fk'.
          splits; [| exact H_fb' | exact H_fk'].
          applys* s_bind.
        + introv Hx. (* shift on the left *)
          specializes H_entails_succ Hx.
          destruct H_entails_succ as (fb' & fk' & Hy & H_fb' & H_fk').
          exists fb' (fun v => bind (fk' v) y0).
          splits; [| exact H_fb' |].
          * applys* s_bind_sh.
          * intros v.
            assert (H_entails0_mono : forall a, gentails n' (x0 a) (y0 a)).
            { intros a.
              specialize (H_entails0 a).
              inverts H_entails0 as H_entails0_mono _.
              applys* H_entails0_mono. }
            specializes H_entails_mono (Nat.le_refl n').
            applys* IH. }
  Qed.

  #[global]
  Instance Proper_seq_gentails : forall n,
    Proper (gentails n ====> gentails n ====> gentails n) seq.
  Proof.
    lets: Proper_bind_gentails.
    unfold seq, Morphisms.pointwise_relation, Proper, respectful in *.
    intros.
    applys* H.
  Qed.

  #[global]
  Instance Proper_rs_gentails : forall n,
    Proper (gentails n ====> gentails n) rs.
  Proof.
    unfold Proper, respectful.
    intros n. induction n as [n IH] using lt_wf_ind.
    intros x y H_gentails.
    destruct n as [| n'].
    { inverts H_gentails as H_gentails_norm H_gentails_shft.
      applys* ge_base.
      - introv Hx.
        inverts Hx as.
        + introv Hx H_body.
          specializes H_gentails_shft Hx.
          destruct H_gentails_shft as (fb' & fk' & Hy).
          applys s_rs_sh.
          { exact Hy. }
          { admit. }
        + intros Hx.
          applys* s_rs_val.
      - introv Hx.
        inverts Hx as.
        introv Hx H_body.
        specializes H_gentails_shft Hx.
        destruct H_gentails_shft as (fb' & fk' & Hy).
        exists fb'. eexists.
        applys s_rs_sh.
        { exact Hy. }
        { admit. } (* same problem as the case above *) }
    { inverts H_gentails as H_gentails_mono H_gentails_succ.
      applys ge_shift.
      - intros m Hm.
        assert (H_gentails' := H_gentails_mono m Hm).
        rewrite <- Nat.lt_succ_r in Hm.
        exact (IH m Hm _ _ H_gentails').
      - introv Hx.
        inverts Hx as Hx H_body.
        specializes H_gentails_succ Hx.
        destruct H_gentails_succ as (fb' & fk' & Hy & H_fb & H_fk).
        exists fb, fk.
        splits*.
        + applys s_rs_sh.
          { exact Hy. }
          { admit. }
        + reflexivity.
        + reflexivity.
  Admitted.

  Example rewrite : forall n,
    gentails n (ens_ \[1 = 1]) (ens_ \[2 = 2]) ->
    gentails n
      (bind (ens_ \[1 = 1]) (fun _ => empty))
      empty.
  Proof.
    intros n H.
    (* TODO this should work for unfolding on the right of a bind, but currently doesn't *)
    (* Set Typeclasses Debug. *)
    rewrite H.
  Abort.

  Example rewrite : forall n,
    gentails n (ens_ \[1 = 1]) (ens_ \[2 = 2]) ->
    gentails n
      (bind empty (fun v => ens_ \[1 = 1]))
      empty.
  Proof.
    intros n H.
    (* Set Typeclasses Debug. *)
    setoid_rewrite H.
  Abort.

  Example refl_shift : forall n,
    gentails n (sh "k" (unk "k" (vint 1))) (sh "k" (unk "k" (vint 1))).
  Proof.
    intros n.
    reflexivity.
  Qed.

  #[global]
  Instance Proper_rs_entails : Proper (entails ====> entails) rs.
  Proof.
    unfold Proper, entails, respectful.
    intros. subst.
    inverts H0 as H0; destr H0.
    { applys* s_rs_sh. }
    { applys* s_rs_val. }
  Qed.

  #[global]
  Instance Proper_rs_bientails : Proper (bientails ====> bientails) rs.
  Proof.
    unfold bientails, Proper, respectful, impl.
    split; subst; intros.
    { inverts H0 as H0.
      { eapply s_rs_sh. apply H. exact H0. exact H7. }
      { apply H in H0. apply s_rs_val. assumption. } }
    { inverts H0 as H0.
      { eapply s_rs_sh. apply H. eauto. eauto. }
      { apply H in H0. apply s_rs_val. assumption. } }
  Qed.

  Example rewrite :
    bientails (rs (ens_ \[1 = 1])) (rs (ens_ \[2 = 2])) ->
    entails (rs (bind (rs (ens_ \[1 = 1])) (fun v => empty))) empty.
  Proof.
    intros H.
    rewrite H.
  Abort.

  #[global]
  Instance Proper_req_entails : Proper (eq ====> entails ====> entails) req.
  Proof.
    unfold Proper, entails, respectful, flip.
    intros.
    constructor. intros.
    rewrite <- H in H2.
    inverts H1 as H5.
    specializes H5 H3 ___.
  Qed.

  #[global]
  Instance Proper_req_bientails : Proper (eq ====> bientails ====> bientails) req.
  Proof.
    unfold Proper, bientails, respectful.
    intros.
    split; intros H1.
    { constructor. intros hp hr H2 H3 H4.
      rewrite <- H in H2.
      inverts H1 as H5.
      specializes H5 H3 ___.
      apply H0. assumption. }
    { constructor. intros hp hr H2 H3 H4.
      rewrite H in H2.
      inverts H1 as H5.
      specializes H5 H3 ___.
      apply H0. assumption. }
  Qed.

End Propriety.
