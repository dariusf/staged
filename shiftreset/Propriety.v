
From Coq Require Import Classes.RelationClasses.
From Coq Require Morphisms Program.Basics.

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
    unfold entails, Proper, respectful, impl. intros. auto.
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
    unfold Proper, respectful, impl, flip.
    intros n. induction n; intros.
    (* this should not be provable *)
  Abort.

  #[global]
  Instance Proper_entails_under_bientails : forall env,
    Proper (bientails ====> bientails ====> iff)
      (entails_under env).
  Proof.
    unfold Proper, respectful, entails_under, bientails, impl.
    intros.
    split; intros.
    { apply H0. apply H1. apply H. assumption. }
    { apply H0. apply H1. apply H. assumption. }
  Qed.

  #[global]
  Instance Proper_entails_under_entails : forall env,
    Proper (flip entails ====> entails ====> impl)
      (entails_under env).
  Proof.
    unfold Proper, respectful, entails_under, entails, flip, impl.
    intros.
    eauto.
  Qed.

  (* For rewriting in the goal. Some of the flipped instances are for this purpose.
     Without them, we can only rewrite in the Coq or the staged context. *)
  #[global]
  Instance Proper_entails_under_entails_flip : forall env,
    Proper (entails ====> flip entails ====> flip impl)
      (entails_under env).
  Proof.
    unfold Proper, respectful, entails_under, entails, flip, impl.
    intros.
    eauto.
  Qed.

  #[global]
  Instance Proper_entails_under_entails_under : forall env, Proper
    (flip (entails_under env) ====> entails_under env ====> impl)
      (entails_under env).
  Proof.
    unfold entails_under, Proper, respectful, impl, flip.
    intros.
    auto.
  Qed.

  #[global]
  Instance Proper_entails_under_flip : forall env, Proper
    (entails_under env ====> flip (entails_under env) ====> flip impl)
      (entails_under env).
  Proof.
    unfold entails_under, Proper, respectful, impl, flip.
    intros.
    auto.
  Qed.

  #[global]
  Instance Proper_gentails_entails : forall n, Proper
    (flip entails ====> entails ====> impl)
    (gentails n).
  Proof.
    unfold entails, Proper, respectful, impl, flip.
    intros n. induction n; intros.
    { inverts H1.
      applys* ge_base. }
    { inverts H1.
      applys ge_shift. intros.
      specializes H H1.
      specializes H3 H.
      jauto. }
  Qed.

  #[global]
  Instance Proper_gentails_gentails : forall n, Proper
    (flip (gentails n) ====> (gentails n) ====> impl)
    (gentails n).
  Proof.
    unfold Proper, respectful, impl, flip.
    intros n. induction n; intros.
    { inverts H. inverts H1. inverts H0.
      applys* ge_base. }
    { applys ge_shift. intros.
      inverts H as H. specializes H H2. destr H.
      inverts H1 as H1. specializes H1 H3. destr H1.
      inverts H0 as H0. specializes H0 H4. destr H0.
      jauto. }
  Qed.

  #[global]
  Instance Proper_gentails_under_bientails : forall n env,
    Proper (bientails ====> bientails ====> iff)
      (gentails_under env n).
  Proof.
    unfold Proper, respectful, entails_under, bientails, impl.
    intros n. destruct n; intros.
    { iff H1.
      { inverts H1. applys geu_base. intros.
        applys H0. applys H2. applys* H. }
      { inverts H1. applys geu_base. intros.
        applys H0. applys H2. applys* H. } }
    { iff H1.
      { inverts H1. applys geu_shift. intros.
        lets H2: H.
        specializes H2 h1 h2 (shft k fb fk) env s2.
        destruct H2.
        specializes H3 H1.
        specializes H4 H3.
        zap.
        applys* H0. }
      { inverts H1. applys geu_shift. intros.
        lets H2: H.
        specializes H2 h1 h2 (shft k fb fk) env s2.
        destruct H2.
        specializes H2 H1.
        specializes H4 H2.
        zap.
        applys* H0. } }
  Qed.

  #[global]
  Instance Proper_gentails_under_entails : forall n env,
    Proper (flip entails ====> entails ====> impl)
      (gentails_under env n).
  Proof.
    unfold Proper, respectful, entails_under, entails, flip, impl.
    intros n. destruct n; intros.
    { inverts H1.
      applys geu_base. intros.
      applys H0.
      applys H2.
      applys* H. }
    { inverts H1.
      applys geu_shift. intros.
      specializes H H1.
      specializes H4 H.
      jauto. }
  Qed.

  #[global]
  Instance Proper_gentails_under_entails_under : forall n env,
    Proper (flip (entails_under env) ====> (entails_under env) ====> impl)
      (gentails_under env n).
  Proof.
    unfold Proper, respectful, entails_under, entails, flip, impl.
    intros n. destruct n; intros.
    { inverts H1.
      applys geu_base. intros.
      applys H0.
      applys H2.
      applys* H. }
    { inverts H1.
      applys geu_shift. intros.
      specializes H H1.
      specializes H4 H.
      jauto. }
  Qed.

  (* Definition res_weaker R1 R2 :=
    match R1, R2 with
    | norm v1, norm v2 => v1 = v2
    | shft k1 fb1 fk1, shft k2 fb2 fk2 =>
      k1 = k2 /\
      entails fb1 fb2 /\
      (forall v, entails (fk1 v) (fk2 v))
    | _, _ => False
    end.

  #[global]
  Instance Proper_satisfies_entails_weaker : Proper
    (eq ====> eq ====> eq ====> eq ====> res_weaker ====> entails ====> impl)
    satisfies.
  Proof.
    unfold entails, Proper, respectful, impl, res_weaker.
    intros. subst.
    destruct x3; destruct y3; subst.
    - auto.
    - false.
    - false.
    - destr H3.
      specializes H4 H5.
  Abort. *)

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

  #[global]
  Instance Proper_satisfies_entails_under : forall env, Proper
    (eq ====> eq ====> eq ====> eq ====> entails_under env ====> impl)
    (satisfies env).
  Proof.
    unfold entails_under, Proper, respectful, impl.
    intros. subst.
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
    unfold Proper, entails, respectful. intros.
    inverts H1. 2: { no_shift. }
    applys* s_seq.
  Qed.

  (* see [Proper_bind_entails_under_sf] *)
  #[global]
  Instance Proper_seq_entails_under_sf f1 : forall env,
    ShiftFree f1 ->
    Proper (entails_under env ====> (entails_under env))
      (@seq f1).
  Proof.
    unfold Proper, respectful, entails_under.
    intros * Hsf **.
    inverts* H0.
    applys* s_seq.
    (* cannot use H *)
  Abort.

  #[global]
  Instance Proper_seq_entails_under_l : forall env,
    Proper (entails_under env ====> eq ====> entails_under env) seq.
  Proof.
    unfold Proper, entails_under, respectful. intros.
    subst.
    inverts H1 as H1; destr H1.
    { applys* s_bind. }
    { eapply s_bind_sh. jauto. }
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

  (* this is essentially the same as entails *)
  #[global]
  Instance Proper_seq_sf2 :
  (* forall env f1, *)
  forall f1,
    ShiftFree f1 ->
    (* Proper (entails_under env ====> entails_under env) (seq f1). *)
    Proper ((fun f2 f3 => forall env, entails_under env f2 f3) ====> (fun f2 f3 => forall env, entails_under env f2 f3)) (seq f1).
  Proof.
  (* Check respectful. *)
    unfold Proper, entails_under, respectful.
    (* unfold Proper, entails_under. *)
    intros.
    inverts H1 as H1. 2: { apply H in H1. false. }
    applys s_seq.
    eassumption.

    (* apply* s_seq. *)
    applys_eq H0.
    assumption.

    (* admit.
    applys_eq H9.
    admit. *)
    (* applys_eq H0. *)
    (* admit. *)

    (* apply* H0.  *)
  Qed.

  Definition env_constant f :=
    (* forall s h1 h2 R, satisfies s s h1 h2 R f. *)
    forall s1 s2 h1 h2 R, satisfies s1 s2 h1 h2 R f -> s1 = s2.

  Lemma env_constant_ens : forall Q,
    env_constant (ens Q).
  Proof.
    unfold env_constant. intros.
    inverts H as H. destr H.
    reflexivity.
  Qed.

  Lemma env_constant_seq : forall f1 f2,
    shift_free f1 ->
    env_constant f1 ->
    env_constant f2 ->
    env_constant (f1;; f2).
  Proof.
    unfold env_constant. intros.
    inverts H2 as H2. 2: { apply H in H2. false. }
    specializes H0 H2.
    specializes H1 H10.
    congruence.
  Qed.

  Class EnvConstant f : Prop :=
    { env_constant_pf :
      forall s1 s2 h1 h2 R, satisfies s1 s2 h1 h2 R f -> s1 = s2 }.

  #[global]
  Instance EnvConstantEns : forall Q,
    EnvConstant (ens Q).
  Proof.
    intros. constructor.
    apply env_constant_ens.
  Qed.

  #[global]
  Instance EnvConstantSeq : forall f1 f2,
    ShiftFree f1 ->
    EnvConstant f1 ->
    EnvConstant f2 ->
    EnvConstant (f1;; f2).
  Proof.
    constructor. apply env_constant_seq.
    destruct* H.
    destruct* H0.
    destruct* H1.
  Qed.

  #[global]
  Instance Proper_seq_sf3 : forall env f1,
    ShiftFree f1 ->
    EnvConstant f1 ->
    Proper (entails_under env ====> entails_under env) (seq f1).
  Proof.
    unfold Proper, entails_under, respectful.
    intros.
    inverts H2 as H2. 2: { apply H in H2. false. }
    destruct H0 as [H0]. specializes H0 H2. subst.
    apply* s_seq.
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
  Instance Proper_bind_entails_under_l : forall env,
    Proper (entails_under env ====> eq ====> entails_under env) bind.
  Proof.
    unfold Proper, entails_under, respectful. intros.
    inverts H1.
    { applys* s_bind.
      rewrite* <- H0. }
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

  #[global]
  Instance Proper_bind_entails_entails_under_sf f1 : forall env,
    ShiftFree f1 ->
    Proper (Morphisms.pointwise_relation val entails ====> (entails_under env))
      (@bind f1).
  Proof.
    unfold Proper, respectful, Morphisms.pointwise_relation, entails_under.
    intros * Hsf **.
    inverts H0.
    2: { destruct Hsf as (Hsf). false Hsf H7. }
    applys* s_bind.
    unfold entails in H.
    eauto.
  Qed.

  #[global]
  Instance Proper_bind_entails_under_sf f1 : forall env,
    ShiftFree f1 ->
    Proper (Morphisms.pointwise_relation val (entails_under env) ====> (entails_under env))
      (@bind f1).
  Proof.
    unfold Proper, respectful, Morphisms.pointwise_relation, entails_under.
    intros * Hsf **.
    inverts H0.
    2: { destruct Hsf as (Hsf). false Hsf H7. }
    applys* s_bind.
    (* cannot use H *)
  Abort.

  Example rewrite :
    entails_under empty_env (ens_ \[1 = 1]) (ens_ \[2 = 2]) ->
    entails_under empty_env
      (bind empty (fun v => ens_ \[1 = 1]))
      empty.
  Proof.
    intros H.
    (* TODO this should work for unfolding on the right of a bind, but currently doesn't *)
    (* Set Typeclasses Debug. *)
    Fail setoid_rewrite H.
  Abort.

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
    intros n. induction n; intros.
    { inverts H.
      applys ge_base. intros.
      inverts H as H2 H3.
      specializes H1 H2.
      applys* s_bind.
      specializes H0 v0.
      inverts H0 as H.
      applys H H3. }
    {
      (* already we see the capacities are wrong, as we don't have shifts in both sides *)
      applys ge_shift. intros.
      inverts H1.
      {
        (* the shift is on the right *)
        specializes H0 v.
        inverts H0 as H0.
        specializes H0 H10.
        zap.
        applys* s_bind.
        (* x is norm, but we only have x gentails_(S n) y *)
        (* inverts H. *)
        (* seemingly cannot be proven without allowing the
          operational semantics of bind to distribute the index? *)
        admit.
      }
      {
        (* the shift is on the left *)
        inverts H as H.
        specializes H H7.
        zap.
        { applys* s_bind_sh. }
        {
          intros.
          applys* IHn.
          intros a.
          specializes H0 a.
          (* we need x0 gentails y0 at n, but have it at S n *)
          inverts H0.
          admit.
        }
      }
    }
  Abort.

  (* this statement also isn't easy to use *)
  #[global]
  Instance Proper_bind_gentails : forall n n1 n2,
    n = (n1 + n2)%nat ->
    Proper (gentails n1 ====> Morphisms.pointwise_relation val (gentails n2) ====> (gentails n)) bind.
  Proof.
    unfold Proper, respectful, Morphisms.pointwise_relation.
    intros n. induction n; intros.
    { symmetry in H. apply Nat.eq_add_0 in H. destr H. subst.
      applys ge_base. intros.
      inverts H as H2 H3.
      inverts H0.
      specializes H1 v0. inverts H1.
      applys* s_bind. }
    {
      (* already we see the capacities are wrong, as we don't have shifts in both sides *)
      applys ge_shift. intros.
      inverts H2.
      {
        (* the shift is on the right *)
        specializes H1 v.
        (* n1 must be 0 *)
        inverts H0.
        2: {
          (* we can't dismiss this case *)
          admit.
        }
        rewrite Nat.add_0_l in H. subst n2.
        inverts H1 as H1.
        specializes H1 H11.
        zap.
        applys* s_bind.
      }
      {
        (* the shift is on the left *)
        (* n1 must be nonzero *)
        inverts H0.
        {
          (* can't dismiss this case *)
          admit.
        }
        specializes H2 H8.
        zap.
        applys* s_bind_sh.
        Fail applys H2.
        admit.
        intros.
        applys IHn.
        admit.
        admit.
        admit.
      }
    }
  Abort.

  Definition gentails1 f1 f2 :=
    forall n, gentails n f1 f2.

  #[global]
  Instance Proper_bind_gentails :
    Proper (gentails1 ====> Morphisms.pointwise_relation val (gentails1) ====> (gentails1)) bind.
  Proof.
    unfold Proper, respectful, Morphisms.pointwise_relation, gentails1.
    intros. induction n; intros.
    { applys ge_base. intros.
      inverts H1.
      specializes H O. inverts H. specializes H1 H9.
      specializes H0 v0 O. inverts H0. specializes H H10.
      applys* s_bind. }
    {
      (* the IH doesn't let us progress *)
      admit.
    }
  Abort.

  #[global]
  Instance Proper_bind_gentails_l : forall n,
    Proper (gentails n ====> eq ====> gentails n) bind.
  Proof.
    unfold Proper, respectful.
    intros n. induction n; intros.
    { applys ge_base. intros.
      inverts H1.
      inverts H. specializes H1 H9.
      subst.
      applys* s_bind. }
    {
      (* H is wrong already. x may not necc have shift. *)
      applys ge_shift. intros.
      inverts H1.
      {
        (* x returns norm but we have x <= y at S n.
          this points to needing to quantify over the first use of n. *)
        inverts H.
        admit.
      }
      { inverts H.
        specializes H2 H7.
        zap.
        applys* s_bind_sh.
        intros. simpl.
        applys* IHn. }
    }
  Abort.

  #[global]
  Instance Proper_bind_gentails_l : forall n,
    Proper (gentails1 ====> eq ====> gentails n) bind.
  Proof.
    unfold Proper, respectful, gentails1.
    intros n. induction n; intros.
    { applys ge_base. intros.
      inverts H1.
      specializes H O. inverts H. specializes H1 H9.
      subst.
      applys* s_bind. }
    {
      applys ge_shift. intros.
      inverts H1.
      {
        specializes H O. inverts H. specializes H1 H9.
        subst.
        exists fb fk.
        splits.
        applys* s_bind.
        reflexivity.
        intros. reflexivity.
      }
      {
        subst.
        specializes H (S n). inverts H. specializes H1 H7.
        zap.
        applys* s_bind_sh.
        intros. simpl.
        applys* IHn.
        intros. specializes H2 v.
        Fail assumption.
        applys_eq H2.
        (* IH is too strong *)
        admit.
      }
    }
  Abort.

  #[global]
  Instance Proper_bind_gentails_l :
    Proper (gentails1 ====> eq ====> gentails1) bind.
  Proof.
    unfold Proper, respectful, gentails1.
    intros. induction n; intros.
    { applys ge_base. intros.
      inverts H1.
      specializes H O. inverts H. specializes H1 H9.
      subst.
      applys* s_bind. }
    {
      applys ge_shift. intros.
      inverts H1.
      {
        specializes H O. inverts H. specializes H1 H9.
        subst.
        exists fb fk.
        splits.
        applys* s_bind.
        reflexivity.
        intros. reflexivity.
      }
      {
        subst.
        specializes H (S n). inverts H. specializes H1 H7.
        zap.
        applys* s_bind_sh.
        intros. simpl.
        (* IH is too strong, Proper fixes x and y already *)
        admit.
      }
    }
  Abort.

  #[global]
  Instance Proper_bind_gentails_r_sf : forall n f,
    ShiftFree f ->
    Proper (Morphisms.pointwise_relation val (gentails n) ====> (gentails n)) (bind f).
  Proof.
    unfold Proper, respectful, Morphisms.pointwise_relation.
    intros n. induction n; intros.
    { applys ge_base. intros.
      inverts H1.
      specializes H0 v0. inverts H0. specializes H1 H10.
      applys* s_bind. }
    { applys ge_shift. intros.
      (* there are two ways in which a bind can produce a shift *)
      inverts H1.
      {
        (* shift on the right *)
        specializes H0 v.
        inverts H0.
        specializes H2 H10.
        zap.
        applys* s_bind.
      }
      {
        destruct H.
        false shift_free_pf H7.
      }
    }
  Qed.

  #[global]
  Instance Proper_bind_gentails : forall n,
    Proper (gentails1 ====> Morphisms.pointwise_relation val (gentails1) ====> (gentails n)) bind.
  Proof.
    unfold Proper, respectful, Morphisms.pointwise_relation, gentails1.
    intros n. induction n; intros.
    { applys ge_base. intros.
      inverts H1.
      specializes H O. inverts H. specializes H1 H9.
      specializes H0 v0 O. inverts H0. specializes H H10.
      applys* s_bind. }
    {
      (* now we have a better IH *)
      applys ge_shift. intros.
      inverts H1.
      {
        (* shift on the right *)
        specializes H O. inverts H as H. specializes H H9.
        specializes H0 v (S n). inverts H0 as H0. specializes H0 H10.
        zap.
        applys* s_bind.
      }
      {
        (* shift on the left *)
        specializes H (S n). inverts H as H. specializes H H7.
        (* specializes H0 v (S n). inverts H0 as H0. specializes H0 H10. *)
        zap.
        applys* s_bind_sh.
        intros.
        applys IHn.
        (* we have this for n only, not all n... *)
        admit.
        intros. auto.
      }
    }
  Abort.

  #[global]
  Instance Proper_bind_gentails_l : forall n f,
    Proper (Morphisms.pointwise_relation val (gentails n) ====> (gentails n)) (@bind f).
  Proof.
    unfold Proper, respectful, Morphisms.pointwise_relation.
    intros n. induction n; intros.
    { applys ge_base. intros.
      inverts H0.
      specializes H v0.
      inverts H as H2 H3.
      applys* s_bind. }
    { applys ge_shift. intros.
      inverts H0.
      { (* the shift comes from the right side *)
        specializes H v.
        inverts H as H.
        specializes H H9.
        zap.
        applys* s_bind. }
      { (* the shift comes from the left *)
        exists fb. exs. splits.
        { applys* s_bind_sh. }
        { reflexivity. }
        { intros.
          applys* IHn.
          intros.
          specializes H a.
          (* we are stuck. we need to know that x and y (the right sides,
            after the continuations) are related after one shift, but
            we instead have that they are related before *)
          admit.
        }
      }
    }
  Abort.
  (* Admitted. *)

  (* #[global]
  Instance Proper_bind_gentails : forall n,
    (* 3 = 1 + 2 -> *)
    Proper (gentails n ====> Morphisms.pointwise_relation val (gentails n) ====> (gentails n)) bind.
  Proof.
  Admitted. *)

  (* #[global]
  Instance Proper_bind_gentails_l : forall n,
    Proper (gentails n ====> eq ====> (gentails n)) bind.
  Proof.
  Admitted.

  #[global]
  Instance Proper_bind_gentails_r : forall n f,
    Proper (Morphisms.pointwise_relation val (gentails n) ====> (gentails n)) (@bind f).
  Proof.
  Admitted. *)

  Example rewrite : forall n,
    gentails n (ens_ \[1 = 1]) (ens_ \[2 = 2]) ->
    gentails n
      (bind (ens_ \[1 = 1]) (fun _ => empty))
      empty.
  Proof.
    intros n H.
    (* TODO this should work for unfolding on the right of a bind, but currently doesn't *)
    (* Set Typeclasses Debug. *)
    Fail rewrite H.
  Abort.

  Example rewrite : forall n,
    gentails n (ens_ \[1 = 1]) (ens_ \[2 = 2]) ->
    gentails n
      (bind empty (fun v => ens_ \[1 = 1]))
      empty.
  Proof.
    intros n H.
    (* Set Typeclasses Debug. *)
    (* Fail setoid_rewrite H. *)
  Abort.

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
  Instance Proper_rs_entails_under : forall s,
    Proper (entails_under s ====> entails_under s) rs.
  Proof.
    unfold Proper, entails_under, respectful.
    intros. subst.
    inverts H0 as H0; destr H0.
    { eapply s_rs_sh.
      apply H. eauto. eauto. }
    { apply s_rs_val. eauto. }
  Qed.

  #[global]
  Instance Proper_fex_entails_under (A : Type) : forall env,
    Proper (Morphisms.pointwise_relation A (entails_under env) ====> entails_under env) (@fex A).
  Proof.
    unfold Proper, respectful, Morphisms.pointwise_relation, entails_under.
    intros.
    inverts H0 as H0. destr H0.
    constructor.
    exists b.
    apply H.
    assumption.
  Qed.

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
  Instance Proper_req_entails_under : forall env,
    Proper (eq ====> entails_under env ====> entails_under env) req.
  Proof.
    unfold Proper, entails_under, respectful, flip.
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

  Example rewrite : forall l,
    entails_under empty_env (ens_ \[1 = 1]) (ens_ \[2 = 2]) ->
    entails_under empty_env
      (rs (bind (req (l~~>vint 1) (ens_ (l~~>vint 1);; ens_ \[1 = 1]))
        (fun _ => empty))) empty.
  Proof.
    intros.
    rewrite H.
  Abort.

End Propriety.
