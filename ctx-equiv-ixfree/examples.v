
From CtxEquivIxFree Require Import lang.
From CtxEquivIxFree Require Import propriety.
From IxFree Require Import Lib Nat.
From CtxEquivIxFree Require Import ixfree_tactics.

(*
Example ex_rew x y :
  ctx_approx ∅ (vlambda x (var x)) (vlambda y (var y)) →
  ctx_approx ∅ (vlambda x (var x)) (vlambda y (var y)).
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Example ex_rew1 x y :
  ctx_equiv ∅ (vlambda x (var x)) (vlambda y (var y)) →
  ctx_approx ∅ (vlambda x (var x)) (vlambda y (var y)).
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.
*)

(*
#[global]
Instance Reflexive_E_rel_o_closed n Γ : Reflexive (E_rel_o_closed n Γ).
Proof.
  unfold Reflexive, E_rel_o_closed. intros.
  apply fundamental_property_e.
  apply cexpr_closed.
Qed.
*)

Goal ∀ n P, (n ⊨ ▷ (P)ᵢ) → P.
Proof.
  intros n P H_later.
  (* if n = 0, then H_later holds trivially, but P may not hold *)
  (* if n > 0, then H_later holds at (n = S n'), by the semantics of ▷, P holds at n'. Because P is pure,
     P holds *)
  (* so, the problem comes from the case, where n = 0! *)
Abort.

Lemma L_rel_trans n :
  n ⊨ ∀ᵢ x y z,
    L_rel x y →ᵢ
    L_rel y z →ᵢ
    L_rel x z.
Proof.
  loeb_induction.
  iintros x y z Hxy Hyz.
  unfold L_rel, L_rel_pre.
  isplit.
  { unfold L_rel, L_rel_pre in Hxy, Hyz.
    (* If n = 0, then:
       - If x is val, then y eventually terminates; otherwise we cannot say anything.
       - If y is val, then z eventually terminates; otherwise we cannot say anything.

       Now, we are given that x is val, and we need to show that z eventually terminates.
       From x is val, we know that y eventually terminates. However, if y terminates in
       more than 0 steps, we cannot say anything (z may loop). Therefore, this does not
       hold.

       Counter-example:
       x = λx.x (is val)
       y = (λx.x)(λx.x) (terminates after 1 step)
       z = (λx.xx)(λx.xx) (omega, loops)

       We observe that 0 ⊨ L_rel x y.
       We also observe that 0 ⊨ L_rel y z.
       But 0 ⊭ L_rel x z. *)
    admit. }
  { iintros x' Hc.
    unfold L_rel, L_rel_pre in Hxy.
    idestruct Hxy as _ Hxy.
    ispec Hxy x' Hc.
    later_shift.
    apply L_rel_unroll in Hxy.
    apply L_rel_roll.
    ispec IH x' y z Hxy Hyz.
    exact IH. }
Abort. (* cannot be proven *)

Definition l_rel e1 e2 : Prop := ∀ n, n ⊨ L_rel e1 e2.

Definition nbigstep n e v := ∃ e', nsteps contextual_step n e e' ∧ to_val e' = Some v.
Definition nterminates n e := ∃ v, nbigstep n e v.

Lemma to_val_eq_Some e v :
  to_val e = Some v →
  e = ret v.
Proof. destruct e; simpl; congruence. Qed.

Lemma nterminates_zero e :
  nterminates O e →
  ∃ (v : val), e = v.
Proof.
  unfold nterminates, nbigstep.
  intros (v & e' & Hnsteps & Heq).
  inversion Hnsteps. subst.
  apply to_val_eq_Some in Heq.
  exists v. exact Heq.
Qed.


Lemma nterminates_succ e n :
  nterminates (S n) e →
  ∃ e', contextual_step e e' ∧ nterminates n e'.
Proof.
  unfold nterminates, nbigstep.
  intros (v & e' & Hnsteps & Heq).
  inversion Hnsteps. subst.
  exists y. split.
  - assumption.
  - exists v, e'. auto.
Qed.

Lemma L_rel_alt n e1 e2 :
  (n ⊨ L_rel e1 e2) ↔
  (forall m, m ≤ nw_index n → nterminates m e1 → terminates e2).
Proof.
  split.
  { revert e1.
    destruct n as [n]. simpl.
    induction n as [| n' IHn']; intros e1 He m Hm He1.
    - rewrite -> Nat.le_0_r in Hm.
      rewrite -> Hm in He1.
      apply nterminates_zero in He1 as (v & He1).
      idestruct He as HeO _. idestruct HeO.
      exact (HeO v He1).
    - destruct m as [| m'].
      + idestruct He as HeO _. idestruct HeO.
        apply nterminates_zero in He1 as (v & He1).
        exact (HeO v He1).
      + rewrite <- Nat.succ_le_mono in Hm.
        apply nterminates_succ in He1 as (e1' & Hstep & He1').
        idestruct He as _ HeS.
        eapply IHn'.
        * eapply I_prop_intro in Hstep.
          iapply HeS in Hstep.
          eapply I_later_elim in Hstep.
          { apply L_rel_unroll. exact Hstep. }
          { unfold "⊏↓". simpl. lia. }
        * exact Hm.
        * exact He1'. }
  { destruct n as [n]. simpl.
    induction n as [| n' IHn']; intros H_terminates.
    - isplit.
      + iintro.
        intros v ->.
        apply (H_terminates 0).
        * exact (Nat.le_0_l _).
        * unfold nterminates, nbigstep.
          exists v, v. split.
          { constructor. }
          { simpl. reflexivity. }
      + iintros e1' _.
        destruct w as [w]. simpl in *.
        replace w with 0 by lia.
        iapply I_later_zero.
        simpl. reflexivity.
    - isplit.
      + iintro.
        intros v ->.
        apply (H_terminates 0).
        * exact (Nat.le_0_l _).
        * unfold nterminates, nbigstep.
          exists v, v. split.
          { constructor. }
          { simpl. reflexivity. }
      + (* this direction seems ... difficult *)
Abort.

Lemma L_rel_nterminates n e1 e2 :
  (n ⊨ L_rel e1 e2) →
  forall m,
    m ≤ nw_index n →
    nterminates m e1 →
    terminates e2.
Proof.
  revert e1.
  destruct n as [n]. simpl.
  induction n as [| n' IHn']; intros e1 He m Hm He1.
  - rewrite -> Nat.le_0_r in Hm.
    rewrite -> Hm in He1.
    apply nterminates_zero in He1 as (v & He1).
    idestruct He as HeO _. idestruct HeO.
    exact (HeO v He1).
  - destruct m as [| m'].
    + idestruct He as HeO _. idestruct HeO.
      apply nterminates_zero in He1 as (v & He1).
      exact (HeO v He1).
    + rewrite <- Nat.succ_le_mono in Hm.
      apply nterminates_succ in He1 as (e1' & Hstep & He1').
      idestruct He as _ HeS.
      eapply IHn'.
      * eapply I_prop_intro in Hstep.
        iapply HeS in Hstep.
        eapply I_later_elim in Hstep.
        { apply L_rel_unroll. exact Hstep. }
        { unfold "⊏↓". simpl. lia. }
      * exact Hm.
      * exact He1'.
Qed.

Lemma terminates_impl_nterminates e :
  terminates e → ∃ n, nterminates n e.
Proof.
  unfold terminates, nterminates.
  unfold bigstep, nbigstep.
  intros (v & e' & Hrtc & Heq).
  induction Hrtc.
  - exists O, v, x.
    split.
    + constructor.
    + exact Heq.
  - specialize (IHHrtc Heq) as (n & v' & e' & Hnsteps & Heq').
    exists (S n), v', e'.
    split.
    + econstructor; eassumption.
    + exact Heq'.
Qed.

Instance Transitive_l_rel : Transitive l_rel.
Proof.
(*
  unfold Transitive, l_rel.
  intros x y z Hxy Hyz n.
  specialize (Hxy n).
  rewrite -> L_rel_alt in Hxy |- *.
  intros m Hlt Hx. specialize (Hxy m Hlt Hx).
  apply terminates_impl_nterminates in Hxy as (n' & Hy).
  specialize (Hyz {| nw_index := n' |}).
  rewrite -> L_rel_alt in Hyz. simpl in Hyz.
  exact (Hyz n' ltac:(auto) Hy).
*)

  unfold Transitive, l_rel.
  intros x y z Hxy Hyz n.
  unfold L_rel, L_rel_pre in Hxy.
  specialize (Hxy n). idestruct Hxy as Hxy Hxy'. idestruct Hxy.
  isplit.
  + iintro. intros v ->.
    specialize (Hxy v eq_refl).
    apply terminates_impl_nterminates in Hxy as (n' & Hy).
    exact (L_rel_nterminates {| nw_index := n' |} _ _ (Hyz _) n' (Nat.le_refl _) Hy).
  + admit. (* loeb_induction *)
Admitted.

Lemma O_rel_trans n :
  n ⊨ ∀ᵢ x y z, O_rel x y →ᵢ
  (* n ⊨ *)
  O_rel y z →ᵢ
  (* n ⊨ *)
  O_rel x z.
Proof.
Admitted.

Lemma E_rel_trans n x y z :
  n ⊨ E_rel x y →
  n ⊨ E_rel y z →
  n ⊨ E_rel x z.
Proof.
  intros Hxy Hyz.

  apply E_rel_intro.
  iintros E1 E2 HK.

  apply E_rel_elim in Hxy.
  apply E_rel_elim in Hyz.
Admitted.

#[global]
Instance Transitive_E_rel_o_closed n Γ :
  Transitive (E_rel_o_closed n Γ).
Proof.
  unfold Transitive, E_rel_o_closed. intros * H1 H2.
  apply E_rel_o_intro.
  iintros γ1 γ2 HG.

  apply E_rel_o_elim in H1.
  apply E_rel_o_elim in H2.
  ispec H1 γ1 γ1 ltac:(admit).
  ispec H2 γ1 γ2 HG.

Admitted.

(* #[global]
Instance Transitive_E_rel_o_closed n Γ : Transitive (E_rel_o_closed n Γ).
Proof.
  unfold Transitive, E_rel_o_closed. intros.
  apply fundamental_property_e.
  assumption.
Qed. *)

#[global]
Instance Proper_E_rel_o_closed n Γ : Proper
  (flip (E_rel_o_closed n Γ) ==> E_rel_o_closed n Γ ==> impl)
  (E_rel_o_closed n Γ).
Proof.
  unfold flip, Proper, respectful, impl. intros.
  assert (E_rel_o_closed n Γ y x0). { transitivity x; assumption. }
  transitivity x0; assumption.
Qed.

Program Definition cvar {Γ} (x: name) : cexpr (Γ ∪ {[x]}) :=
  mk_cexpr (Γ ∪ {[x]}) (var x) _.
Next Obligation.
  intros.
  rewrite closed_var.
  set_solver.
Qed.

Example ex_ctx_lambda1 n x y :
  E_rel_o_closed n (∅ ∪ {[x]})
    (capp (celambda y (cvar y)) (cvar x)) (cvar x) →
  E_rel_o_closed n ∅
    (celambda x (capp (celambda y (cvar y)) (cvar x)))
    (celambda x (cvar x)).
Proof.
  intros H.
  rewrite -> H.
  reflexivity.
Qed.

  (* apply Proper_E_rel_o_lambda.
  (* why does this work *)
  eassert (∅ ∪ {[x]} = {[x]}).
  { eapply union_empty_r. set_solver. }
  apply H. *)

Example ex_ctx_lambda x y :
  closed ∅ (vlambda x (var x)) →
  closed ∅ (vlambda x (app (vlambda y (var y)) (var x))) →
  ctx_equiv ∅
    (vlambda x (var x))
    (vlambda x (app (vlambda y (var y)) (var x))).
Proof.
  intros Hc1 Hc2.
  apply E_rel_o_soundness.
  { exact Hc1. }
  { exact Hc2. }
  intros n.
  apply compat_val.
  apply compat_lambda.
  { exact Hc1. }
  { exact Hc2. }
  apply E_rel_o_intro.
  iintros γ1 γ2 Hγ.
  apply G_rel_elim in Hγ as (Hγc1 & Hγc2 & Hγ').
  destruct Hγc1 as [Hdom1 Hγc1].
  destruct Hγc2 as [Hdom2 Hγc2].
  rewrite -> fold_unfold_subst_map_app.
  assert (Hc3 : closed ∅ (vlambda y (var y))).
  { unfold closed. simpl. rewrite bool_decide_spec. set_solver. }
  rewrite -> (subst_map_closed _ _ Hc3).
  assert (Hin1 : x ∈ dom γ1) by set_solver.
  rewrite -> Hdom1 in Hγc1.
  specialize (Hγc1 x Hin1).
  apply elem_of_dom in Hin1.
  unfold is_Some in Hin1.
  destruct Hin1 as [u1 Hu1].
  specialize (Hγc1 u1 Hu1).
  assert (Hin2 : x ∈ dom γ2) by set_solver.
  rewrite -> Hdom2 in Hγc2.
  specialize (Hγc2 x Hin2).
  apply elem_of_dom in Hin2.
  unfold is_Some in Hin2.
  destruct Hin2 as [u2 Hu2].
  specialize (Hγc2 u2 Hu2).
  rewrite -> fold_unfold_subst_map_var.
  rewrite -> fold_unfold_subst_map_var.
  setoid_rewrite -> Hu1.
  setoid_rewrite -> Hu2.
  apply E_rel_intro.
  iintros E1 E2 HE.
  apply (O_rel_red_r _ _ (fill E2 u2)).
  { econstructor.
    - reflexivity.
    - reflexivity.
    - econstructor. exact I. simpl. rewrite -> decide_True; auto. }
  iapply (K_rel_elim _ _ _ HE).
  iapply Hγ'.
  { iintro. eassumption. }
  { iintro. eassumption. }
Qed.

(*
Example ex_ctx_app e1 e2 e1' e2' :
  ctx_equiv ∅ e1 e1' →
  ctx_equiv ∅ e2 e2' →
  ctx_equiv ∅ (app e1 e2) (app e1' e2').
Proof.
  intros He1 He2.
  rewrite -> He1.
  rewrite -> He2.
  reflexivity.
Qed.
*)
