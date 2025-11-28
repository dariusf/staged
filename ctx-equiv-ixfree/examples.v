(*
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
       But 0 ⊭ L_rel x z.

       Also note that 0 ⊨ L_rel y x and 0 ⊨ L_rel z y.
       Thus 0 ⊨ O_rel x y and 0 ⊨ O_rel y z.
       But 0 ⊭ L_rel x z, hence 0 ⊭ O_rel x z.
     *)
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

Lemma to_val_eq_Some e v :
  to_val e = Some v →
  e = ret v.
Proof. destruct e; simpl; congruence. Qed.


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
      eapply (IHn' e1').
      * eapply I_prop_intro in Hstep.
        iapply HeS in Hstep.
        eapply I_later_elim in Hstep.
        { apply L_rel_unroll. exact Hstep. }
        { unfold "⊏↓". simpl. lia. }
      * exact Hm.
      * exact He1'.
Qed.


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
  specialize (Hxy n).
  irevert x Hxy. loeb_induction IH.
  iintros x Hxy.
  isplit.
  + idestruct Hxy as Hxy _. idestruct Hxy.
    iintro. intros v ->.
    specialize (Hxy v eq_refl).
    apply terminates_impl_nterminates in Hxy as (n' & Hy).
    exact (L_rel_nterminates {| nw_index := n' |} _ _ (Hyz _) n' (Nat.le_refl _) Hy).
  + iintros x' Hc.
    idestruct Hxy as _ Hxy.
    ispec Hxy x' Hc.
    later_shift.
    apply L_rel_unroll in Hxy.
    apply L_rel_roll.
    ispec IH x' Hxy.
    exact IH.
Qed.

Definition o_rel e1 e2 := ∀ n, n ⊨ O_rel e1 e2.

Lemma o_rel_alt e1 e2 :
  o_rel e1 e2 ↔
  l_rel e1 e2 ∧ l_rel e2 e1.
Proof.
  unfold o_rel, l_rel, O_rel.
  split.
  { intros He. split.
    - intros n. exact (I_conj_elim1 _ _ (He n)).
    - intros n. exact (I_conj_elim2 _ _ (He n)). }
  { intros [He1 He2] n. isplit; auto. }
Qed.

Instance Transitive_o_rel : Transitive o_rel.
Proof.
  unfold Transitive.
  intros x y z Hxy Hyz.
  apply o_rel_alt in Hxy as [Hxy1 Hxy2].
  apply o_rel_alt in Hyz as [Hyz1 Hyz2].
  apply o_rel_alt. split.
  - etransitivity; eauto.
  - etransitivity; eauto.
Qed.

(*
Instance Transitive_e_rel : Transitive e_rel.
Proof.
  unfold Transitive, e_rel.
  intros x y z Hxy Hyz n.
  apply E_rel_intro.
  iintros E1 E2 HE.
Abort.
*)

Definition ciu_equiv Γ e1 e2 :=
  ∀ E γ,
    ectx_is_closed ∅ E →
    subst_is_closed Γ ∅ γ →
    obs_equiv (plug E (subst_map γ e1)) (plug E (subst_map γ e2)).

Fixpoint rctx_to_ctx (R : rctx) : ctx :=
  match R with
  | rctx_hole => ctx_hole
  | rctx_app1 R' e => ctx_app1 (rctx_to_ctx R') e
  | rctx_app2 v R' => ctx_app2 v (rctx_to_ctx R')
  end.

Definition ectx_to_ctx (E : ectx) : ctx :=
  rctx_to_ctx (ectx_to_rctx E).

Lemma rctx_to_ctx_correct R e :
  rplug R e = cplug (rctx_to_ctx R) e.
Proof.
  induction R.
  - simpl. reflexivity.
  - simpl. rewrite -> IHR. reflexivity.
  - simpl. rewrite -> IHR. reflexivity.
Qed.

Lemma rctx_to_ectx_correct R e :
  rplug R e = plug (rctx_to_ectx R) e.
Proof.
  unfold rctx_to_ectx.
  rewrite -> ectx_comp_rctx1_correct.
  simpl. reflexivity.
Qed.

Lemma ectx_to_ctx_correct E e :
  plug E e = cplug (ectx_to_ctx E) e.
Proof.
  unfold ectx_to_ctx.
  rewrite <- (ectx_rctx_bijection1 E) at 1.
  rewrite <- rctx_to_ectx_correct. simpl.
  rewrite -> rctx_to_ctx_correct.
  reflexivity.
Qed.

(*
Lemma ciu_equiv_completeness Γ e1 e2 :
  closed Γ e1 →
  closed Γ e2 →
  ctx_equiv Γ e1 e2 →
  ciu_equiv Γ e1 e2.
Proof.
  revert e1 e2.
  induction Γ as [Γ IH] using (induction_ltof1 _ size).
  intros e1 e2 Hce1 Hce2 Hequiv.
  destruct (size Γ) as [| n'] eqn:Hsize.
  - unfold ctx_equiv, ciu_equiv in *.
    intros E γ HE [-> _].
    setoid_rewrite -> size_dom in Hsize.
    rewrite -> map_size_empty_iff in Hsize. subst.
    setoid_rewrite -> dom_empty_L in Hce1.
    setoid_rewrite -> dom_empty_L in Hce2.
    setoid_rewrite -> dom_empty_L in Hequiv.
    rewrite ->2 subst_map_empty.
    rewrite ->2 ectx_to_ctx_correct.
    apply Hequiv.
    unfold ectx_is_closed in HE.
    admit.
  - Search (size _ = S _).
Admitted.
*)

Instance Transitive_ciu_equiv Γ : Transitive (ciu_equiv Γ).
Proof.
  unfold Transitive, ciu_equiv.
  intros x y z Hxy Hyz E HE γ Hγ.
  specialize (Hxy E HE γ Hγ).
  specialize (Hyz E HE γ Hγ).
  etransitivity; eassumption.
Qed.

Lemma O_rel_comp_obs_equiv e1 e2 e3 n :
  n ⊨ O_rel e1 e2 →
  obs_equiv e2 e3 →
  n ⊨ O_rel e1 e3.
Proof. Admitted.

Lemma E_rel_o_soundness' Γ e1 e2 :
  closed Γ e1 →
  closed Γ e2 →
  (∀ n, n ⊨ E_rel_o Γ e1 e2) →
  ciu_equiv Γ e1 e2.
Proof.
  unfold ciu_equiv.
  intros Hc1 Hc2 He E γ HE Hγ.
  apply O_rel_adequacy. intros n.
  specialize (He n).
  apply E_rel_o_elim in He.
  assert (HG : n ⊨ G_rel Γ γ γ).
  { apply fundamental_property_sub. exact Hγ. }
  ispec He γ γ HG.
  apply E_rel_elim in He.
  iapply He. admit.
  (* need n ⊨ K_rel E E, I'm not sure whether this holds for arbitrary E (not closed) *)
Admitted.

(* Observation: we prove the transitivity of E_rel_o by going through
   the transitivity of ciu_equiv, NOT of ctx_equiv *)
Lemma E_rel_o_completeness Γ e1 e2 n :
  closed Γ e1 →
  closed Γ e2 →
  ciu_equiv Γ e1 e2 →
  n ⊨ E_rel_o Γ e1 e2.
Proof.
  intros Hce1 Hce2 Hequiv.
  unfold ciu_equiv in Hequiv.
  apply E_rel_o_intro.
  iintros γ1 γ2 Hγ.
  apply E_rel_intro.
  iintros E1 E2 HE.
  apply (O_rel_comp_obs_equiv _ (fill E2 (subst_map γ2 e1))).
  { eapply E_rel_elimO; [| exact HE].
    iapply (E_rel_o_elim _ _ _ _ (fundamental_property_e Γ e1 n Hce1)).
    exact Hγ. }
  { apply Hequiv.
    admit.
    apply G_rel_elim in Hγ as (_ & Hγ2 & _).
    exact Hγ2. }
Admitted.

Definition E_rel_o_closed' Γ e1 e2 := ∀ n, E_rel_o_closed n Γ e1 e2.

#[global]
Instance Transitive_E_rel_o_closed Γ :
  Transitive (E_rel_o_closed' Γ).
Proof.
  unfold Transitive, E_rel_o_closed', E_rel_o_closed.
  intros [x Hcx] [y Hcy] [z Hcz] Hxy Hyz n. simpl in *.
  apply E_rel_o_completeness; auto.
  apply (E_rel_o_soundness' Γ x y Hcx Hcy) in Hxy.
  apply (E_rel_o_soundness' Γ y z Hcy Hcz) in Hyz.
  etransitivity; eassumption.
Qed.

(* #[global]
Instance Transitive_E_rel_o_closed n Γ : Transitive (E_rel_o_closed n Γ).
Proof.
  unfold Transitive, E_rel_o_closed. intros.
  apply fundamental_property_e.
  assumption.
Qed. *)

(*
#[global]
Instance Proper_E_rel_o_closed n Γ : Proper
  (flip (E_rel_o_closed n Γ) ==> E_rel_o_closed n Γ ==> impl)
  (E_rel_o_closed n Γ).
Proof.
  unfold flip, Proper, respectful, impl. intros.
  assert (E_rel_o_closed n Γ y x0). { transitivity x; assumption. }
  transitivity x0; assumption.
Qed.
*)

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
*)
