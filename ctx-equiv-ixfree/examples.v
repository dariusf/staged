
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

#[global]
Instance Reflexive_E_rel_o_closed n Γ : Reflexive (E_rel_o_closed n Γ).
Proof.
  unfold Reflexive, E_rel_o_closed. intros.
  apply fundamental_property_e.
  apply cexpr_closed.
Qed.

(* #[global]
Instance Transitive_L_rel n Γ : Transitive (L_rel).
Proof. *)

(* n ⊨ L_rel e1 e2
n ⊨ L_rel (fill E2 (subst_map γ2 y)) (fill E1 (subst_map γ1 x))
n ⊨ O_rel  (fill E2 (subst_map γ2 z))
n ⊨ L_rel e2 (fill E2 (subst_map γ2 z)) *)

(* #[global]
Instance Transitive_L_rel n Γ : Transitive (n ⊨ L_rel ).
Proof. *)

Goal ∀ n P, (n ⊨ ▷ (P)ᵢ) → P.
Proof.
  intros n P H_later.
  (* if n = 0, then H_later holds trivially, but P may not hold *)
  (* if n > 0, then H_later holds at (n = S n'), by the semantics of ▷, P holds at n'. Because P is pure,
     P holds *)
  (* so, the problem comes from the case, where n = 0! *)
Abort.

Lemma L_rel_trans n :
  n ⊨ ∀ᵢ x y z, L_rel x y →ᵢ
  (* n ⊨ *)
  L_rel y z →ᵢ
  (* n ⊨ *)
  L_rel x z.
Proof.
  (* loeb_induction. *)

  (* intros. *)
  loeb_induction.
  iintros x y z Hxy Hyz.

  unfold L_rel, L_rel_pre in Hxy, Hyz |- *.
  (* if n = 0, then:
     - if x is val, then y eventually terminates; otherwise we cannot say anything
     - if y is val, then z eventually terminates; otherwise we cannot say anything

     Now, we are given that x is val, and we need to show that z eventually terminates.
     From x is val, we know that y eventually terminates. However, if y terminates in
     more than 0 steps, we cannot say anything (z may loop). Therefore, this does not hold.

     -> Counter-example:
     let x = λx.x (is val)
     let y = (λx.x)(λx.x) (terminates after 1 step)
     let z = (λx.xx)(λx.xx) (omega, loops)

     we observe that 0 ⊨ L_rel x y
     we also observe that 0 ⊨ L_rel y z
     but 0 ⊭ L_rel x z
   *)
  (* unfold L_rel, L_rel_pre. *)
  isplit.
  {
    iintro.
    intros v1 ->.
    idestruct Hxy.
    idestruct Hyz.
    ispec H v1.
    specialize (H eq_refl).

    destruct H as (v2&?).
    unfold bigstep in H.
    destruct H as (e2&Hrtc&Hr).
    (* destruct Hrtc. *)
    (* Print rtc. *)
    inversion Hrtc; subst.
    admit.
    Search (▷ _).
    eapply I_prop_intro in H.
    ispec H2 y0.
    iapply H2 in H. clear H2.
    Search (▷ _).
    assert (n ⊨ ▷ (terminates z)ᵢ).
    { later_shift.
      iintro.
      assert (n ⊨ L_rel z z) by admit.
      apply L_rel_unroll in H.
      ispec IH y0. ispec IH z. ispec IH z. ispec IH H. ispec IH H4.
    admit.
  }
  {
    iintros e1 Hc.
    (* idestruct Hc. *)

    idestruct Hxy.
    (* idestruct H2. *)
    ispec H0 e1 Hc.
    later_shift.
    (* Unset Printing Notations. Set Printing Coercions. Set Printing Parentheses. *)

    ispec IH e1 y z.
    admit.
    (* iapply H2 in Hc. *)

(* I_arrow_elim *)
    (* Search "I_arrow". *)


    (* ispecialize H2 Hc. *)

    (* idestruct H1. *)

  }

  (* apply L_rel_unroll.
  apply L_rel_roll in H, H0.
  unfold L_rel_fix in *.
  unfold L_rel_pre in *.

  unfold L_rel in *. *)

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
  ispec H1 γ1 γ2 HG.
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
