
From CtxEquivIxFree Require Import lang.

#[global]
Instance Proper_ctx_equiv Γ : Proper
  (ctx_equiv Γ ==> ctx_equiv Γ ==> impl)
  (ctx_equiv Γ).
Proof.
  unfold flip, Proper, respectful, impl. intros.
  assert (ctx_equiv Γ y x). { symmetry. assumption. }
  assert (ctx_equiv Γ y x0). { transitivity x; assumption. }
  transitivity x0; assumption.
Qed.

#[global]
Instance Proper_ctx_approx_equiv Γ : Proper
  (ctx_equiv Γ ==> ctx_equiv Γ ==> impl)
  (ctx_approx Γ).
Proof.
  unfold flip, Proper, respectful, impl. intros.
  assert (ctx_approx Γ y x0).
  { apply ctx_equiv_unfold in H. destruct H.
    transitivity x; assumption. }
  transitivity x0.
  assumption.
  apply ctx_equiv_unfold in H0. destruct H0. assumption.
Qed.

#[global]
Instance Proper_ctx_approx Γ : Proper
  (flip (ctx_approx Γ) ==> ctx_approx Γ ==> impl)
  (ctx_approx Γ).
Proof.
  unfold flip, Proper, respectful, impl. intros.
  assert (ctx_approx Γ y x0). { transitivity x; assumption. }
  transitivity x0; assumption.
Qed.

#[global]
Instance Proper_ctx_approx_app Γ : Proper
  (flip (ctx_approx Γ) ==> ctx_approx Γ ==> ctx_approx Γ)
  app.
Proof.
  unfold flip, Proper, respectful. intros.
(* Qed. *)
Abort.

#[global]
Instance Proper_ctx_approx_lambda Γ : Proper
  (eq ==> ctx_approx Γ ==> ctx_approx Γ)
  vlambda.
Proof.
  unfold flip, Proper, respectful. intros.
(* Qed. *)
Abort.