
From IxFree Require Import Nat Lib.
From CtxEquivIxFree Require Import lang.

(** top level Proper instances (using ctx_equiv/ctx_approx) *)

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

(** congruence Proper instances (using E_rel_o) *)

(* TODO: move to lang_ext.v or whatever *)
Definition E_rel_o_closed n Γ e1 e2 :=
  closed Γ e1 →
  closed Γ e2 →
  n ⊨ E_rel_o Γ e1 e2.

Definition elambda x e := ret (vlambda x e).

#[global]
Instance Proper_E_rel_o_app n Γ :
  Proper
    (E_rel_o_closed n Γ ==>
     E_rel_o_closed n Γ ==>
     E_rel_o_closed n Γ) app.
Proof.
  unfold Proper, E_rel_o_closed, respectful.
  intros e1 e1' He1.
  intros e2 e2' He2.
  intros Hc1 Hc2.
  rewrite closed_app in Hc1.
  rewrite closed_app in Hc2.
  destruct Hc1 as (?&?).
  destruct Hc2 as (?&?).
  specialize (He1 H H1).
  specialize (He2 H0 H2).
  by apply compat_app.
Qed.

Instance Proper_E_rel_o_lambda n Γ x :
  Proper
    (E_rel_o_closed n (Γ ∪ {[x]}) ==>
     E_rel_o_closed n Γ) (elambda x).
Proof.
  unfold Proper, E_rel_o_closed, respectful, elambda.
  intros e1 e2 He Hc1 Hc2.
  ospecialize (He _ _).
  { by rewrite closed_lambda in Hc1. }
  { by rewrite closed_lambda in Hc2. }
  apply compat_val.
  by apply compat_lambda.
Qed.
