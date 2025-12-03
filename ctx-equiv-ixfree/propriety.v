(*
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

(** Dependent types seem more expressive than explicit hypotheses,
  as there are some statements where associating a property with
  an object seems different from putting it in front of or behind
  an implication. *)
Record cexpr (Γ:scope) := mk_cexpr {
  cexpr_car :> expr;
  cexpr_closed : closed Γ cexpr_car
}.

(** congruence Proper instances (using E_rel_o) *)

(* TODO: move to lang_ext.v or whatever *)
Definition E_rel_o_closed n Γ (e1 e2:cexpr Γ) :=
  (* closed Γ e1 → *)
  (* closed Γ e2 → *)
  n ⊨ E_rel_o Γ e1 e2.

Definition elambda x e := ret (vlambda x e).
Program Definition celambda {Γ} x (e:cexpr (Γ ∪ {[x]})) : cexpr Γ :=
  mk_cexpr {[x]} (ret (vlambda x e)) _.
Next Obligation.
  intros.
  rewrite closed_lambda.
  apply cexpr_closed.
Qed.

Program Definition capp {Γ} (e1 e2:cexpr Γ) : cexpr Γ :=
  mk_cexpr Γ (app (cexpr_car Γ e1) (cexpr_car Γ e2)) _.
Next Obligation.
  intros.
  apply closed_app.
  split; apply cexpr_closed.
Qed.

#[global]
Instance Proper_E_rel_o_app n Γ :
  Proper
    (E_rel_o_closed n Γ ==>
     E_rel_o_closed n Γ ==>
     E_rel_o_closed n Γ) capp.
Proof.
  unfold Proper, E_rel_o_closed, respectful.
  intros e1 e1' He1.
  intros e2 e2' He2.
  by apply compat_app.
Qed.

Instance Proper_E_rel_o_lambda n Γ x :
  Proper
    (E_rel_o_closed n (Γ ∪ {[x]}) ==>
     E_rel_o_closed n Γ) (celambda x).
Proof.
  unfold Proper, E_rel_o_closed, respectful.
  intros e1 e2 He.
  apply compat_val.
  apply compat_lambda.
  apply cexpr_closed.
  apply cexpr_closed.
  assumption.
Qed.
*)
