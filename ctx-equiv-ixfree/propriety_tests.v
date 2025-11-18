
From stdpp Require Import strings.

Module ELambdaClosed.

Inductive expr :=
  (* this is collapsed; elambda also works here *)
  | vlambda (x : string) (e: expr)
  | var (x : string)
  | app (e1 e2: expr).

Definition closed (Γ:list string) (e:expr) := True.

(* not needed *)
(* Class Closed (Γ:list string) e : Prop :=
  { closed_pf: closed Γ e }. *)

Definition ctx_equiv (Γ:list string) (e1 e2 : expr) : Prop :=
  (* placeholder *)
  True.

#[global]
Instance Params_lambda : Params vlambda 1.
Proof. Qed.

Definition ctx_equiv_closed (Γ:list string) (e1 e2 : expr) : Prop :=
  closed Γ e1 ∧
  closed Γ e2 ∧
  ctx_equiv Γ e1 e2.

(* doesn't work *)
(* Hint Unfold ctx_equiv_closed. *)

#[global]
Instance Reflexive_ctx_equiv Γ : Reflexive (ctx_equiv Γ).
Proof.
  unfold Reflexive, ctx_equiv. done.
Qed.

#[global]
Instance Proper_ctx_approx_lambda Γ x : Proper
  (ctx_equiv (x::Γ) ==> ctx_equiv Γ)
  (vlambda x).
  (* (fun e => ret (vlambda x e)). *)
Proof.
  unfold flip, Proper, respectful. intros.
Admitted.

#[global]
Instance Proper_ctx_approx_lambda_closed Γ x : Proper
  (ctx_equiv_closed (x::Γ) ==> ctx_equiv Γ)
  (vlambda x).
  (* (fun e => ret (vlambda x e)). *)
Proof.
  unfold flip, Proper, respectful. intros.
  destruct H as (?&?&?).
Admitted.

Local Example ex_ctx_lambda x y :
  ctx_equiv [x]
    (app (vlambda y (var y)) (var x)) (var x) →
  ctx_equiv [] (vlambda x (var x))
    (vlambda x (app (vlambda y (var y)) (var x))).
Proof.
  intros.
  (* this works even though the scope is changing *)
  rewrite -> H.
  reflexivity.
Abort.

Local Example ex_ctx_lambda1 x y :
  ctx_equiv_closed [x]
    (app (vlambda y (var y)) (var x)) (var x) →
  ctx_equiv [] (vlambda x (var x))
    (vlambda x (app (vlambda y (var y)) (var x))).
Proof.
  intros.
  (* this requires closed to be proved upfront
    and put under a new definition *)
  rewrite -> H.
  reflexivity.
Abort.

End ELambdaClosed.