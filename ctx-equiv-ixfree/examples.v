
From CtxEquivIxFree Require Import lang.
From CtxEquivIxFree Require Import propriety.

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

Example ex_ctx_lambda x y :
  x <> y →
  ctx_equiv ∅ (vlambda x (var x))
    (vlambda y (app (vlambda x (var x)) (var y))).
Proof.
  intros.
Abort.