
From ShiftReset Require Export Logic.

Local Open Scope string_scope.

Example ex_gentails_non_shift_free :
  gentails 0%nat
    ((sh "k" empty;; ens (fun r => \[r = 1]));; empty)
    (sh "k" empty;; empty;; empty).
Proof.
  unfold ";;".
  rewrite gnorm_bind_assoc.
  applys ge_base.
  introv H_absurd.
  inverts H_absurd as H_absurd _.
  inverts H_absurd.
Qed.
