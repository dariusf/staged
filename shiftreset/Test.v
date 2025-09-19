
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

Example ex_gentails_val_0 :
  gentails 0%nat
    (ens (fun r => \[r = 1+1]))
    (ens (fun r => \[r = 2])).
Proof.
  applys ge_base. intros.
  inverts H.
  applys s_ens.
  heaps.
Qed.

Example ex_gentails_val_1 :
  gentails 1%nat
    (ens (fun r => \[r = 1+1]))
    (ens (fun r => \[r = 2])).
Proof.
  applys ge_shift. intros.
  - applys_eq ex_gentails_val_0. lia.
    (* this is proved the regular way, and follows from monotonicity *)
  - intros.
    inverts H.
    destr H6. discriminate H.
    (* vacuously true *)
Qed.

Example ex_gentails_shift_0_vacuous :
  gentails 0%nat
    (sh "k" empty;; ens (fun r => \[r = 1]))
    (sh "k" empty;; ens (fun r => \[r = 2])).
Proof.
  applys ge_base.
  intros.
  inverts H.
  inverts H7.
Qed.

(* confirm that this is not vacuous *)
Example ex_gentails_shift_1 :
  gentails 1%nat
    (sh "k" empty;; ens (fun r => \[r = 1]))
    (sh "k" empty;; ens (fun r => \[r = 2])).
Proof.
  applys ge_shift; intros.
  - applys_eq ex_gentails_shift_0_vacuous. lia.
    (* monotonicity holds vacuously *)
  - inverts H. { inverts H7. }
    inverts H5.
    exs. splits.
    { applys* s_bind_sh. applys* s_sh. }
    { reflexivity. }
    { intros.
      applys ge_base.
      intros.
      (* we still need to relate the continuations *)
      admit.
    }
Abort.