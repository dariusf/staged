
From ShiftReset Require Export Logic.

Local Open Scope string_scope.

Example ex_rewrite_right1:
  entails_under (Fmap.update empty_env "k" (fun a => ens (fun r => \[a = r])))
   (ens_ \[True];; unk "k" (vint 1)) (ens_ \[True]).
Proof.
  (* funfold1 "k". *)
  pose proof (@entails_under_unk (Fmap.update empty_env "k" (fun a => ens (fun r => \[a = r]))) "k").
  specializes H (vint 1) ___.

  rewrite H.
  rew_fmap.

Abort.

Example ex_rewrite_right1:
  entails_under (Fmap.update empty_env "k" (fun a => ens (fun r => \[a = r])))
   (unk "k" (vint 1);; ens_ \[True]) (ens_ \[True]).
Proof.
  (* funfold1 "k". *)
  pose proof (@entails_under_unk (Fmap.update empty_env "k" (fun a => ens (fun r => \[a = r]))) "k").
  specializes H (vint 1) ___.

(* Set Typeclasses Debug. *)
  (* setoid_rewrite H. *)
  rewrite H.
  rew_fmap.

Abort.

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
