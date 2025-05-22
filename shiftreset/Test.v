
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

Example ex_gentails_non_shift_free:
  gentails 1%nat
    ((sh "k" empty;; empty);; empty)
    (sh "k" empty;; empty;; empty).
Proof.
  intros.
  applys ge_shift.
  intros.
  inverts H. { inverts H7. false_invert H6. }
  inverts H5. { false_invert H7. }
  inverts H4.
  exists empty.
  exs.
  splits.
  - applys s_bind_sh.
    applys s_sh.
  - reflexivity.
  - intros.
    rewrite norm_bind_assoc_sf; shiftfree.
    reflexivity.
Qed.