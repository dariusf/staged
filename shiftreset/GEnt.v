
From ShiftReset Require Import Basics Norm ShiftFree.

(* sadly this has to be proven from scratch *)
Lemma gent_seq_defun_idem : forall n s x uf f1 f2,
  Fmap.indom s x ->
  Fmap.read s x = uf ->
  gentails_under s n f1 f2 ->
  gentails_under s n (defun x uf;; f1) f2.
Proof.
  intros.
  inverts H1.
  { apply geu_base. intros.
    inverts H1.
    inverts H10.
    lets: update_idem H H0.
    rewrite H1 in H11.
    jauto. }
  { apply geu_shift. intros.
    inverts H1. 2: { no_shift. }
    inverts H10.
    rewrites (>> update_idem H H0) in H11.
    specializes H2 H11.
    assumption. }
Qed.
