
From Staged Require Export HeapF LibFmap ExtraTactics.

From ShiftReset Require Export
  Basics ShiftFree Propriety Reduction
  Satisfies Biab Norm Ent GEnt
  ReductionOld.

Implicit Types a v r : val.



(** * Reduction example *)
(**
  < (shift k. k i1) + (shift k1. k1 i2) >
  assuming left-to-right evaluation
  k1 takes i1, result is i1 + i2
  k2 takes i2, result is also i1 + i2
*)
(* Example e1_red : forall x1 x2 i1 i2 r3, exists f,
  entails_under empty_env
    (rs
      (sh x1 (unk x1 (vint i1));;
        sh x2 (unk x2 (vint i2));;
        ens (fun r => \[r = vint (i1 + i2)]))) f.
Proof.
  intros.
  eexists.

  rewrite red_init.
  rewrite red_acc.
  rewrite red_shift_elim.
  apply ent_seq_defun.

  (* TODO funfold1 *)
  rewrites (>> entails_under_unk x1); [ resolve_fn_in_env | ].
  simpl.

  rewrite norm_ens_eq.
  rewrite (norm_seq_pure_l (fun r0 => r0 = vint i1)).

  rewrite red_init.
  rewrite red_acc.
  rewrite red_shift_elim.
  rewrites (>> red_skip sf_defun).
  apply ent_seq_defun.

  rewrites (>> entails_under_unk x2); [ resolve_fn_in_env | ].
  simpl.

  rewrite norm_ens_eq.

  rewrite red_normal; shiftfree.
  rewrite red_normal; shiftfree.
  rewrite red_normal; shiftfree.

  rewrite (norm_seq_pure_l (fun r4 => r4 = vint i2)).
  apply entails_under_refl.
Qed. *)

Example ex_rewrite_right:
  (* entails (ens_ \[True]) (ens_ \[True];; ens_ \[True]). *)
  entails (ens_ \[True]) (ens_ \[True];; ens_ \[True];; ens_ \[True]).
Proof.
(* Set Typeclasses Debug. *)
  rewrite <- norm_ens_ens_void.
Abort.

(* Example ex_rewrite_right1:
  entails_under empty_env (ens_ \[True]) (ens_ \[True];; ens_ \[True];; ens_ \[True]).
Proof.
  assert (forall H1 H2, entails_under empty_env (ens_ H1;; ens_ H2) (ens_ (H1 \* H2))) as ?. admit.
  assert (forall H1 H2, entails_under empty_env (ens_ (H1 \* H2)) (ens_ H1;; ens_ H2)) as ?. admit.
  (* rewrite norm_ens_ens_void. *)
  (* Set Typeclasses Debug. *)
  (* rewrite H.
  rewrite H0.
  rewrite <- H. *)
  rewrite <- H0.
  rewrite <- H.

Abort. *)


(** * Correspondence with the paper *)
(** ** Differences *)
(** #<!-- this space is needed!!-->#
- Function pointer values [vfptr] enable arbitrary higher-order staged formulae. A [defun] staged formula (conceptually just an [ens] which binds a function value) and an output [senv] added to [satisfies] complete this, allowing shift bodies to return continuations.
- The semantics guarantees that [shft]/[Sh#] continuations are #<i>shift-free by construction</i>#, by having a [rs] as their topmost form. This significantly simplifies the proofs of the reduction rules. *)
(** ** Section 4.3. Shift/Reset Reduction *)
(** The reduction rules are proved as lemmas.
- #<a href="&num;red_skip">red_skip</a>#
- #<a href="&num;red_normal">red_normal</a>#
- #<a href="&num;red_init">red_init</a>#
- #<a href="&num;red_extend">red_extend</a>#
- #<a href="&num;red_acc">red_acc</a>#
- #<a href="&num;red_shift_elim">red_shift_elim</a># *)
