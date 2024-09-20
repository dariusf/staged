
(* From SLF Require Export LibSepFmap. *)
From SLF Require Export LibCore LibSepFmap.
(* From SLF Require Export LibSepFmap. *)
Module Fmap := LibSepFmap.

(* extra things to add to SLF's formalization *)

Lemma fmap_indom_empty : forall A B (k:A),
  ~ Fmap.indom (@Fmap.empty A B) k.
Proof.
  intros.
  unfold not; intros.
  hnf in H.
  unfold Fmap.empty in H.
  apply H.
  simpl.
  reflexivity.
Qed.

Lemma fmap_read_update : forall A B {IB:Inhab B} (k:A) (v:B) m,
  ~ Fmap.indom m k ->
  Fmap.read (Fmap.update m k v) k = v.
Proof.
  intros.
  unfold Fmap.update.
  rewrite Fmap.read_union_l.
  apply Fmap.read_single.
  apply Fmap.indom_single.
Qed.

#[global]
Hint Rewrite fmap_read_update : rew_fmap rew_fmap_for_fmap_eq.