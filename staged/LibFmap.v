
From SLF Require Import LibCore.
From SLF Require Export LibSepFmap.

Module Fmap := LibSepFmap.

Lemma fmap_disjoint_indom : forall (A B: Type) (h1 h2 : fmap A B) x,
  disjoint h1 h2 -> indom h1 x -> not (indom h2 x).
Proof.
  unfold not; intros.
  apply (disjoint_inv_not_indom_both H H0).
  auto.
Qed.

Lemma fmap_indom_empty : forall A B (k:A),
  ~ indom (@empty A B) k.
Proof.
  intros.
  unfold not; intros.
  hnf in H.
  unfold empty in H.
  apply H.
  simpl.
  reflexivity.
Qed.

Lemma fmap_read_update : forall A B {IB:Inhab B} (k:A) (v:B) m,
  ~ indom m k ->
  read (update m k v) k = v.
Proof.
  intros.
  unfold update.
  rewrite read_union_l.
  apply read_single.
  apply indom_single.
Qed.

#[global]
Hint Rewrite fmap_read_update : rew_fmap rew_fmap_for_fmap_eq.

Ltac solve_trivial_not_indom :=
  match goal with
  | |- ~ Fmap.indom _ _ => unfold not; rewrite Fmap.indom_single_eq; intros; false
  end.

Ltac resolve_fn_in_env :=
  match goal with
  | |- Fmap.read (Fmap.update _ ?k (Some _)) ?k = _ =>
    rewrite fmap_read_update; [reflexivity | solve_trivial_not_indom]
  | |- Fmap.read (Fmap.update _ _ _) _ = _ =>
    unfold Fmap.update;
    first [
      rewrite Fmap.read_union_l; [resolve_fn_in_env | apply Fmap.indom_single] |
        rewrite Fmap.read_union_r; [resolve_fn_in_env | solve_trivial_not_indom]
    ]
  | |- Fmap.read (Fmap.single ?k (Some _)) ?k = _ =>
    rewrite Fmap.read_single; reflexivity
  (* | |- ?g => idtac "resolve_fn_in_env could not solve:"; idtac g *)
  end.
