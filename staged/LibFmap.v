
From SLF Require Import LibCore.
From SLF Require Export LibSepFmap.

Module Fmap := LibSepFmap.

Lemma fmap_disjoint_indom : forall (A B: Type) (h1 h2 : fmap A B) x,
  disjoint h1 h2 -> indom h1 x -> ~ indom h2 x.
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

Lemma fmap_not_indom_of_neq : forall (A B:Type) (a b:A) (v:B),
  a <> b -> ~ Fmap.indom (Fmap.single a v) b.
Proof.
  intros.
  unfold not. intros.
  rewrite (Fmap.indom_single_eq a b v) in H0.
  contradiction.
Qed.

Ltac solve_trivial_not_indom :=
  rew_fmap; lazymatch goal with
  | |- ~ Fmap.indom (Fmap.update _ _ _) _ => unfold Fmap.update; solve_trivial_not_indom
  | |- ~ Fmap.indom (Fmap.single _ _ ) _ => unfold not; rewrite Fmap.indom_single_eq; intros; false
  end.

Ltac resolve_fn_in_env :=
  match goal with
  | |- Fmap.read (Fmap.update _ ?k _) ?k = _ =>
    rewrite fmap_read_update; [reflexivity | solve_trivial_not_indom]
  | |- Fmap.read (Fmap.update _ _ _) _ = _ =>
    unfold Fmap.update;
    first [
      rewrite Fmap.read_union_l; [resolve_fn_in_env | apply Fmap.indom_single] |
        rewrite Fmap.read_union_r; [resolve_fn_in_env | solve_trivial_not_indom]
    ]
  | |- Fmap.read (Fmap.single ?k _) ?k = _ =>
    rewrite Fmap.read_single; reflexivity
  (* | |- ?g => idtac "resolve_fn_in_env could not solve:"; idtac g *)
  end.


Lemma remove_union_single_l : forall (A B:Type) h (x:A) (v:B),
  ~ indom h x ->
  remove (union (single x v) h) x = h.
Proof using.
  introv M. applys fmap_extens. intros y.
  unfold remove, map_remove, union, map_union, single. simpls. case_if.
  { destruct h as [f F]. unfolds indom, map_indom. simpls. subst. rew_logic~ in M. }
  { case_if~. }
Qed.

Lemma remove_not_indom : forall (A B:Type) (h:Fmap.fmap A B) (x:A),
  ~ Fmap.indom h x ->
  Fmap.remove h x = h.
Proof.
  intros.
  applys fmap_extens. intros y.
  unfold remove, map_remove. simpls. case_if.
  { unfolds indom, map_indom. rew_logic in H. subst~. }
  { auto. }
Qed.

Lemma update_noop : forall A B {IB:Inhab B} s (x:A) (v:B),
  Fmap.indom s x ->
  Fmap.read s x = v ->
  Fmap.update s x v = s.
Proof.
  unfold update, indom, read, map_indom, single, union, map_union. intros.
  applys fmap_extens. intros y. simpls. case_if.
  { subst.
    destruct (Fmap.fmap_data s y).
    reflexivity.
    exfalso. apply H. reflexivity. }
  { reflexivity. }
Qed.
