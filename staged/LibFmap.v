
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

Lemma not_indom_empty : forall A B (x:A),
  ~ Fmap.indom (@Fmap.empty A B) x.
Proof.
  unfold indom, map_indom, empty.
  intros.
  simpls.
  rew_logic.
  reflexivity.
Qed.

Lemma not_indom_union : forall A (B:Type) (s1 s2:fmap A B) (x:A),
  ~ Fmap.indom s1 x ->
  ~ Fmap.indom s2 x ->
  ~ Fmap.indom (s1 \+ s2) x.
Proof.
  unfold indom, map_indom, union, map_union.
  intros.
  simpls.
  rew_logic in *.
  destruct (Fmap.fmap_data s1 x); auto.
Qed.

Lemma not_indom_update : forall A (B:Type) (s1:fmap A B) (x x1:A) (v:B),
  ~ Fmap.indom s1 x ->
  x <> x1 ->
  ~ Fmap.indom (Fmap.update s1 x1 v) x.
Proof.
  unfold update.
  intros.
  apply not_indom_union.
  { unfold not. intros.
    unfold indom, single, map_indom in *.
    simpls *.
    case_if. }
  { assumption. }
Qed.

Ltac solve_not_indom :=
  rew_fmap; lazymatch goal with
  | |- ~ Fmap.indom (Fmap.update _ _ _) _ => unfold Fmap.update; solve_not_indom
  | |- ~ Fmap.indom (Fmap.single _ _ ) _ => unfold not; rewrite Fmap.indom_single_eq; intros; false
  | |- ~ Fmap.indom Fmap.empty _ => apply not_indom_empty
  end.

Ltac resolve_fn_in_env :=
  match goal with
  | |- Fmap.read (Fmap.update _ ?k _) ?k = _ =>
    rewrite fmap_read_update; [reflexivity | solve_not_indom]
  | |- Fmap.read (Fmap.update _ _ _) _ = _ =>
    unfold Fmap.update;
    first [
      rewrite Fmap.read_union_l; [resolve_fn_in_env | apply Fmap.indom_single] |
        rewrite Fmap.read_union_r; [resolve_fn_in_env | solve_not_indom]
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

Lemma remove_update : forall (A B:Type) h (x:A) (v:B),
  ~ indom h x ->
  remove (update h x v) x = h.
Proof using.
  unfold update.
  applys remove_union_single_l.
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

Lemma update_idem : forall A B {IB:Inhab B} s (x:A) (v:B),
  Fmap.indom s x ->
  Fmap.read s x = v ->
  Fmap.update s x v = s.
Proof.
  unfold update, indom, read, map_indom, single, union, map_union. intros.
  applys fmap_extens. intros y. simpls. case_if.
  { subst.
    destruct (Fmap.fmap_data s y).
    reflexivity.
    false. }
  { reflexivity. }
Qed.

Lemma disjoint_single_neq : forall A (B:Type) (x1 x2:A) (u1 u2:B),
  Fmap.disjoint (Fmap.single x1 u1) (Fmap.single x2 u2) ->
  x1 <> x2.
Proof.
  unfold disjoint, single, map_disjoint. intros. simpls.
  specializes H x1.
  destruct H; case_if.
  congruence.
Qed.

Lemma indom_update : forall A (B:Type) (s1:fmap A B) (x:A) (u:B),
  Fmap.indom (Fmap.update s1 x u) x.
Proof.
  intros.
  apply Fmap.indom_union_l.
  apply Fmap.indom_single.
Qed.

Lemma cancel_update_remove : forall A (B:Type) {IB:Inhab B} (s1:fmap A B) (x:A) (u:B),
  Fmap.indom s1 x ->
  Fmap.read s1 x = u ->
  Fmap.update (Fmap.remove s1 x) x u = s1.
Proof.
  unfold update, remove, single, read, indom, map_indom. intros.
  applys fmap_extens. intros y. simpls.
  unfold map_union, map_remove.
  case_if.
  { subst.
    destruct (Fmap.fmap_data s1 y).
    reflexivity.
    rew_logic *. }
  { case_if. reflexivity. }
Qed.

Lemma update_precedence: forall A (B:Type) (s:fmap A B) (x: A) (v v1:B),
  Fmap.update (Fmap.update s x v) x v1 = Fmap.update s x v1.
Proof.
  unfold Fmap.update, single, Fmap.union, Fmap.map_union. intros.
  applys fmap_extens. intros y. simpls.
  case_if; reflexivity.
Qed.

Lemma update_update_idem: forall A (B:Type) (s:fmap A B) x v,
  Fmap.update (Fmap.update s x v) x v = Fmap.update s x v.
Proof.
  intros.
  applys update_precedence v v.
Qed.

Lemma fmap_update_read : forall A B {IB:Inhab B} (k:A) (m:fmap A B),
  indom m k ->
  update m k (read m k) = m.
Proof.
  intros. unfold update.
  rewrite <- Fmap.update_eq_union_single.
  applys update_idem.
  assumption.
  reflexivity.
Qed.

Lemma update_inv : forall A B {IB:Inhab B} (k:A) (v:B) (m:fmap A B),
  update m k v = union (single k v) m.
Proof.
  intros. unfold update.
  reflexivity.
Qed.
