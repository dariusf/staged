From SLF Require Import LibCore.
From SLF Require Export LibSepFmap.

Module Fmap := LibSepFmap.

Lemma fmap_disjoint_indom_not_indom :
  forall (A B : Type)
         (h1 h2 : fmap A B)
         (x : A),
    disjoint h1 h2 -> indom h1 x -> ~ indom h2 x.
Proof.
  unfold not.
  exact disjoint_inv_not_indom_both.
Qed.

Lemma fmap_not_indom_empty :
  forall (A B : Type)
         (x : A),
    ~ indom (@empty A B) x.
Proof. auto. Qed.

Lemma fmap_neq_not_indom_single :
  forall (A B : Type)
         (x y : A)
         (v : B),
    x <> y ->
    ~ indom (single x v) y.
Proof.
  intros A B x y v H_neq H_indom.
  rewrite -> indom_single_eq in H_indom.
  contradiction.
Qed.

Lemma fmap_read_update :
  forall (A B : Type)
         {IB : Inhab B}
         (h : fmap A B)
         (x : A)
         (v : B),
    read (update h x v) x = v.
Proof.
  intros A B IB h x v.
  unfold update.
  rewrite -> (read_union_l h (indom_single x v)).
  exact (read_single x v).
Qed.

#[global] Hint Rewrite fmap_read_update : rew_fmap rew_fmap_for_fmap_eq.

Lemma fmap_neq_read_update :
  forall (A B : Type)
         {IB : Inhab B}
         (h : fmap A B)
         (x y : A)
         (v : B),
    x <> y ->
    read (update h x v) y = read h y.
Proof.
  intros A B IB h x y v H_neq.
  unfold update.
  rewrite -> read_union_r. reflexivity.
  auto using fmap_neq_not_indom_single.
Qed.

Lemma fmap_neq_read_remove :
  forall (A B : Type)
         {IB : Inhab B}
         (h : fmap A B)
         (x y : A),
    x <> y ->
    read (remove h x) y = read h y.
Proof.
  intros A B IB h x y H_neq.
  unfold read.
  unfold remove.
  unfold map_remove. simpl.
  destruct (classicT _).
  - congruence.
  - reflexivity.
Qed.

Lemma fmap_single_union_single_eq_single :
  forall (A B : Type)
         (x : A)
         (v w : B),
    single x v \+ single x w = single x v.
Proof.
  intros A B x v w.
  apply fmap_extens.
  intro y. simpl.
  unfold map_union.
  destruct (classicT _); reflexivity.
Qed.

Lemma fmap_update_update_eq_update :
  forall (A B : Type)
         (h : fmap A B)
         (x : A)
         (v w : B),
    update (update h x v) x w = update h x w.
Proof.
  intros.
  unfold update.
  rewrite <- union_assoc.
  rewrite -> fmap_single_union_single_eq_single.
  reflexivity.
Qed.

Ltac solve_trivial_not_indom :=
  match goal with
  | |- ~ Fmap.indom _ _ => unfold not; rewrite Fmap.indom_single_eq; intros; false
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
