
From Stdlib Require Import Utf8.

Ltac specialise_one H H1 k :=
  match type of H with
  | forall (_ : ?t), _ =>
   first [ specialize (H H1); k |
      let n := fresh in
      evar (n : t);
      specialize (H n);
      specialise_one H H1 k;
      clear n
   ]
  end.

Tactic Notation "specialise" hyp(H) uconstr(t1) :=
  specialise_one H t1 idtac.

Tactic Notation "specialise" hyp(H) uconstr(t1) uconstr(t2) :=
  specialise_one H t1 ltac:(specialise H t2).

Tactic Notation "specialise" hyp(H) uconstr(t1) uconstr(t2) uconstr(t3) :=
  specialise_one H t1 ltac:(specialise H t2 t3).

Tactic Notation "specialise" hyp(H) uconstr(t1) uconstr(t2) uconstr(t3) uconstr(t4) :=
  specialise_one H t1 ltac:(specialise H t2 t3 t4).

Tactic Notation "specialise" hyp(H) uconstr(t1) uconstr(t2) uconstr(t3) uconstr(t4) uconstr(t5) :=
  specialise_one H t1 ltac:(specialise H t2 t3 t4 t5).

Tactic Notation "specialise" hyp(H) uconstr(t1) uconstr(t2) uconstr(t3) uconstr(t4) uconstr(t5)uconstr(t6) :=
  specialise_one H t1 ltac:(specialise H t2 t3 t4 t5 t6).

Tactic Notation "specialise" hyp(H) uconstr(t1) uconstr(t2) uconstr(t3) uconstr(t4) uconstr(t5)uconstr(t6) uconstr(t7):=
  specialise_one H t1 ltac:(specialise H t2 t3 t4 t5 t6 t7).

Example ex1_basics P Q R U T : U → T → R → P → (U → T → P → R → Q) → Q.
Proof.
  intros Hu Ht Hr Hp H.
  specialise H Hr.
  assumption.
  Unshelve.
  assumption.
  assumption.
  assumption.
Qed.

Example ex2_dependent A (y:A) P Q : P y → (∀ x, P x → Q) → Q.
Proof.
  intros Hp H.
  specialise H Hp.
Abort.

Tactic Notation "pose_proof" hyp(H) uconstr(t1) :=
  pose proof H; specialise H t1.

Tactic Notation "pose_proof" hyp(H) uconstr(t1) "as" uconstr(name) :=
  pose proof H as name; specialise H t1.

Tactic Notation "app" hyp(H) uconstr(t1) :=
  let H1 := fresh in
  pose_proof H t1 as H1; eapply H1; clear H1.

Example some_lemma b : b = true → b = true.
Proof. auto. Qed.

Example ex3_pose b : b = true → True.
Proof.
  Search andb.
  (* pose proof andb_true_intro as H0. *)
  intros H.
  pose proof some_lemma as H1.

  let n := fresh in
  evar (n : bool);
  specialize (H1 n);
  (* specialise_one H H1 k; *)

  specialize (H1 H).
  (* clear n. *)

  (* specialise H1 H. *)
  (* pose_proof andb_true_intro H. *)
  (* intros Hp H. *)
  (* specialise H Hp. *)
Abort.
