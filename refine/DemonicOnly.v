
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Lia.

Set Implicit Arguments.

(* demonic nondet only *)
Definition wp (A : Type) : Type := (A -> Prop) -> Prop.


Lemma sdemon_weaken :
 forall (A : Type) (s : wp A) (Q1 Q2 : A -> Prop),
 s Q1 -> (forall a : A, Q1 a -> Q2 a) -> s Q2.
Proof.
  intros.
  (* Q <-> (fun _ => True) *)
  (* intros A s Q1 Q2 H; case (DScorrect s Q1); case (DScorrect s Q2);
   intuition eauto.
Qed. *)

Definition entails (A : Type) (s1 s2 : wp A) :=
  forall Q : A -> Prop, (s2 Q -> s1 Q).

(* preorder *)
Instance entails_refl : forall A, Reflexive (@entails A).
Proof.
  unfold Reflexive, entails. intros. auto.
Qed.
Instance entails_trans : forall A, Transitive (@entails A).
Proof.
  unfold Transitive, entails. intros. auto.
Qed.


Definition val (A : Type) (a:A) : wp A
 := fun Q => Q a.

Definition bind (A B : Type) (s1:wp A) (s2:(A -> wp B)) : wp B
 := fun Q => s1 (fun a => (s2 a) Q).

Definition seq (A B : Type) (s1:wp A) (s2:wp B) : wp B
 := bind s1 (fun (_:A) => s2).

(* Infix ";;" := seq (at level 38, right associativity). *)

Notation "c1 ;; c2" := (bind c1 (fun _ => c2)) (at level 100, right associativity).

(* https://www.cs.cornell.edu/courses/cs6115/2017fa/notes/Monads.html *)
Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
                             (right associativity, at level 84, c1 at next level).

Definition require (p:Prop) : wp unit := fun Q => p /\ Q tt.

Definition ensure (p:Prop) : wp unit := fun Q => p -> Q tt.

Definition any (A : Type) : wp A := fun Q => forall a : A, Q a.

Definition abort (A : Type) : wp A := fun Q => False.

Definition magic (A : Type) : wp A := fun Q => True.

Definition or (A:Type) (s1 s2:(wp A)) : wp A := fun Q => s1 Q /\ s2 Q.


Lemma ex1: forall x,
  entails (require (x >= 1)) (require (x > 1)).
Proof.
  intros.
  unfold entails, require. intros.
  destruct H.
  split. lia.
  assumption.
Qed.

Lemma ex2: forall x,
  entails (require (x = 1))
    (bind (val 1) (fun y => require (x + 1 = 2))).
Proof.
  intros.
  unfold entails, require. intros.
  unfold bind, val in H. destruct H.
  split. lia.
  assumption.
Qed.

Definition f x := (ensure (x = x + 1)).

Lemma ex3: forall x,
  x >= 0 ->
  entails (f x)
    (ensure (x >= 1)).
Proof.
  intros.
  unfold entails, ensure, f, ensure.
  intros.
  lia.
Qed.

Lemma wp_extens: forall (A:Type) (f:wp A) (p1 p2:A->Prop),
  (forall v, p1 v -> p2 v) ->
  f p1 -> f p2.
Proof.
  intros. revert H0.
  (* Search (?f _ -> ?f _). *)
  unfold entails. unfold seq, bind. intros.
(* Qed. *)
Admitted.

Lemma seq_cancel: forall (f:wp unit) (p1 p2:wp unit),
  entails p1 p2 ->
  entails (f;; p1) (f;; p2).
Proof.
  unfold entails. unfold seq, bind. intros. revert H0.
  apply wp_extens.
  intros.
  auto.
Qed.

Lemma bind_cancel: forall (A:Type) (f:wp A) (p1 p2:A -> wp unit),
  (forall x, entails (p1 x) (p2 x)) ->
  entails (x <- f;; p1 x) (x <- f;; p2 x).
Proof.
  unfold entails. unfold seq, bind. intros. revert H0.
  (* apply wp_extens.
  intros. *)
  (* auto. *)
(* Qed. *)
Abort.

Lemma seq_cancel1: forall (f:wp unit) (p1 p2:wp unit),
  entails (f;; p1) (f;; p2) ->
  entails p1 p2.
Proof.
  unfold entails. unfold seq, bind. intros.
  specialize (H Q).
  (* apply wp_extens.
  intros.
  auto. *)
(* Qed. *)
Abort.

Lemma ex4: forall (f:nat -> wp unit) x,
  entails (f x;; ensure (x = 0))
    (f x;; ensure (x > 0)).
Proof.
  unfold entails. intros.
  unfold seq, bind in H.
  unfold seq, bind.

  (* reflexivity. *)
(* Qed. *)
Abort.

(*
  ens results,
  biab,
  state and separation logic,
  rewriting under entail,
  free monad/alg eff,
  shift reset
*)
