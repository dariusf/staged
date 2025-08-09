
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Lia.

Set Implicit Arguments.

Record W (A:Type): Type := pre_post { pre: Prop; post: A -> Prop }.

Definition refines (A:Type) (s1 s2:W A): Prop
:= pre s2 -> ( pre s1 /\ (forall a:A, post s1 a -> post s2 a) ).

Definition val (A:Type) (a:A): W A := pre_post True (fun b => a=b).

Definition bind (A B:Type) (s1:W A) (s2:A -> W B): (W B) :=
  pre_post (pre s1 /\ (forall a:A, post s1 a -> pre (s2 a)))
    (fun b => exists a:A, post s1 a /\ post (s2 a) b).

Definition seq (A B : Type) (s1:W A) (s2:W B) : W B
 := bind s1 (fun (_:A) => s2).

Notation "c1 ;; c2" := (bind c1 (fun _ => c2)) (at level 100, right associativity).

(* https://www.cs.cornell.edu/courses/cs6115/2017fa/notes/Monads.html *)
Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
                             (right associativity, at level 84, c1 at next level).

Definition any (A:Type): W A := pre_post True (fun a:A => True).

Definition sync (A B:Type) (s:A -> W B) : W B :=
  pre_post (exists a:A, pre (s a))
    (fun b => forall a:A, pre (s a) -> post (s a) b).

Definition require (p:Prop) : W unit := pre_post p (fun _ => True).

Definition ensure (p:Prop) : W unit := pre_post True (fun _ => p).

Notation entails := refines.

Example ex1: forall x,
  entails (require (x >= 1)) (require (x > 1)).
Proof.
  intros.
  unfold refines, require. intros.
  simpl in *.
  split. lia.
  auto.
Qed.

Example ex2: forall x,
  entails (require (x = 1))
    (bind (val 1) (fun y => require (x + 1 = 2))).
Proof.
  intros.
  unfold entails, require. simpl. intros (?&?).
  specialize (H0 1 ltac:(reflexivity)).
  split.
  lia.
  intros.
  exists 1.
  split.
  lia.
  constructor.
Qed.

Definition f x := (ensure (x = 1)).

Example ex3: forall x,
  x >= 0 ->
  entails (f x)
    (ensure (x >= 1)).
Proof.
  intros.
  unfold entails, ensure, f, ensure. simpl. intros.
  split. constructor.
  lia.
Qed.

Example ex4: forall (f:nat -> W unit) x,
  entails (f x;; ensure (x = 0))
    (f x;; ensure (x >= 0)).
Proof.
  unfold entails, ensure. simpl. intros.
  split. assumption.
  intros.
  destruct H0 as (?&?&?).
  exists x0.
  split. assumption. lia.
Qed.
