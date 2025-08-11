
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Lia.
From Coq Require Import Morphisms Program.Basics.

Set Implicit Arguments.

Record PP (A:Type): Type := pre_post { pre: Prop; post: A -> Prop }.

Definition refines (A:Type) (s1 s2:PP A): Prop
:= pre s2 -> ( pre s1 /\ (forall a:A, post s1 a -> post s2 a) ).

Definition pp_ret (A:Type) (a:A): PP A :=
  pre_post True (fun b => a=b).

Definition pp_bind (A B:Type) (s1:PP A) (s2:A -> PP B): (PP B) :=
  pre_post (pre s1 /\ (forall a:A, post s1 a -> pre (s2 a)))
    (fun b => exists a:A, post s1 a /\ post (s2 a) b).


Inductive W (a : Type) : Type :=
  | Spec   : PP a -> W a
  (* | Eff  : nat -> (nat -> W a) -> W a *)
  | Return : a -> W a.

(* Fixpoint *)
Definition semantics {a : Type} (w: W a) : PP a :=
  match w with
    | Spec s => s
    (* | Eff s => s *)
    | Return x => pre_post True (fun v => v = x)
  end.

Definition wrefines {a : Type} (w1 w2 : W a) :=
  refines (semantics w1) (semantics w2).

Notation entails a b := (wrefines a b).


#[global]
Instance Proper_entails_entails {a:Type} : Proper
  (flip (@wrefines a) ==> @wrefines a ==> impl)
  (@wrefines a).
Proof.
  unfold Proper, respectful, impl, flip.
  unfold entails, refines. intros.
  specialize (H0 H2). destruct H0.
  specialize (H1 H0). destruct H1.
  specialize (H H1). destruct H.
  split.
  { assumption. }
  { intros. eauto. }
Qed.

Instance entails_refl : forall A, Reflexive (@wrefines A).
Proof.
  unfold Reflexive, wrefines, refines. intros. auto.
Qed.
Instance entails_trans : forall A, Transitive (@wrefines A).
Proof.
  unfold Transitive, wrefines, refines. intros.
  specialize (H0 H1). destruct H0.
  specialize (H H0). destruct H.
  split. assumption.
  intros. eauto.
Qed.

(* Fixpoint *)
Definition bind {a b : Type} (w : W a) (k : a -> W b) : W b :=
  match w with
  | Spec pt => Spec (pp_bind pt (fun x => semantics (k x)))
  | Return x => k x
  end.

Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
                             (right associativity, at level 84, c1 at next level).

Definition seq (A B : Type) (s1:W A) (s2:W B) : W B
 := bind s1 (fun (_:A) => s2).

Notation "c1 ;; c2" := (bind c1 (fun _ => c2)) (at level 100, right associativity).

Definition require (p:Prop) : W unit := Spec (pre_post p (fun _ => True)).

Definition ensure (p:Prop) : W unit := Spec (pre_post True (fun _ => p)).

Definition val {A:Type} (a:A) : W A :=
  Return a.

Example ex0: forall x,
  entails (ensure (x > 1)) (ensure (x >= 1)).
Proof.
  intros.
  unfold entails, refines. simpl. intros.
  split. constructor. lia.
Qed.

Example ex01: forall x,
  entails (ensure (x > 1)) (ensure (x >= 1)).
Proof.
  intros.
  rewrite ex0.
  reflexivity.
Qed.

Example ex1: forall x,
  entails (require (x >= 1)) (require (x > 1)).
Proof.
  intros.
  unfold entails, refines. simpl. intros.
  split. lia.
  constructor.
Qed.

Example ex2: forall x,
  entails (require (x = 1))
    (y <- val 1;; require (x + 1 = 2)).
Proof.
  intros.
  unfold entails, refines. simpl.
  intros.
  split. lia. constructor.
Qed.

Definition f x := ensure (x = 1).

Fixpoint fact n : W unit :=
  match n with
  | O => ensure (n = 1)
  | S n1 => x <- fact n1;; ensure (x = tt)
  end.

Example ex3: forall x,
  x >= 0 ->
  entails (f x)
    (ensure (x >= 1)).
Proof.
  intros.
  unfold entails, refines. simpl.
  split. constructor. lia.
Qed.

Lemma cancel_seq: forall (w w1 w2:W unit),
  entails w1 w2 ->
  entails (w;; w1) (w;; w2).
Proof.
  intros.
  destruct w.
  {
  unfold bind.
  unfold pp_bind.
  unfold entails, refines. simpl.
  intros.
  split.
    {
      destruct H0. split. assumption.
      unfold entails, refines in H.
      intros. specialize (H1 a H2).
      specialize (H H1). destruct H.
      assumption.
    }
    {
      intros. destruct H1. destruct H1.
      exists x. split. assumption. destruct H0. specialize (H3 x H1).
      unfold entails, refines in H.
      specialize (H H3).
      destruct H.
      apply H4.
      assumption.
    }
  }
  {
    unfold bind.
    assumption.
  }
Qed.

Lemma cancel_functions: forall (f:nat->W unit) x (w1 w2:W unit),
  entails w1 w2 ->
  entails (f x;; w1) (f x;; w2).
Proof.
  intros.
  apply cancel_seq.
  assumption.
Qed.

Lemma cancel_functions1: forall (f:nat->W unit) x (w1 w2:W unit),
  entails w1 w2 ->
  entails (f x;; w1) (f x;; w2).
Proof.
  intros.
  rewrite (cancel_seq (f0 x)).
  2: { eassumption. }
  reflexivity.
Qed.

Example ex4: forall (f:nat -> W unit) x,
  entails (f x;; ensure (x = 0))
    (f x;; ensure (x >= 0)).
Proof.
  intros.
  apply cancel_seq.
  unfold entails, refines. simpl. intros.
  split. constructor.
  lia.
Qed.
