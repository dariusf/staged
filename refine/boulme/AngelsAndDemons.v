
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Lia.
From SLF Require Import LibTactics.

Set Implicit Arguments.

(* sdemon means: program terminates and for all outputs the post is satisfied *)
(* angel means: there is an output for which the post is satisfied. *)
Definition is_wp_pair (A : Type) (sdemon angel : (A -> Prop) -> Prop) :=
  forall Q : A -> Prop,
  (sdemon Q <-> sdemon (fun _ => True) /\ (forall a : A, angel (eq a) -> Q a))
  /\ (angel Q <-> (exists a : A, angel (eq a) /\ Q a)).

Record W (A : Type) : Type :=
  {
   sdemon : (A -> Prop) -> Prop;
   angel : (A -> Prop) -> Prop;
   DScorrect : is_wp_pair sdemon angel
  }.


(* the wp of true is the condition under which the program terminates? *)
Notation "'pre' s" := (sdemon s (fun _ => True)) (at level 70, s at level 0).

(* a is a possible result of s *)
Notation "'post' s a":= (angel s (eq a)) (at level 70, s at level 0, a at level 0).


(* angel assumes precondition because there may be nonterminating paths *)
Definition entails (A : Type) (s1 s2 : W A) :=
  forall R : A -> Prop,
  (sdemon s2 R -> sdemon s1 R) /\ (pre s2 -> angel s1 R -> angel s2 R).

(* preorder *)
Lemma entails_refl : forall (A : Type) (s : W A), entails s s.
Proof.
  firstorder auto.
Qed.

Lemma entails_trans :
 forall (A : Type) (s1 s2 s3 : W A),
 entails s1 s2 -> entails s2 s3 -> entails s1 s3.
Proof.
  firstorder auto.
Qed.

Lemma require_correct :
 forall p : Prop, is_wp_pair (fun R => p /\ R tt) (fun R => R tt).
Proof.
  unfold is_wp_pair in |- *; firstorder eauto; subst; auto.
Qed.

Definition require (p:Prop) : W unit
 := Build_W (sdemon:=fun R => p /\ R tt) (angel:=fun R => R tt) (require_correct p).

Lemma ensure_correct : forall p : Prop,
  is_wp_pair (fun R => p -> R tt) (fun R => p /\ R tt).
Proof.
  unfold is_wp_pair in |- *; firstorder eauto; subst; auto.
Qed.

Definition ensure (p:Prop) : W unit
 := Build_W (sdemon:=fun R => p -> R tt) (angel:=fun R => p /\ R tt) (ensure_correct p).

Lemma any_correct :
 forall A : Type,
 is_wp_pair (fun R => forall a : A, R a) (fun R => exists a : A, R a).
Proof.
  unfold is_wp_pair in |- *; firstorder eauto.
Qed.

Definition any (A : Type) : W A
  := Build_W
      (sdemon:=fun R => forall a : A, R a)
      (angel:=fun R => exists a : A, R a)
      (any_correct (A:=A)).

Lemma val_correct :
 forall (A : Type) (a : A), is_wp_pair (fun R => R a) (fun R => R a).
Proof.
  unfold is_wp_pair; firstorder eauto; subst; auto.
Qed.

Definition val (A : Type) (a:A) : W A
 := Build_W (sdemon:=fun R => R a) (angel:=fun R => R a) (val_correct a).

Lemma sdemon_weaken :
 forall (A : Type) (s : W A) (R1 R2 : A -> Prop),
 sdemon s R1 -> (forall a : A, R1 a -> R2 a) -> sdemon s R2.
Proof.
  intros A s R1 R2 H. case (DScorrect s R1). case (DScorrect s R2).
  intros.
   intuition eauto.
Qed.

(* Lemma bind_correct :
 forall (A B : Type) (s1 : W A) (s2 : A -> W B),
 is_wp_pair (fun R => sdemon s1 (fun a => sdemon (s2 a) R))
            (fun R => angel s1 (fun a => angel (s2 a) R)).
Proof.
  intros A B s1 s2.
  (* constructor. *)
  (* unfold is_wp_pair. intros. *)
  split.
  { (* sdemon *)
  (* sdemon <-> *)
  (* constructor 1. *)
   (* sdemon -> 1 *)
   (* {

   } *)
    iff H.
    {
      split.
      (* sdemon -> _ /\ *)
      {
        eapply sdemon_weaken; eauto.
        simpl.
        intros.
        Unset Printing Notations.
        applys sdemon_weaken H0.
        constructor.
      }
      (* eauto with wipi. *)
      {
        (* sdemon -> /\ _ *)
        intros a H1; case (angel_unfold _ _ H1).
        intros a0 H2; lapply (sdemon_unfold _ _ a0 H); firstorder auto.
        apply (sdemon_unfold (s2 a0)); auto.
      }
    }
  {
    (* -> sdemon *)
    intros. apply sdemon_fold; firstorder (eauto with wipi).
    apply sdemon_fold.
    apply (sdemon_unfold s1 (fun a : A => pre (s2 a))); auto.
    intuition eauto with wipi.
  }
  }
   (* angel *)
   constructor 1.
   (* angel -> *)
   intros H; case (angel_unfold _ _ H);
   intros a H0; case (angel_unfold (s2 a) R).
   firstorder auto.
   intros b H1; constructor 1 with (x:=b); firstorder auto .
   eauto with wipi.
   (* -> angel *)
   intros H; case H; clear H; intros b H.
   case (angel_unfold s1 (fun a : A => post (s2 a) b));
   intuition eauto with wipi.
Qed.

Definition bind (A B : Type) (s1:W A) (s2:(A -> W B)) : W B
 := Build_W
       (sdemon:=fun R => sdemon s1 (fun a => sdemon (s2 a) R))
       (angel:=fun R => angel s1 (fun a => angel (s2 a) R))
       (bind_correct s1 s2).


Definition seq (A B : Type) (s1:W A) (s2:W B) : W B
 := bind s1 (fun (_:A) => s2).

(* Infix ";;" := seq (at level 38, right associativity). *)

Notation "c1 ;; c2" := (bind c1 (fun _ => c2)) (at level 100, right associativity).

(* https://www.cs.cornell.edu/courses/cs6115/2017fa/notes/Monads.html *)
Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
                             (right associativity, at level 84, c1 at next level).

Example ex1: forall x,
  entails (require (x >= 1)) (require (x > 1)).
Proof.
  intros.
  unfold entails, require. intros.
  destruct H.
  split. lia.
  assumption.
Qed. *)
