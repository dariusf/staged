
From Coq Require Import Lia.

(* Inductive Free (C:Type) (R:C->Type) : Type -> Type :=
  | pure : forall a, Free C R a
  | step : forall a (c:C), (R c -> Free C R a) -> Free C R a
  .

(* Arguments Free [C R].
Arguments pure [C R]. *)

Variant CNondet :=
  Choice | Failure.

Definition RNondet c : Type :=
  match c with
  | Choice => bool
  | Failure => False
  end.

Definition Nondet := @Free CNondet RNondet.

Definition handleList (a:Type) (c:Nondet a) : list a :=
  match c with
  | pure _ _ x => x::nil
  (* | step (Op) => bool *)
  (* | Failure => False *)
  end. *)


(* Variant CNondet :=
  Choice | Failure. *)

(* Definition RNondet c : Type :=
  match c with
  | Choice => bool
  | Failure => False
  end. *)

Unset Automatic Proposition Inductives.
Inductive empty : Type := .

Inductive Nondet (A:Type) : Type :=
  | pure : A -> Nondet A
  | choice : (bool -> Nondet A) -> Nondet A
  | failure : (empty -> Nondet A) -> Nondet A
  .

Fixpoint handleList {a:Type} (c:Nondet a) : list a :=
  match c with
  | pure _ x => x::nil
  | choice _ k => handleList (k true) ++ handleList (k false)
  | failure _ _ => nil
  end.

Fixpoint handlePT {a:Type} (c:Nondet a) : (a -> Prop) -> Prop :=
  fun Q =>
    match c with
    | pure _ x => Q x
    | choice _ k => handlePT (k true) Q /\ handlePT (k false) Q
    | failure _ _ => False
    end.

Fixpoint bind {a b : Type}
  (w : Nondet a) (k : a -> Nondet b) : Nondet b :=
  match w with
  | pure _ x => k x
  | choice _ g => choice _ (fun x => bind (g x) k)
  | failure _ g => failure _ (fun x => bind (g x) k)
  end.

Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
                             (right associativity, at level 84, c1 at next level).

Definition a :=
  choice _ (fun x => if x then pure _ 1 else pure _ 2).

Definition b := handleList a.

Compute b.

Definition a1 :=
  x <- choice _ (fun z => if z then pure _ 1 else pure _ 2);; pure _ x.

Compute (handleList a1).

(* get :: State s <: sig => Free sig s
get = inject (Get return)

put :: State s <: sig => s -> Free sig ()
put s = inject (Put s (return ())) *)

Definition Choice := choice _ (pure _).
Definition Failure := failure _ (pure _).
(* Check Failure. *)

Definition a2 :=
  x <- Choice;;
  if x then pure _ 1 else pure _ 2.
Compute (handleList a2).

Definition a3 :=
  x <- Choice;;
  Failure.
Compute (handleList a3).

Definition a4 :=
  let Q := (fun x => x > 0) in
  handlePT a2 Q.

Lemma a5: a4.
Proof.
  unfold a4.
  simpl.
  split; lia.
Qed.

  (* x <- choice;;
  if x then pure 1 else pure 2. *)

(* Definition bind {a b : Type} (w : Nondet a) (k : a -> Nondet b) : Nondet b :=
  match w with
  (* | Spec pt => Spec (BindPT pt (fun x => semantics (k x)))
  | Return x => k x *)
  end. *)



(*
Set Implicit Arguments.

Fixpoint bind m f :=
  match m with
  | pure _ _ _ x => f x
  | step _ _ _ c k => step _ _ _ c (fun x => bind (k x) f)
  end
  . *)

(* Check pure.
Check pure _ _ _ 1.
Check fun c => step c. *)
(* Check fun c => step c (pure _ _ _ ). *)


(* Definition grec (C:Type) (R:C->Type) : Type := *)
(* fun C R => bool. *)
  (* forall (c:C), Free C R (R c). *)

(* Definition call := fun arg => step arg (fun x => @pure _ _ _ x). *)

(* Check call 1. *)
