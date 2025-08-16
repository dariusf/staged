
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Lia.
From Coq Require Import Morphisms Program.Basics.
From Coq Require Import Lists.List.

Import ListNotations.
Open Scope list_scope.

Set Implicit Arguments.

Definition Cont (i o a : Type) := (a -> i) -> o.

Definition ret (r a:Type) (x:a): Cont r r a :=
  fun k => k x.

Definition bind (m i o a b:Type)
  (m1:Cont m o a) (f:a -> Cont i m b): Cont i o b :=
  fun c => m1 (fun a => (f a) c).

Definition eval_cont (a o:Type) (k : Cont a o a) : o := k (fun x => x).

(* Definition shift (a i o:Type) (f:(a -> i) -> o): Cont i o a := f.

Definition reset (a o:Type) (f: Cont a o a): o := eval_cont f. *)

Definition shift {tau t a s b} (f : (tau -> Cont t t a) -> Cont s b s) : Cont a b tau :=
  fun k => f (fun tau => ret (k tau)) id.

Definition reset {i o a} (c : Cont i o i) : Cont a a o :=
  fun k => k (c id).

Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
                             (right associativity, at level 84, c1 at next level).

Fixpoint append_sh {A b a} (l : list A)
  : Cont b (list A -> Cont a a b) (list A)
  :=
  match l with
    | [] => shift (fun k => ret k)
    | hd :: tl =>
      tl1 <- append_sh tl;;
      ret (hd :: tl1)
  end.

Example append123 {A T} : Cont A A (list nat -> Cont T T (list nat)) :=
  reset (append_sh [1;2;3]).

Example test1 : list nat := eval_cont (k <- append123;; k [4;5;6]).

Print test1.
Eval compute in test1.

(* Lemma reduction: forall (A:Type),
  (reset (shift (fun k => ret k))) = id. *)

(* Lemma reduction:  *)

Lemma append_sh_correct: forall (xs ys:list nat),
  eval_cont (k <- (reset (append_sh xs));; k ys) = app xs ys.
Proof.
  intros xs.
  induction xs; intros.
  {
    simpl.

    Unset Printing Notations. Set Printing Coercions. Set Printing Parentheses.
    admit.
  }
Abort.
