
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Lia.
From Coq Require Import Morphisms Program.Basics.

Set Implicit Arguments.

From Coq Require Import Lia.

Unset Automatic Proposition Inductives.

Inductive Free (R A:Type) : Type :=
  | pure : A -> Free R A
  (* | impure : A -> Free A *)
  (* | shift : ((A -> R) -> R) -> Free R A *)
  | reset : Free R A -> Free R A
  .

Definition ret (R A:Type) (a:A) : Free R A := pure _ a.
Fixpoint bind (R A B:Type) (m:Free R A) (f:A -> Free R B) : Free R B :=
  match m with
  | pure _ a => f a
  (* | impure a => f a *)
  | reset a => reset (bind a f)
  (* | shift fk => fk f *)
  end.


  (* pure a. *)

  (* return x = Pure x

  -- Free f a -> (a -> Free f b) -> Free f b
  (Pure x) >>= g = g x
  (Op y)   >>= g = Op $ fmap (>>= g) y *)