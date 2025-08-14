
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Lia.
From Coq Require Import Morphisms Program.Basics.

Set Implicit Arguments.

Definition Cont (r a : Type) := (a -> r) -> r.

Definition cont_ret (r a:Type) (x:a): Cont r a :=
  fun k => k x.

Definition cont_bind (r a b:Type) (m:Cont r a) (f:a -> Cont r b): Cont r b :=
  fun c => m (fun a => f a c).

Definition eval_cont (a:Type) (k : Cont a a) : a := k (fun x => x).

Definition shift f : Cont unit := f.

Definition reset f : W unit := eval_cont f.

   (* member this.Bind (m, f) = fun c => m (fun a -> f a c) *)
   (* member this.Return x = fun k -> k x *)

  (* pre_post True (fun b => a=b). *)

(* Definition cont_bind (A B:Type) (s1:PP A) (s2:A -> PP B): (PP B) :=
  pre_post (pre s1 /\ (forall a:A, post s1 a -> pre (s2 a)))
    (fun b => exists a:A, post s1 a /\ post (s2 a) b). *)

Record PP (A:Type): Type := pre_post { pre: Prop; post: A -> Prop }.

Definition refines (A:Type) (s1 s2:PP A): Prop
:= pre s2 -> ( pre s1 /\ (forall a:A, post s1 a -> post s2 a) ).

Definition pp_ret (A:Type) (a:A): PP A :=
  pre_post True (fun b => a=b).

Definition pp_bind (A B:Type) (s1:PP A) (s2:A -> PP B): (PP B) :=
  pre_post (pre s1 /\ (forall a:A, post s1 a -> pre (s2 a)))
    (fun b => exists a:A, post s1 a /\ post (s2 a) b).


Definition W (a:Type) := Cont (PP a) (PP a).

Definition entails (A:Type) (s1 s2:W A): Prop :=
  refines (eval_cont s1) (eval_cont s2).

Definition ret (A:Type) (v:A) : W A :=
  cont_ret (pp_ret v).

Definition val := ret.

Definition ensure (A:Type) (q:A -> Prop) : W A :=
  cont_ret (pre_post True q).

Definition ensure_ (q:Prop) : W unit :=
  cont_ret (pre_post True (fun _ => q)).

Definition require (p:Prop) : W unit :=
  cont_ret (pre_post p (fun _ => True)).

Definition shift f : W unit := f.
Definition reset f : W unit := eval_cont f.


(* Definition cont_bind (r a b:Type) (m:Cont r a) (f:a -> Cont r b): Cont r b :=
  fun c => m (fun a => f a c). *)

Definition bind (a b:Type) (m:W a) (f:a -> W b): W b :=
  fun c => cont_bind m (fun pa => pp_bind pa (fun y => 0) c).

Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
                             (right associativity, at level 84, c1 at next level).

Notation "c1 ;; c2" := (bind c1 (fun _ => c2)) (at level 100, right associativity).

(* evalCont (return x) = x *)

(* resetT :: (Monad m) => ContT r m r -> ContT r' m r
resetT = lift . evalContT

shiftT :: (Monad m) => ((a -> m r) -> ContT r m r) -> ContT r m a
shiftT f = ContT (evalContT . f) *)
(*

shiftT f = evalContT . f

shiftT f = (fun x -> evalContT (f x))

*)

Example ex0: forall x,
  entails (ensure_ (x > 1)) (ensure_ (x >= 1)).
Proof.
  intros.
  unfold entails, refines. simpl. intros.
  split. constructor. lia.
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
    (cont_bind (val 1) (fun y =>
    (* require (x + 1 = 2) *)
    (* ensure_ True *)
    val 2
    )).
    (* (y <- val 1;; require (x + 1 = 2)). *)
Proof.
  intros.
  unfold entails, refines. simpl.
  intros.
  split. lia. constructor.
Qed.
