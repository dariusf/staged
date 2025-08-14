
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

Definition cont_shift (a r:Type) (f:(a -> r) -> r): Cont r a := f.

Definition cont_reset (a:Type) (f: Cont a a): a := eval_cont f.

(*

f (fun a ->
  g (fun r1 ->
  ) : r
) : r

f : (a -> r) -> r
g : (b -> r) -> r

*)

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

Module One.
(* Definition W (a:Type) := Cont (PP a) (PP a). *)
Definition W (r a:Type) := Cont r (PP a).

Definition entails (a:Type) (s1 s2:W (PP a) a): Prop :=
  refines (eval_cont s1) (eval_cont s2).

(* Definition entails (a:Type) (s1 s2:W a a): Prop :=
  forall k, refines (s1 k) (s2 k). *)

(* Definition entails (a:Type) (s1 s2:W (PP a) a): Prop :=
  refines (s1 id) (s2 id). *)

Definition ret (r a:Type) (v:a) : W r a :=
  cont_ret (pp_ret v).

Definition val := ret.


(* Definition cont_bind (r a b:Type) (m:Cont r a) (f:a -> Cont r b): Cont r b :=
  fun c => m (fun a => f a c). *)

Definition bind := cont_bind.

(* Definition bind (r a b:Type) (m:Cont r a) (f:a -> Cont r b): Cont r b :=
  fun c => m (fun a => f a c). *)

(* Definition bind (a b:Type) (m:W ra) (f:a -> W b): W b :=
  fun c => cont_bind m (fun pa => pp_bind pa (fun y => 0) c). *)

(* Check cont_bind (val 1) (fun pp =>
  cont_ret (pp_bind pp (fun a =>
    pp_ret (a+1)
(* 0 *)
    ))). *)

(* Definition wbind (r a b:Type) (m:W r a) (f:a -> W r b): W r b :=
  fun c => cont_bind m (fun pa => pp_bind pa (fun y =>
      (* can build a cont by applying f, but need to return a pp *)
    cont_bind (f y) (fun pb =>
      (* cont_ret 0 *)
      cont_ret pb
      )) c).
 *)
(* Definition wbind m f :=
  cont_bind m (fun pp =>
  cont_ret (pp_bind pp (fun a => 0)))
. *)

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

Definition ensure (r a:Type) (q:a -> Prop) : W r a :=
  cont_ret (pre_post True q).

Definition ensure_ (r:Type) (q:Prop) : W r unit :=
  cont_ret (pre_post True (fun _ => q)).

Definition require (r:Type) (p:Prop) : W r unit :=
  cont_ret (pre_post p (fun _ => True)).

Definition shift := cont_shift.
Definition reset := cont_reset.


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

(* Example ex2: forall x,
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
Qed. *)


End One.
