
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
  | Sh   : ((a -> a) -> W a) -> W a
  | Rs   : W a -> W a
  | Return : a -> W a.

Variant domain a :=
  | d_pre : PP a -> domain a
  | d_shift : ((a -> a) -> W a) -> (a -> a) -> domain a.

Inductive semantics1 {a : Type} : W a -> domain a -> Prop :=
  | s_spec : forall p,
    semantics1 (Spec p) (d_pre p)
  | s_ret : forall x,
    semantics1 (Return x) (d_pre (pre_post True (fun v => v = x)))
  | s_sh : forall b k,
    semantics1 (Sh b) (d_shift b k)
  | s_rs : forall f b k d,
    semantics1 f (d_shift b k) ->
    semantics1 (b k) d ->
    semantics1 (Rs f) d
  .

Definition entails {a : Type} (w1 w2 : W a) :=
  forall d,
  (* d is not equal, refines *)
    semantics1 w1 d -> semantics1 w2 d.