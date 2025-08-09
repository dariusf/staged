
From SLF Require Import LibSepFmap.
From Coq Require Import Lia.

Definition loc := nat.
Definition heap (A:Type) : Type := fmap loc A.

Set Implicit Arguments.

Section Refinement.
  Variable t : Type.
  Definition S := heap t.

Definition Pred : Type -> Type := fun a => a -> Type.

Definition K : forall {A} {a : Type}, Pred S -> (forall s:S, A s -> a -> Pred S) := fun a _ pt _ _ _ s => pt s.

Definition Ka : forall {A} {a : Type}, (a -> Pred S) -> (forall s:S, A s -> a -> Pred S) := fun _ _ pt _ _ a s => pt a s.

Arguments K [A].

Arguments Ka [A].

Definition subset : Pred S -> Pred S -> Type :=
  fun P1 P2 => forall s, P1 s -> P2 s.

Notation "P1 ⊂ P2" := (subset P1 P2) (at level 80) : type_scope.

Record PT (a : Type) : Type :=
  MkPT { pre : Pred S;
         post : (forall s : S, pre s -> a -> Pred S) }.

Inductive Refines {a : Type} (pt1 pt2 : PT a) : Type :=
  | Refinement :
    forall (d : pre pt1 ⊂ pre pt2),
      (forall (s : S) (x : pre pt1 s) v, post pt2 s (d s x) v ⊂ post pt1 s x v) -> Refines pt1 pt2.

Definition refines {a : Type} (pt1 pt2 : PT a) : Type :=
  forall (d : pre pt1 ⊂ pre pt2),
    (forall (s : S) (x : pre pt1 s) v, post pt2 s (d s x) v ⊂ post pt1 s x v).

(* Notation "PT1 ⊏ PT2" := (Refines PT1 PT2) (at level 90, no associativity) : type_scope. *)

Notation "[ p , q ]" := (MkPT p q) (at level 70) : type_scope.


(* Definition semantics {A : Type} (pt : PT A) : Pred (A * S) -> Pred S
  := fun P s =>
      {p : pre pt s
       & forall s' v, post pt s p v s' -> P (v, s')}. *)

Definition SkipPT {a : Type} : PT a :=
  let skipPre := fun s => True in
  let skipPost := fun s pres v s' => s = s' in
  [skipPre , skipPost].


Definition BindPT {a b : Type} (pt1 : PT a) (pt2 : a -> PT b) : PT b :=
  let seqPre := fun s => {pres : pre pt1 s & forall t v, post pt1 s pres v t -> pre (pt2 v) t} in

  let seqPost : forall s : S, seqPre s -> b -> Pred S := fun (s : S) (pres : seqPre s) (v : b) (s' : S) =>
    { t : S &
    { x : a &
    { q : post pt1 s (projT1 pres) x t &
     post (pt2 x) t (projT2 pres t x q) v s'}}}
  in
  [seqPre , seqPost].

End Refinement.


Section Effects.

Variable v : Type.


Inductive W (a : Type) : Type :=
  (* | New    : v -> (Ptr -> W a) -> W a *)
  (* | Read   : Ptr -> (v -> W a) -> W a *)
  (* | Write  : Ptr -> v -> W a  -> W a *)
  (* | While  : (S v -> S v -> Type) -> (S v -> bool) -> W unit -> W a -> W a *)
  | Spec   : PT v a -> W a
  | Return : a -> W a.

(* Fixpoint *)
Definition semantics {a : Type} (w: W a) : PT v a :=
  match w with
    (* | New v k =>
      let pre := fun s =>
                  { ptr : Ptr & prod (find s ptr = None)
                              (pre (semantics (k ptr)) (update s ptr v)) } in
      let post := fun s pres v' s' =>
                    post (semantics (k (projT1 pres))) (update s (projT1 pres) (v)) (snd (projT2 pres)) v' s' in

      MkPT pre post
    | Read ptr k =>
      let readPre := fun h => { x : v & find h ptr = Some x} in
      let pre := fun s => {p : readPre s & pre (semantics (k (projT1 p))) s} in
      let post := fun s pres x s' =>
                    post (semantics (k (projT1 (projT1 pres)))) s (projT2 pres) x s' in
      MkPT pre post
    | Write ptr x k =>
      let pre := fun s =>
                   prod ({y : v & find s ptr = Some y})
                        (pre (semantics k) (update s ptr x)) in
      let post := fun s pres res s' =>
                    post (semantics k) (update s ptr x) (snd pres) res s' in
      MkPT pre post
    | While inv c body k => SeqPT (WhilePT' inv c (semantics body)) (@semantics a k) *)
    | Spec s => s
    | Return  x => MkPT (fun s => True) (fun s _ v s' => s = s' /\ v = x)
  end.

Definition wrefines {a : Type} (w1 w2 : W a) :=
  Refines (semantics w1) (semantics w2).

(* somehow wrefines is backwards *)
Notation entails a b := (wrefines b a).

(* Fixpoint *)
(* {struct w} *)
Definition bind {a b : Type} (w : W a) (k : a -> W b) : W b :=
  match w with
  (* | New v c  => New v (fun p => bind (c p) k)
  | Read p c => Read p (fun v => bind (c v) k)
  | Write p v c => Write p v (bind c k)
  | While Inv cond body c => While Inv cond body (bind c k) *)
  | Spec pt => Spec (BindPT pt (fun x => semantics (k x)))
  | Return x => k x
  end.

Definition seq (A B : Type) (s1:W A) (s2:W B) : W B
 := bind s1 (fun (_:A) => s2).

(* Infix ";;" := seq (at level 38, right associativity). *)

Notation "c1 ;; c2" := (bind c1 (fun _ => c2)) (at level 100, right associativity).

(* https://www.cs.cornell.edu/courses/cs6115/2017fa/notes/Monads.html *)
Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
                             (right associativity, at level 84, c1 at next level).


Definition require (p:Prop) : W unit :=
  Spec (MkPT (fun _ => p) (fun _ _ _ _ => True)).

Definition ensure (Q:Prop) : W unit :=
  Spec (MkPT (fun _ => True) (fun _ _ _ _ => Q)).

Example ex1: forall x,
  entails (require (x >= 1)) (require (x > 1)).
Proof.
  intros.
  unfold entails.
  eapply Refinement.
  { simpl. intros.
  unfold subset.
  easy. }
  Unshelve.
  { unfold subset. simpl. intros.
    lia. }
Qed.

Example ex2: forall x,
  entails (ensure (x > 1)) (ensure (x >= 1)).
Proof.
  intros.
  unfold entails.
  eapply Refinement.
  { simpl. intros.
  unfold subset.
  intros.
  lia. }
  Unshelve.
  { unfold subset. simpl. intros.
    easy. }
Qed.

End Effects.
