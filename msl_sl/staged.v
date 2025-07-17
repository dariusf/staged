
(* Require Import msl.msl_standard. *)
(* Require Import msl.knot_hered. *)
(* Require Import msl.functors. *)
Require Import msl.base.
(* Require Import msl.functors. *)
(* Require Import msl.functor_facts. *)
(* Require Import msl.knot. *)
Require Import msl.knot_hered.

Require Import msl.functors.
Require Import msl.ageable.

Import CovariantFunctor.
Import CovariantFunctorLemmas.
Import CovariantFunctorGenerator.

From Coq Require Import Classes.RelationClasses.
From Coq Require Morphisms Program.Basics.

From Staged Require Export HeapF.
From Staged Require Export LibFmap.
From Staged Require Export ExtraTactics.

Local Open Scope string_scope.
(* Local Open Scope nat_scope. *)
Local Open Scope Z_scope.
Local Open Scope list_scope.

Set Implicit Arguments.
Definition var : Type := string.
Notation var_eq := String.string_dec.

Definition loc := nat.

Inductive val :=
  | vunit : val
  | vint : Z -> val.

#[global]
Instance Inhab_val : Inhab val.
Proof.
  constructor.
  exists vunit.
  constructor.
Qed.

Module Val.
  Definition value := val.
End Val.

Module Export Heap := HeapF.HeapSetup Val.

Definition empty_heap : heap := Fmap.empty.

Module TFP <: TY_FUNCTOR_PROP.

  (* Definition T := Prop. *)
  (* Definition T_bot := False. *)

  Definition F1 : Type -> Type :=
    fun X => var -> heap -> heap -> val -> X.

  Definition fmap : forall A B, (A -> B) -> F1 A -> F1 B :=
    fun A B (g : A -> B) (psi : F1 A) =>
    fun x h1 h2 v =>
      g (psi x h1 h2 v).

  Lemma fmap_id : forall A, fmap (id A) = id (F1 A).
  Proof.
    unfold fmap, id, compose, option_map.
    intro.
    extensionality FA a.
    extensionality FB v.
    reflexivity.
  Qed.
  Lemma fmap_comp : forall A B C (f:B -> C) (g:A -> B),
    fmap f oo fmap g = fmap (f oo g).
  Proof.
    unfold fmap, id, compose, option_map.
    intros.
    extensionality FA a.
    extensionality FB b.
    reflexivity.
  Qed.

  Definition F :=
    {| _functor := F1;
      CovariantFunctor.fmap := fmap;
      functor_facts :=
        {| ff_id := fmap_id;
          ff_comp := fmap_comp |} |}.

  Definition other : Type := unit.
End TFP.

Export TFP.


(* Module K := KnotProp(TFP). *)
(* Module KL := KnotProp_Lemmas(K). *)

Module K := KnotHered(TFP).
(* Module KL := KnotHered_Lemmas(K). *)

Export K.
(* Export KL. *)

Definition env : Type := knot.
Definition flow : Type := env -> heap -> heap -> val -> Prop.

Definition ens (H:hprop) : flow :=
  fun s h1 h2 v =>
  (* TODO ignore s *)
    True.

(* Check k_age1. *)
Search "age".

Check predicate.
Print predicate.

Definition unk (f:var) (v:val) : flow :=
  fun s h1 h2 v =>
    let (k, m) := unsquash s in
    let f1 := m f in
    let x := f1 h1 h2 v in
    (* forall  *)
    (* let y := squash (k, m) in *)
    (* x must be applied to an env *)
  (* age *)
    x (y, tt)
    (* True *)
    .

(* TODO parameters *)