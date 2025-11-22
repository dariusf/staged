Require Import Utf8.
Require Import Binding.Lib.
Require Import SetoidClass Morphisms.

Definition eq_ext {A B} (f g : A → B) := ∀ x, f x = g x.

Lemma Equivalence_eq_ext {A B} : Equivalence (@eq_ext A B).
Proof.
  split.
  - intros Γ x; reflexivity.
  - intros Γ₁ Γ₂ HEq x; symmetry; apply HEq.
  - intros Γ₁ Γ₂ Γ₃ HEq₁ HEq₂ x; etransitivity; [apply HEq₁ | apply HEq₂].
Qed.

Instance Setoid_equiv {A B} : Setoid (A → B) := Build_Setoid Equivalence_eq_ext.

Definition empty_env {A} : ∀ (x : ∅), A := λ x, match x with end.

Definition extend {V : Set} {A} (Γ : V → A) (τ : A) : inc V → A :=
  λ x, match x with VZ => τ | VS x => Γ x end.

Definition compose {A B C} (f : B → C) (g : A → B) (x : A) := f (g x).

Set Warnings "-notation-overridden".
Module Notations.
  Notation "f • g" := (compose f g) (at level 45, right associativity).
  Notation "f ▹ v" := (extend f v) (at level 40, v at next level, left associativity).
  Notation "□" := empty_env.
  Notation "x ≡ y" := (equiv x y) (at level 70, no associativity).
End Notations.
Import Notations.
Set Warnings "notation-overridden".

Arguments compose {A B C} f g x /.

Ltac destr_refl x :=
  match type of x with
  | inc _ => destruct x as [| x]; [term_simpl; reflexivity | destr_refl x]
  | _ => term_simpl
  end.

Ltac solve_simple_eq :=
  match goal with
  | [ H: ?X ≡ ?Y |- ?X ?x = ?Y ?x ] => apply H
  | [ |- ?f ?v1 = ?f ?v2 ] => f_equal; solve_simple_eq
  | _ => now eauto
  end.

Ltac solve_equiv :=
  match goal with
  | [|- ?X ≡ ?Y] =>
      let x := fresh "x"
      in intros x; destr_refl x; solve_simple_eq
  | _ => eassumption || reflexivity
  end.

Instance equiv_extend {A B : Set} : Proper (equiv ==> eq ==> equiv) (@extend A B).
Proof.
  intros f g EQ v₁ v₂ EQv; subst; solve_equiv.
Qed.

Instance equiv_compose {A B C : Set} : Proper (equiv ==> equiv ==> equiv) (@compose A B C).
Proof.
  intros f₁ f₂ EQf g₁ g₂ EQg x; simpl; now rewrite EQf, EQg.
Qed.

Require Import Binding.Set.
#[warnings="-notation-overridden"] Import ArrowNotations.

Lemma env_extend_equiv (V : Type) (A B : Set) (Δ₁ : A → V) Δ₂ (δ : B [→] A) (κ : V)
      (HEq : Δ₂ ≡ Δ₁ • δ) :
  Δ₂ ▹ κ ≡ (Δ₁ ▹ κ) • ( δ ↑ : inc B [→] inc A)%bind.
Proof.
  solve_equiv.
Qed.
