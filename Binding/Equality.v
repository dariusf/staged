Require Import Utf8.
Require Import RelationClasses Morphisms.

(* types with designated equality relation *)
Class EqCore (C : Type) :=
  equal : C → C → Prop.

Notation "x ≡ y" := (equal x y) (at level 70, no associativity).

Class Equiv (C : Type) {EC : EqCore C} :=
  equiv :: Equivalence equal.


(* indexed versions; the separate typeclasses are not satisfactory,
   but seem difficult to work around *)

Class EqCore1 {I : Type} (C : I → Type) :=
  eq1 i :: EqCore (C i).

Class Equiv1 {I} (C : I → Type) {EC : EqCore1 C} :=
  equiv1 i :: Equiv (C i).

Class EqCore2 {I J : Type} (C : I → J → Type) :=
  eq2 i :: EqCore1 (C i).

Class Equiv2 {I J} (C : I → J → Type) {EC : EqCore2 C} :=
  equiv2 i :: Equiv1 (C i).

Arguments eq1 {I C _} _ /.
Arguments eq2 {I J C _} _ _ /.
