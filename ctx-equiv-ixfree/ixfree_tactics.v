
From IxFree Require Import Lib Nat.
From Stdlib Require Import Utf8.

(* how to use refine to add a hypothesis *)
Example test_refine P Q : P → (P → Q) → Q.
Proof.
  intros Hp Hpq.
  refine ((fun Hz => _) (Hpq Hp)).
  assumption.
Abort.

Ltac ispec H H1 :=
  match type of H with
  | I_valid_at _ (I_prop (forall _, _)) =>
    ispecialize H H1
  | I_valid_at _ (I_prop (forall _, forall _, _)) =>
    ispecialize H H1
  | I_valid_at _ (I_arrow (I_prop _) _) =>
    refine ((fun H2 => _) (I_arrow_elim _ _ H (I_prop_intro _ H1)));
    clear H;
    rename H2 into H
  | I_valid_at _ (I_arrow _ _) =>
    refine ((fun H2 => _) (I_arrow_elim _ _ H H1));
    clear H;
    rename H2 into H
  (* | _ => idtac "no match" *)
  end.

Example test_ispec2 P R Q n :
  P → R → (n ⊨ (P → R → Q)ᵢ) → Q.
Proof.
  intros * Hp Hr H.
  ispec H Hp.
  specialize (H Hr).
Abort.

Example test_ispec1 P Q n :
  P → (n ⊨ (P → Q)ᵢ) → Q.
Proof.
  intros * Hp H.
  ispec H Hp.
  assumption.
Abort.

Example test_ispec3 P Q n :
  (n ⊨ P) → (n ⊨ P →ᵢ Q) → n ⊨ Q.
Proof.
  intros.
  Fail ispecialize H0 H.
  ispec H0 H.
  assumption.
Abort.

Example test_ispec3 P Q n :
  P → (n ⊨ (P)ᵢ →ᵢ Q) → n ⊨ Q.
Proof.
  intros.
  Fail ispecialize H0 H.
  ispec H0 H.
  assumption.
Abort.
