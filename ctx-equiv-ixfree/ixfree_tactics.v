
From IxFree Require Import Lib Nat.
From Stdlib Require Import Utf8.

(* how to use refine to add a hypothesis *)
Example test_refine P Q : P → (P → Q) → Q.
Proof.
  intros Hp Hpq.
  refine ((fun Hz => _) (Hpq Hp)).
  assumption.
Abort.

Ltac ispec_one H H1 k :=
  match type of H with
  | I_valid_at _ (I_forall _ _) =>
    ispecialize H H1; k
  | I_valid_at _ (I_prop (forall _, _)) =>
    ispecialize H H1; k
  | I_valid_at _ (I_prop (forall _, forall _, _)) =>
    ispecialize H H1; k
  | I_valid_at _ (I_arrow (I_prop _) _) =>
    let H2 := fresh "H" in
    refine ((fun H2 => _) (I_arrow_elim _ _ H (I_prop_intro _ H1)));
    clear H;
    rename H2 into H; k
  | I_valid_at _ (I_arrow _ _) =>
    let H2 := fresh "H" in
    refine ((fun H2 => _) (I_arrow_elim _ _ H H1));
    clear H;
    rename H2 into H; k
  (* | _ => idtac "no match" *)
  end.

Tactic Notation "ispec" hyp(H) uconstr(t1) :=
  ispec_one H t1 idtac.

Tactic Notation "ispec" hyp(H) uconstr(t1) uconstr(t2) :=
  ispec_one H t1 ltac:(ispec H t2).

Tactic Notation "ispec" hyp(H) uconstr(t1) uconstr(t2) uconstr(t3) :=
  ispec_one H t1 ltac:(ispec H t2 t3).

Tactic Notation "ispec" hyp(H) uconstr(t1) uconstr(t2) uconstr(t3) uconstr(t4) :=
  ispec_one H t1 ltac:(ispec H t2 t3 t4).

Tactic Notation "ispec" hyp(H) uconstr(t1) uconstr(t2) uconstr(t3) uconstr(t4) uconstr(t5) :=
  ispec_one H t1 ltac:(ispec H t2 t3 t4 t5).

Tactic Notation "ispec" hyp(H) uconstr(t1) uconstr(t2) uconstr(t3) uconstr(t4) uconstr(t5)uconstr(t6) :=
  ispec_one H t1 ltac:(ispec H t2 t3 t4 t5 t6).

Tactic Notation "ispec" hyp(H) uconstr(t1) uconstr(t2) uconstr(t3) uconstr(t4) uconstr(t5)uconstr(t6) uconstr(t7):=
  ispec_one H t1 ltac:(ispec H t2 t3 t4 t5 t6 t7).

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

Example test_ispec3 P R Q n :
  P → R → (n ⊨ (P)ᵢ →ᵢ (R)ᵢ →ᵢ Q) → n ⊨ Q.
Proof.
  intros Hp Hr **.
  Fail ispecialize H0 H.
  ispec H Hp Hr.
  assumption.
Abort.

Example test_ispec4 A (y:A) (P:A→Prop) Q n :
  P y → (n ⊨ ∀ᵢ x, (P x)ᵢ →ᵢ Q) → n ⊨ Q.
Proof.
  intros Hp H **.
  Fail ispecialize H0 H.
  ispec H y Hp.
  assumption.
Abort.
