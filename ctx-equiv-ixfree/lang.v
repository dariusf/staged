From stdpp Require Import relations.
(** Note: both stdpp and Binding define `fmap`, but with different
    signature. What we want in this file is Binding's `fmap`, thus
    we Require Import Binding after stdpp *)
From Stdlib Require Import Utf8.
From Binding Require Import Lib Auto.
Require Import Binding.Set.
From IxFree Require Import Lib Nat.
From CtxEquivIxFree Require Import ixfree_tactics.
From CtxEquivIxFree Require Import tactics.

Local Close Scope stdpp_scope.

Definition loc : Set := nat.

Inductive expr (V : Set) : Set :=
| e_val (v : val V)
| e_app (e1 e2 : expr V)

with val (V : Set) : Set :=
| v_var (x : V)
| v_lambda (e : expr (inc V)).

Arguments e_val {V} v.
Arguments e_app {V} e1 e2.
Arguments v_var {V} x.
Arguments v_lambda {V} e.

Definition e_var {V : Set} (x : V) : expr V :=
  e_val (v_var x).

Definition e_lambda {V} (e : expr (inc V)) : expr V :=
  e_val (v_lambda e).

#[global]
Instance SetPureCore_value : SetPureCore val :=
  { set_pure := @v_var }.

Fixpoint emap {A B} (f : A [→] B) (e : expr A) : expr B :=
  match e with
  | e_val v => e_val (vmap f v)
  | e_app e1 e2 => e_app (emap f e1) (emap f e2)
  end

with vmap {A B} (f : A [→] B) (v : val A) : val B :=
  match v with
  | v_var x => v_var (f x)
  | v_lambda e => v_lambda (emap (lift f) e)
  end.

#[global]
Instance FunctorCore_emap : FunctorCore expr := @emap.

#[global]
Instance FunctorCore_vmap : FunctorCore val := @vmap.

Fixpoint ebind {A B} (f : A [⇒] B) (e : expr A) : expr B :=
  match e with
  | e_val v => e_val (vbind f v)
  | e_app e1 e2 => e_app (ebind f e1) (ebind f e2)
  end

with vbind {A B} (f : A [⇒] B) (v : val A) : val B :=
  match v with
  | v_var x => f x
  | v_lambda e => v_lambda (ebind (lift f) e)
  end.

#[global]
Instance BindCore_ebind : BindCore expr := @ebind.

#[global]
Instance BindCore_vbind : BindCore val := @vbind.

Coercion e_val : val >-> expr.

(** Inside-out contexts, similar to a "reversed" list *)

(* Imagine the list is from left-to-right, with the following structure:
   ectx_hole ... ectx_app1 e ... ectx_app1 e ... ectx_app2 v.

   The actual structure is zig-zag, but let's linearize it so that we
   can implement and reason about this data-structure just like a list *)
Inductive ectx (V : Set) :=
  | ectx_hole
  | ectx_app1 (E : ectx V) (e : expr V)
  | ectx_app2 (v : val V) (E : ectx V).

Arguments ectx_hole {V}.
Arguments ectx_app1 {V} E e.
Arguments ectx_app2 {V} v E.

Fixpoint ectx_map {A B} (f : A [→] B) (E : ectx A) : ectx B :=
  match E with
  | ectx_hole => ectx_hole
  | ectx_app1 E' e => ectx_app1 (ectx_map f E') (fmap f e)
  | ectx_app2 v E' => ectx_app2 (fmap f v) (ectx_map f E')
  end.

#[global]
Instance FunctorCore_ectx_map : FunctorCore ectx := @ectx_map.

Fixpoint ectx_bind {A B} (f : A [⇒] B) (E : ectx A) : ectx B :=
  match E with
  | ectx_hole => ectx_hole
  | ectx_app1 E' e => ectx_app1 (ectx_bind f E') (bind f e)
  | ectx_app2 v E' => ectx_app2 (bind f v) (ectx_bind f E')
  end.

#[global]
Instance BindCore_ectx_bind : BindCore ectx := @ectx_bind.

(* similar to foldr of a "reversed" list (foldl of a normal list) *)
Fixpoint plug {V} (E : ectx V) (e : expr V) : expr V :=
  match E with
  | ectx_hole => e
  | ectx_app1 E' e' => plug E' (e_app e e')
  | ectx_app2 v E' => plug E' (e_app v e)
  end.

Lemma fold_unfold_plug_ectx_hole {V} (e : expr V) :
  plug ectx_hole e = e.
Proof. auto. Qed.

(* similar to "prepend" of a "reversed" list ("append" of a normal list) *)
Fixpoint ectx_comp {V} (E1 E2 : ectx V) : ectx V :=
  match E2 with
  | ectx_hole => E1
  | ectx_app1 E2' e => ectx_app1 (ectx_comp E1 E2') e
  | ectx_app2 v E2' => ectx_app2 v (ectx_comp E1 E2')
  end.

Lemma ectx_comp_assoc {V} (E1 E2 E3 : ectx V) :
  ectx_comp E1 (ectx_comp E2 E3) = ectx_comp (ectx_comp E1 E2) E3.
Proof.
  induction E3; simpl.
  - reflexivity.
  - rewrite -> IHE3. reflexivity.
  - rewrite -> IHE3. reflexivity.
Qed.

Lemma ectx_comp_correct {V} (E1 E2 : ectx V) (e : expr V) :
  plug (ectx_comp E1 E2) e = plug E1 (plug E2 e).
Proof.
  revert e.
  induction E2; intros e'.
  - simpl. reflexivity.
  - simpl. rewrite -> IHE2. reflexivity.
  - simpl. rewrite -> IHE2. reflexivity.
Qed.

(** Outside-in evaluation contexts, similar to a normal list *)

Inductive rctx (V : Set) :=
| rctx_hole
| rctx_app1 (R : rctx V) (e : expr V)
| rctx_app2 (v : val V) (R : rctx V).

Arguments rctx_hole {V}.
Arguments rctx_app1 {V} R e.
Arguments rctx_app2 {V} v R.

Fixpoint rctx_map {A B} (f : A [→] B) (R : rctx A) : rctx B :=
  match R with
  | rctx_hole => rctx_hole
  | rctx_app1 R' e => rctx_app1 (rctx_map f R') (fmap f e)
  | rctx_app2 v R' => rctx_app2 (fmap f v) (rctx_map f R')
  end.

#[global]
Instance FunctorCore_rctx_map : FunctorCore rctx := @rctx_map.

Fixpoint rctx_bind {A B} (f : A [⇒] B) (R : rctx A) : rctx B :=
  match R with
  | rctx_hole => rctx_hole
  | rctx_app1 R' e => rctx_app1 (rctx_bind f R') (bind f e)
  | rctx_app2 v R' => rctx_app2 (bind f v) (rctx_bind f R')
  end.

#[global]
Instance BindCore_rctx_bind : BindCore rctx := @rctx_bind.

(* similar to foldr of a normal list *)
Fixpoint rplug {V} (R : rctx V) (e : expr V) : expr V :=
  match R with
  | rctx_hole => e
  | rctx_app1 R' e' => e_app (rplug R' e) e'
  | rctx_app2 v R' => e_app v (rplug R' e)
  end.

(* similar to append of a normal list *)
Fixpoint rctx_comp {V} (R1 R2 : rctx V) : rctx V :=
  match R1 with
  | rctx_hole => R2
  | rctx_app1 R1' e => rctx_app1 (rctx_comp R1' R2) e
  | rctx_app2 v R1' => rctx_app2 v (rctx_comp R1' R2)
  end.

Lemma rctx_comp_assoc {V} (R1 R2 R3 : rctx V) :
  rctx_comp (rctx_comp R1 R2) R3 = rctx_comp R1 (rctx_comp R2 R3).
Proof.
  induction R1.
  - simpl. reflexivity.
  - simpl. rewrite -> IHR1. reflexivity.
  - simpl. rewrite -> IHR1. reflexivity.
Qed.

Lemma rctx_comp_correct {V} (R1 R2 : rctx V) (e : expr V) :
  rplug (rctx_comp R1 R2) e = rplug R1 (rplug R2 e).
Proof.
  induction R1.
  - simpl. reflexivity.
  - simpl. rewrite -> IHR1. reflexivity.
  - simpl. rewrite -> IHR1. reflexivity.
Qed.

(** Equivalence of ectx and rctx *)

(* similar to reverse_prepend : reverse R, and then prepend E to it *)
Fixpoint ectx_comp_rctx1 {V} (E : ectx V) (R : rctx V) : ectx V :=
  match R with
  | rctx_hole => E
  | rctx_app1 R' e => ectx_comp_rctx1 (ectx_app1 E e) R'
  | rctx_app2 v R' => ectx_comp_rctx1 (ectx_app2 v E) R'
  end.

(* similar to reverse *)
Definition rctx_to_ectx {V} : rctx V -> ectx V :=
  ectx_comp_rctx1 ectx_hole.

Lemma ectx_comp_rctx1_correct {V} (E : ectx V) (R : rctx V) (e : expr V) :
  plug (ectx_comp_rctx1 E R) e = plug E (rplug R e).
Proof.
  revert E.
  induction R; intros E.
  - simpl. reflexivity.
  - simpl. rewrite -> (IHR (ectx_app1 E _)). simpl. reflexivity.
  - simpl. rewrite -> (IHR (ectx_app2 _ E)). simpl. reflexivity.
Qed.

(* similar to reverse_append : reverse E, and then append to R *)
Fixpoint ectx_comp_rctx2 {V} (E : ectx V) (R : rctx V) : rctx V :=
  match E with
  | ectx_hole => R
  | ectx_app1 E e => ectx_comp_rctx2 E (rctx_app1 R e)
  | ectx_app2 v E => ectx_comp_rctx2 E (rctx_app2 v R)
  end.

Definition ectx_to_rctx {V} (E : ectx V) : rctx V :=
  ectx_comp_rctx2 E rctx_hole.

Lemma ectx_comp_rctx2_correct {V} (E : ectx V) (R : rctx V) (e : expr V) :
  rplug (ectx_comp_rctx2 E R) e = plug E (rplug R e).
Proof.
  revert R.
  induction E; intros R.
  - simpl. reflexivity.
  - simpl. rewrite -> (IHE (rctx_app1 R _)). simpl. reflexivity.
  - simpl. rewrite -> (IHE (rctx_app2 _ R)). simpl. reflexivity.
Qed.

Lemma ectx_comp_rctx1_reset {V} (E : ectx V) (R : rctx V) :
  ectx_comp_rctx1 E R = ectx_comp E (ectx_comp_rctx1 ectx_hole R).
Proof.
  revert E.
  induction R; intros E; simpl.
  - reflexivity.
  - rewrite -> (IHR (ectx_app1 E e)).
    rewrite -> (IHR (ectx_app1 ectx_hole e)).
    rewrite -> ectx_comp_assoc. simpl.
    reflexivity.
  - rewrite -> (IHR (ectx_app2 v E)).
    rewrite -> (IHR (ectx_app2 v ectx_hole)).
    rewrite -> ectx_comp_assoc. simpl.
    reflexivity.
Qed.

Lemma ectx_comp_rctx2_reset {V} (E : ectx V) (R : rctx V) :
  ectx_comp_rctx2 E R = rctx_comp (ectx_comp_rctx2 E rctx_hole) R.
Proof.
  revert R.
  induction E; intros R; simpl.
  - reflexivity.
  - rewrite -> (IHE (rctx_app1 R e)).
    rewrite -> (IHE (rctx_app1 rctx_hole e)).
    rewrite -> rctx_comp_assoc. simpl.
    reflexivity.
  - rewrite -> (IHE (rctx_app2 v R)).
    rewrite -> (IHE (rctx_app2 v rctx_hole)).
    rewrite -> rctx_comp_assoc. simpl.
    reflexivity.
Qed.

Lemma ectx_rctx_bijection_aux {V} (E : ectx V) (R : rctx V) :
  ectx_comp_rctx1 ectx_hole (ectx_comp_rctx2 E R) = ectx_comp_rctx1 E R.
Proof.
  revert R.
  induction E; intros R.
  - simpl. reflexivity.
  - simpl. rewrite -> (IHE (rctx_app1 R e)). simpl. reflexivity.
  - simpl. rewrite -> (IHE (rctx_app2 v R)). simpl. reflexivity.
Qed.

Lemma ectx_rctx_bijection {V} (E : ectx V) :
  rctx_to_ectx (ectx_to_rctx E) = E.
Proof.
  unfold rctx_to_ectx, ectx_to_rctx.
  exact (ectx_rctx_bijection_aux E rctx_hole).
Qed.

Lemma rctx_ectx_bijection_aux {V} (E : ectx V) (R : rctx V) :
  ectx_comp_rctx2 (ectx_comp_rctx1 E R) rctx_hole = ectx_comp_rctx2 E R.
Proof.
  revert E.
  induction R; intros E.
  - simpl. reflexivity.
  - simpl. rewrite -> (IHR (ectx_app1 E e)). simpl. reflexivity.
  - simpl. rewrite -> (IHR (ectx_app2 v E)). simpl. reflexivity.
Qed.

Lemma rctx_ectx_bijection {V} (R : rctx V) :
  ectx_to_rctx (rctx_to_ectx R) = R.
Proof.
  unfold ectx_to_rctx, rctx_to_ectx.
  exact (rctx_ectx_bijection_aux ectx_hole R).
Qed.

Lemma ectx_to_rctx_correct {V} (E : ectx V) (e : expr V) :
  rplug (ectx_to_rctx E) e = plug E e.
Proof.
  unfold ectx_to_rctx.
  exact (ectx_comp_rctx2_correct E rctx_hole e).
Qed.

Lemma plug_eq_val_inv {V} E e (v : val V) :
  plug E e = v →
  E = ectx_hole ∧ e = v.
Proof.
  revert e.
  induction E; intros e' H_eq; simpl in *.
  - auto.
  - specialize (IHE _ H_eq) as (_ & H_absurd). discriminate.
  - specialize (IHE _ H_eq) as (_ & H_absurd). discriminate.
Qed.

Lemma rplug_eq_val_inv {V} R e (v : val V) :
  rplug R e = v →
  R = rctx_hole ∧ e = v.
Proof.
  intros H_eq.
  destruct R; simpl in *.
  - auto.
  - discriminate.
  - discriminate.
Qed.

(** Properties of syntax *)

Lemma fmap_plug {A B} (f : A [→] B) (E : ectx A) (e : expr A) :
  fmap f (plug E e) = plug (fmap f E) (fmap f e).
Proof.
  revert e.
  induction E; intros e'.
  - term_simpl. reflexivity.
  - term_simpl. rewrite -> IHE. term_simpl. reflexivity.
  - term_simpl. rewrite -> IHE. term_simpl. reflexivity.
Qed.

Lemma bind_plug {A B} (f : A [⇒] B) (E : ectx A) (e : expr A) :
  bind f (plug E e) = plug (bind f E) (bind f e).
Proof.
  revert e.
  induction E; intros e'.
  - term_simpl. reflexivity.
  - term_simpl. rewrite -> IHE. term_simpl. reflexivity.
  - term_simpl. rewrite -> IHE. term_simpl. reflexivity.
Qed.

Lemma subst_plug {V} (E : ectx (inc V)) e v :
  subst (plug E e) v = plug (subst E v) (subst e v).
Proof.
  revert e.
  induction E as [| E IHE e' | v' E IHE]; intros e.
  - term_simpl. reflexivity.
  - term_simpl. rewrite -> IHE. term_simpl. reflexivity.
  - term_simpl. rewrite -> IHE. term_simpl. reflexivity.
Qed.

#[global] Hint Rewrite @fmap_plug : term_simpl.
#[global] Hint Rewrite @bind_plug : term_simpl.
#[global] Hint Rewrite @subst_plug : term_simpl.

#[global]
Instance SetPure_val : SetPure val.
Proof.
  split.
  - simpl. unfold SetPureCore_value. term_simpl. reflexivity.
  - simpl. unfold SetPureCore_value. term_simpl. reflexivity.
Qed.

(** Functor instances *)

Fixpoint emap_id {A} (f : A [→] A) (e : expr A) :
  equal f (arrow_id A) → fmap f e = e
with vmap_id {A} (f : A [→] A) (v : val A) :
  equal f (arrow_id A) → fmap f v = v.
Proof.
  - auto_map_id.
  - auto_map_id.
Qed.

Fixpoint emap_comp {A B C} (f : B [→] C) (g : A [→] B) (h : A [→] C) (e : expr A) :
  equal (arrow_comp f g) h → fmap f (fmap g e) = fmap h e
with vmap_comp {A B C} (f : B [→] C) (g : A [→] B) (h : A [→] C) (v : val A) :
  equal (arrow_comp f g) h → fmap f (fmap g v) = fmap h v.
Proof.
  - auto_map_comp.
  - auto_map_comp.
Qed.

#[global]
Instance Functor_expr : Functor expr.
Proof.
  constructor.
  - exact @emap_id.
  - exact @emap_comp.
Qed.

#[global]
Instance Functor_val : Functor val.
Proof.
  constructor.
  - exact @vmap_id.
  - exact @vmap_comp.
Qed.

Fixpoint ectx_map_id {A} (f : A [→] A) (E : ectx A) :
  equal f (arrow_id A) → fmap f E = E.
Proof. auto_map_id. Qed.

Fixpoint ectx_map_comp {A B C} (f : B [→] C) (g : A [→] B) (h : A [→] C) (E : ectx A) :
  equal (arrow_comp f g) h → fmap f (fmap g E) = fmap h E.
Proof. auto_map_comp. Qed.

#[global]
Instance Functor_ectx : Functor ectx.
Proof.
  constructor.
  - exact @ectx_map_id.
  - exact @ectx_map_comp.
Qed.

(** Bind-Map_Pure instances *)

Fixpoint ebind_map_pure {A B} (f : A [→] B) g (e : expr A) :
  equal (subst_of_arr f) g → fmap f e = bind g e
with vbind_map_pure {A B} (f : A [→] B) g (v : val A) :
  equal (subst_of_arr f) g → fmap f v = bind g v.
Proof.
  - auto_map_bind_pure.
  - auto_map_bind_pure.
Qed.

#[global]
Instance BindMapPure_expr : BindMapPure expr.
Proof. constructor. exact @ebind_map_pure. Qed.

#[global]
Instance BindMapPure_val : BindMapPure val.
Proof. constructor. exact @vbind_map_pure. Qed.

Fixpoint ectx_bind_map_pure {A B} (f : A [→] B) g (E : ectx A) :
  equal (subst_of_arr f) g → fmap f E = bind g E.
Proof. auto_map_bind_pure. Qed.

#[global]
Instance BindMapPure_ectx : BindMapPure ectx.
Proof. constructor. exact @ectx_bind_map_pure. Qed.

(** Bind-Map_Comm instances *)

Fixpoint ebind_map_comm {A B1 B2 C}
  (f1 : B1 [→] C) (f2 : A [→] B2) (g1 : A [⇒] B1) (g2 : B2 [⇒] C) (e : expr A) :
  equal (arrow_comp g2 (subst_of_arr f2)) (arrow_comp (subst_of_arr f1) g1) →
  bind g2 (fmap f2 e) = fmap f1 (bind g1 e)
with vbind_map_comm {A B1 B2 C}
  (f1 : B1 [→] C) (f2 : A [→] B2) (g1 : A [⇒] B1) (g2 : B2 [⇒] C) (v : val A) :
  equal (arrow_comp g2 (subst_of_arr f2)) (arrow_comp (subst_of_arr f1) g1) →
  bind g2 (fmap f2 v) = fmap f1 (bind g1 v).
Proof.
  - auto_map_bind_comm.
  - auto_map_bind_comm.
Qed.

#[global]
Instance BindMapComm_expr : BindMapComm expr.
Proof. constructor. exact @ebind_map_comm. Qed.

#[global]
Instance BindMapComm_val : BindMapComm val.
Proof. constructor. exact @vbind_map_comm. Qed.

Fixpoint ectx_bind_map_comm {A B1 B2 C}
  (f1 : B1 [→] C) (f2 : A [→] B2) (g1 : A [⇒] B1) (g2 : B2 [⇒] C) (E : ectx A) :
  equal (arrow_comp g2 (subst_of_arr f2)) (arrow_comp (subst_of_arr f1) g1) →
  bind g2 (fmap f2 E) = fmap f1 (bind g1 E).
Proof. auto_map_bind_comm. Qed.

#[global]
Instance BindMapComm_ectx : BindMapComm ectx.
Proof. constructor. exact @ectx_bind_map_comm. Qed.

(** Bind instances *)

Fixpoint ebind_id {A} (f : A [⇒] A) (e : expr A) :
  equal f (arrow_id A) → bind f e = e
with vbind_id {A} (f : A [⇒] A) (v : val A) :
  equal f (arrow_id A) → bind f v = v.
Proof.
  - auto_bind_id.
  - auto_bind_id.
Qed.

Fixpoint ebind_comp {A B C}
  (f : B [⇒] C) (g : A [⇒] B) (h : A [⇒] C) (e : expr A) :
  equal (arrow_comp f g) h → bind f (bind g e) = bind h e
with vbind_comp {A B C}
  (f : B [⇒] C) (g : A [⇒] B) (h : A [⇒] C) (v : val A) :
  equal (arrow_comp f g) h → bind f (bind g v) = bind h v.
Proof.
  - auto_bind_comp.
  - auto_bind_comp.
Qed.

#[global]
Instance Bind_expr : Bind expr.
Proof.
  constructor.
  - exact @ebind_id.
  - exact @ebind_comp.
Qed.

#[global]
Instance Bind_val : Bind val.
Proof.
  constructor.
  - exact @vbind_id.
  - exact @vbind_comp.
Qed.

Fixpoint ectx_bind_id {A} (f : A [⇒] A) (E : ectx A) :
  equal f (arrow_id A) → bind f E = E.
Proof. auto_bind_id. Qed.

Fixpoint ectx_bind_comp {A B C}
  (f : B [⇒] C) (g : A [⇒] B) (h : A [⇒] C) (E : ectx A) :
  equal (arrow_comp f g) h → bind f (bind g E) = bind h E.
Proof. auto_bind_comp. Qed.

#[global]
Instance Bind_ectx : Bind ectx.
Proof.
  constructor.
  - exact @ectx_bind_id.
  - exact @ectx_bind_comp.
Qed.

(** Reduction *)

Inductive base_step {V} : expr V → expr V → Prop :=
| Beta_step (e : expr (inc V)) (v : val V) :
  base_step (e_app (v_lambda e) v) (subst (Inc:=inc) e v).

Inductive contextual_step {V} : expr V → expr V → Prop :=
| Ectx_step E e1 e2 :
  base_step e1 e2 →
  contextual_step (plug E e1) (plug E e2).

Definition big_step {V} e (v : val V) :=
  rtc contextual_step e v.

Definition terminates {V} (e : expr V) :=
  ∃ v, big_step e v.

Lemma not_base_step_val {V} (v : val V) e : ¬ base_step v e.
Proof. inversion_clear 1. Qed.

Lemma not_contextual_step_val {V} (v : val V) e : ¬ contextual_step v e.
Proof.
  intros Hstep.
  inversion Hstep as [E' e1' e2' H_step' Hv He].
  apply plug_eq_val_inv in Hv as [_ ->].
  by eapply not_base_step_val.
Qed.

Lemma big_step_val {V} (v : val V) : big_step v v.
Proof. unfold big_step. done. Qed.

Lemma terminates_val {V} (v : val V) : terminates v.
Proof. unfold terminates. exists v. apply big_step_val. Qed.

Lemma contextual_step_comp {V} (E : ectx V) e1 e2 :
  contextual_step e1 e2 →
  contextual_step (plug E e1) (plug E e2).
Proof.
  intros H_step.
  inversion_clear H_step as [E' e1' e2' H_step'].
  rewrite <- ectx_comp_correct.
  rewrite <- ectx_comp_correct.
  constructor. exact H_step'.
Qed.

Lemma contextual_step_terminates {V} (e e' : expr V) :
  contextual_step e e' →
  terminates e' →
  terminates e.
Proof.
  unfold terminates, big_step.
  intros H_step [v H_steps].
  exists v. econstructor; eauto.
Qed.

Lemma base_step_is_deterministic {V} (e1 e2 e3 : expr V) :
  base_step e1 e2 →
  base_step e1 e3 →
  e2 = e3.
Proof.
  intros Hstep2 Hstep3.
  inversion Hstep2.
  inversion Hstep3.
  congruence.
Qed.

Inductive potential_redex {V} : expr V -> Prop :=
| pr_app (v1 v2 : val V) : potential_redex (e_app v1 v2).

Lemma not_potential_redex_val {V} (v : val V) : ¬ potential_redex v.
Proof. inversion_clear 1. Qed.

Lemma potential_redex_app_inv {V} e1 e2 :
  potential_redex (e_app e1 e2) →
  ∃ (v1 v2 : val V), e1 = v1 ∧ e2 = v2.
Proof. inversion_clear 1. eauto. Qed.

Lemma unique_rdecomposition {V} (R1 R2 : rctx V) e1 e2 :
  potential_redex e1 →
  potential_redex e2 →
  rplug R1 e1 = rplug R2 e2 →
  R1 = R2 ∧ e1 = e2.
Proof.
  intros He1 He2.
  revert R2.
  induction R1; intros R2 Heq.
  - destruct R2; simpl in *.
    + auto.
    + rewrite -> Heq in He1.
      apply potential_redex_app_inv in He1 as (v1 & v2 & Hv1 & Hv2).
      apply rplug_eq_val_inv in Hv1 as [_ ->].
      contradict (not_potential_redex_val _ He2).
    + rewrite -> Heq in He1.
      apply potential_redex_app_inv in He1 as (v1 & v2 & Hv1 & Hv2).
      apply rplug_eq_val_inv in Hv2 as [_ ->].
      contradict (not_potential_redex_val _ He2).
  - destruct R2; simpl in *.
    + rewrite <- Heq in He2.
      apply potential_redex_app_inv in He2 as (v1 & v2 & Hv1 & Hv2).
      apply rplug_eq_val_inv in Hv1 as [_ ->].
      contradict (not_potential_redex_val _ He1).
    + injection Heq as Heq1 Heq2.
      apply IHR1 in Heq1 as [Heq11 Heq12].
      split; congruence.
    + injection Heq as Heq1 Heq2.
      apply rplug_eq_val_inv in Heq1 as [_ ->].
      contradict (not_potential_redex_val _ He1).
  - destruct R2; simpl in *.
    + rewrite <- Heq in He2.
      apply potential_redex_app_inv in He2 as (v1 & v2 & Hv1 & Hv2).
      apply rplug_eq_val_inv in Hv2 as [_ ->].
      contradict (not_potential_redex_val _ He1).
    + injection Heq as Heq1 Heq2. symmetry in Heq1.
      apply rplug_eq_val_inv in Heq1 as [_ ->].
      contradict (not_potential_redex_val _ He2).
    + injection Heq as Heq1 Heq2.
      apply IHR1 in Heq2 as [Heq11 Heq12].
      split; congruence.
Qed.

Lemma unique_decomposition {V} (E1 E2 : ectx V) e1 e2 :
  potential_redex e1 →
  potential_redex e2 →
  plug E1 e1 = plug E2 e2 →
  E1 = E2 ∧ e1 = e2.
Proof.
  intros He1 He2 Heq.
  rewrite <- ectx_to_rctx_correct in Heq.
  rewrite <- ectx_to_rctx_correct in Heq.
  destruct (unique_rdecomposition _ _ _ _ He1 He2 Heq) as [Heq1 Heq2].
  split.
  - rewrite <- (ectx_rctx_bijection E1).
    rewrite <- (ectx_rctx_bijection E2).
    f_equal. exact Heq1.
  - exact Heq2.
Qed.

Lemma base_step_potential_redex {V} (e e' : expr V) :
  base_step e e' →
  potential_redex e.
Proof.
  inversion_clear 1.
  constructor.
Qed.

Lemma contextual_step_is_deterministic {V} (e1 e2 e3 : expr V) :
  contextual_step e1 e2 →
  contextual_step e1 e3 →
  e2 = e3.
Proof.
  intros Hstep2 Hstep3.
  inversion Hstep2 as [E2 e12 e2' Hstep2' He12 He2'].
  inversion Hstep3 as [E3 e13 e3' Hstep3' He13 He3'].
  assert (Hpr2 := base_step_potential_redex _ _ Hstep2').
  assert (Hpr3 := base_step_potential_redex _ _ Hstep3').
  destruct (unique_decomposition E2 E3 e12 e13 Hpr2 Hpr3) as [HE_eq He_eq].
  { congruence. }
  rewrite -> He_eq in Hstep2'.
  assert (He_eq' := base_step_is_deterministic e13 e2' e3' Hstep2' Hstep3').
  congruence.
Qed.

(** Relations for closed term *)

Definition expr_rel := expr ∅ ⇒ᵢ expr ∅ ⇒ᵢ IRel.
Definition val_rel := val ∅ ⇒ᵢ val ∅ ⇒ᵢ IRel.
Definition ectx_rel := ectx ∅ ⇒ᵢ ectx ∅ ⇒ᵢ IRel.

Definition L_rel_pre (L_rel : expr_rel) : expr_rel :=
  λ e1 e2,
    (∀ v1 : val ∅, e1 = v1 → terminates e2)ᵢ ∧ᵢ
    (∀ᵢ e1' : expr ∅, (contextual_step e1 e1')ᵢ →ᵢ ▷ L_rel e1' e2).

Definition L_rel_fix := I_fix L_rel_pre.
Definition L_rel := L_rel_pre L_rel_fix.

Definition O_rel : expr_rel :=
  λ e1 e2, L_rel e1 e2 ∧ᵢ L_rel e2 e1.

Definition K_rel_pre (V_rel : val_rel) : ectx_rel :=
  λ E1 E2,
    ∀ᵢ (v1 v2 : val ∅),
      V_rel v1 v2 →ᵢ
      O_rel (plug E1 v1) (plug E2 v2).

Definition R_rel_pre (V_rel : val_rel) : expr_rel :=
  λ e1 e2,
    ∀ᵢ E1 E2,
      ▷ K_rel_pre V_rel E1 E2 →ᵢ
      O_rel (plug E1 e1) (plug E2 e2).

Definition V_rel_pre (V_rel : val_rel) : val_rel :=
  λ v1 v2,
    ∀ᵢ u1 u2,
      ▷ V_rel u1 u2 →ᵢ
      R_rel_pre V_rel (e_app v1 u1) (e_app v2 u2).

Definition V_rel_fix := I_fix V_rel_pre.
Definition V_rel := V_rel_pre V_rel_fix.
Definition R_rel := R_rel_pre V_rel_fix.
Definition K_rel := K_rel_pre V_rel_fix.

Definition E_rel (e1 e2 : expr ∅) :=
  ∀ᵢ E1 E2,
    K_rel E1 E2 →ᵢ
    O_rel (plug E1 e1) (plug E2 e2).

(** Relations for open terms *)

Definition G_rel {V} (γ1 γ2 : V [⇒] ∅) : IProp :=
  ∀ᵢ x, V_rel (γ1 x) (γ2 x).

Definition E_rel_o {V} (e1 e2 : expr V) : IProp :=
  ∀ᵢ γ1 γ2, G_rel γ1 γ2 →ᵢ E_rel (bind γ1 e1) (bind γ2 e2).

Definition V_rel_o {V} (v1 v2 : val V) : IProp :=
  ∀ᵢ γ1 γ2, G_rel γ1 γ2 →ᵢ V_rel (bind γ1 v1) (bind γ2 v2).

Definition O_rel_o {V} (e1 e2 : expr V) : IProp :=
  ∀ᵢ γ1 γ2, G_rel γ1 γ2 →ᵢ O_rel (bind γ1 e1) (bind γ2 e2).

Definition K_rel_o {V} (E1 E2 : ectx V) : IProp :=
  ∀ᵢ γ1 γ2, G_rel γ1 γ2 →ᵢ K_rel (bind γ1 E1) (bind γ2 E2).

(** Contractiveness and unrolling fixpoint *)

Lemma L_rel_pre_contractive : contractive L_rel_pre.
Proof. intro n; iintros; unfold L_rel_pre; auto_contr. Qed.

Lemma L_rel_roll p1 p2 n :
  n ⊨ L_rel p1 p2 →
  n ⊨ L_rel_fix p1 p2.
Proof.
  intro H; iapply (I_fix_roll expr_rel); [| exact H].
  apply L_rel_pre_contractive.
Qed.

Lemma L_rel_unroll p1 p2 n :
  n ⊨ L_rel_fix p1 p2 →
  n ⊨ L_rel p1 p2.
Proof.
  intro H; iapply (I_fix_unroll expr_rel); [| exact H].
  apply L_rel_pre_contractive.
Qed.

Lemma V_rel_pre_contractive : contractive V_rel_pre.
Proof. intro n; iintros; unfold V_rel_pre, R_rel_pre, K_rel_pre; auto_contr. Qed.

Lemma V_rel_roll v1 v2 n :
  n ⊨ V_rel v1 v2 →
  n ⊨ V_rel_fix v1 v2.
Proof.
  intro H; iapply (I_fix_roll val_rel); [| exact H].
  apply V_rel_pre_contractive.
Qed.

Lemma V_rel_unroll v1 v2 n :
  n ⊨ V_rel_fix v1 v2 →
  n ⊨ V_rel v1 v2.
Proof.
  intro H; iapply (I_fix_unroll val_rel); [| exact H].
  apply V_rel_pre_contractive.
Qed.

(** Introduction and elimination lemmas *)

Lemma L_rel_intro (e1 e2 : expr ∅) n :
  (∀ v1 : val ∅, e1 = v1 → terminates e2) →
  n ⊨ (∀ᵢ e1' : expr ∅, (contextual_step e1 e1')ᵢ →ᵢ ▷ L_rel e1' e2) →
  n ⊨ L_rel e1 e2.
Proof.
  intros H_val H_expr.
  unfold L_rel, L_rel_pre.
  isplit.
  - iintro. exact H_val.
  - iintros e1' H_step.
    ispec H_expr e1' H_step.
    later_shift. apply L_rel_roll. exact H_expr.
Qed.

Lemma L_rel_elim (e1 e2 : expr ∅) n :
  n ⊨ L_rel e1 e2 →
  (∀ v1 : val ∅, e1 = v1 → terminates e2) ∧
  (n ⊨ ∀ᵢ e1' : expr ∅, (contextual_step e1 e1')ᵢ →ᵢ ▷ L_rel e1' e2).
Proof.
  intros He.
  unfold L_rel, L_rel_pre in He.
  idestruct He as He1 He2.
  split.
  - idestruct He1. exact He1.
  - iintros e1' H_step.
    ispec He2 e1' H_step.
    later_shift. apply L_rel_unroll. exact He2.
Qed.

Lemma O_rel_intro (e1 e2 : expr ∅) n :
  n ⊨ L_rel e1 e2 →
  n ⊨ L_rel e2 e1 →
  n ⊨ O_rel e1 e2.
Proof.
  intros He1 He2.
  unfold O_rel. isplit; assumption.
Qed.

Lemma O_rel_elim (e1 e2 : expr ∅) n :
  n ⊨ O_rel e1 e2 →
  (n ⊨ L_rel e1 e2) ∧
  (n ⊨ L_rel e2 e1).
Proof.
  unfold O_rel.
  intros He. idestruct He as He1 He2.
  split; assumption.
Qed.

Lemma O_rel_elim1 (e1 e2 : expr ∅) n :
  n ⊨ O_rel e1 e2 →
  n ⊨ L_rel e1 e2.
Proof. intros He. by apply O_rel_elim in He as []. Qed.

Lemma O_rel_elim2 (e1 e2 : expr ∅) n :
  n ⊨ O_rel e1 e2 →
  n ⊨ L_rel e2 e1.
Proof. intros He. by apply O_rel_elim in He as []. Qed.

Lemma V_rel_intro (v1 v2 : val ∅) n :
  (n ⊨ ∀ᵢ u1 u2,
         ▷ V_rel u1 u2 →ᵢ
         R_rel (e_app v1 u1) (e_app v2 u2)) →
  n ⊨ V_rel v1 v2.
Proof.
  intros Hv.
  unfold V_rel, V_rel_pre.
  iintros u1 u2 Hu.
  ispecialize Hv u1.
  ispecialize Hv u2.
  iapply Hv. later_shift.
  apply V_rel_unroll. exact Hu.
Qed.

Lemma V_rel_elim (v1 v2 : val ∅) n :
  n ⊨ V_rel v1 v2 →
  n ⊨ ∀ᵢ u1 u2,
        ▷ V_rel u1 u2 →ᵢ
        R_rel (e_app v1 u1) (e_app v2 u2).
Proof.
  intros Hv.
  unfold V_rel, V_rel_pre in Hv.
  iintros u1 u2 Hu.
  ispecialize Hv u1.
  ispecialize Hv u2.
  iapply Hv. later_shift.
  apply V_rel_roll. exact Hu.
Qed.

Lemma V_rel_elimR (v1 v2 u1 u2 : val ∅) n :
  n ⊨ V_rel v1 v2 →
  n ⊨ ▷ V_rel u1 u2 →
  n ⊨ R_rel (e_app v1 u1) (e_app v2 u2).
Proof.
  intros Hv Hu.
  apply V_rel_elim in Hv.
  iapply Hv. exact Hu.
Qed.

Lemma K_rel_intro (E1 E2 : ectx ∅) n :
  n ⊨ (∀ᵢ v1 v2, V_rel v1 v2 →ᵢ O_rel (plug E1 v1) (plug E2 v2)) →
  n ⊨ K_rel E1 E2.
Proof.
  intros HE.
  unfold K_rel, K_rel_pre.
  iintros v1 v2 Hv.
  iapply HE. apply V_rel_unroll. exact Hv.
Qed.

Lemma K_rel_elim (E1 E2 : ectx ∅) n :
  n ⊨ K_rel E1 E2 →
  n ⊨ ∀ᵢ v1 v2, V_rel v1 v2 →ᵢ O_rel (plug E1 v1) (plug E2 v2).
Proof.
  unfold K_rel, K_rel_pre.
  intros HE.
  iintros v1 v2 Hv.
  iapply HE. apply V_rel_roll. exact Hv.
Qed.

Lemma K_rel_elimO E1 E2 v1 v2 n :
  n ⊨ K_rel E1 E2 →
  n ⊨ V_rel v1 v2 →
  n ⊨ O_rel (plug E1 v1) (plug E2 v2).
Proof.
  intros HE Hv.
  apply K_rel_elim in HE.
  iapply HE. exact Hv.
Qed.

Lemma R_rel_intro (e1 e2 : expr ∅) n :
  n ⊨ (∀ᵢ E1 E2, ▷ K_rel E1 E2 →ᵢ O_rel (plug E1 e1) (plug E2 e2)) ->
  n ⊨ R_rel e1 e2.
Proof. auto. Qed.

Lemma R_rel_elim (e1 e2 : expr ∅) n :
  n ⊨ R_rel e1 e2 →
  n ⊨ (∀ᵢ E1 E2, ▷ K_rel E1 E2 →ᵢ O_rel (plug E1 e1) (plug E2 e2)).
Proof. auto. Qed.

Lemma R_rel_elimO (e1 e2 : expr ∅) E1 E2 n :
  n ⊨ R_rel e1 e2 →
  n ⊨ ▷ K_rel E1 E2 →
  n ⊨ O_rel (plug E1 e1) (plug E2 e2).
Proof.
  intros He HE.
  apply R_rel_elim in He.
  iapply He. exact HE.
Qed.

Lemma E_rel_intro (e1 e2 : expr ∅) n :
  (n ⊨ ∀ᵢ E1 E2, K_rel E1 E2 →ᵢ O_rel (plug E1 e1) (plug E2 e2)) →
  n ⊨ E_rel e1 e2.
Proof. auto. Qed.

Lemma E_rel_elim (e1 e2 : expr ∅) n :
  n ⊨ E_rel e1 e2 →
  n ⊨ ∀ᵢ E1 E2, K_rel E1 E2 →ᵢ O_rel (plug E1 e1) (plug E2 e2).
Proof. auto. Qed.

(** Bind lemma *)
Lemma E_rel_elimO e1 e2 E1 E2 n :
  n ⊨ E_rel e1 e2 →
  n ⊨ K_rel E1 E2 →
  n ⊨ O_rel (plug E1 e1) (plug E2 e2).
Proof.
  intros He HE.
  apply E_rel_elim in He.
  iapply He. exact HE.
Qed.

Lemma G_rel_intro {V} (γ1 γ2 : V [⇒] ∅) n :
  (n ⊨ ∀ᵢ x, V_rel (γ1 x) (γ2 x)) →
  n ⊨ G_rel γ1 γ2.
Proof. auto. Qed.

Lemma G_rel_elim {V} (γ1 γ2 : V [⇒] ∅) n :
  n ⊨ G_rel γ1 γ2 →
  n ⊨ ∀ᵢ x, V_rel (γ1 x) (γ2 x).
Proof. auto. Qed.

Lemma G_rel_elimV {V} (γ1 γ2 : V [⇒] ∅) (x : V) n :
  n ⊨ G_rel γ1 γ2 →
  n ⊨ V_rel (γ1 x) (γ2 x).
Proof.
  intros Hγ.
  apply G_rel_elim in Hγ.
  iapply Hγ.
Qed.

Lemma E_rel_o_intro {V} (e1 e2 : expr V) n :
  (n ⊨ ∀ᵢ γ1 γ2, G_rel γ1 γ2 →ᵢ E_rel (bind γ1 e1) (bind γ2 e2)) →
  n ⊨ E_rel_o e1 e2.
Proof. auto. Qed.

Lemma E_rel_o_elim {V} (e1 e2 : expr V) n :
  n ⊨ E_rel_o e1 e2 →
  n ⊨ ∀ᵢ γ1 γ2, G_rel γ1 γ2 →ᵢ E_rel (bind γ1 e1) (bind γ2 e2).
Proof. auto. Qed.

Lemma E_rel_o_elimE {V} (e1 e2 : expr V) (γ1 γ2 : V [⇒] ∅) n :
  n ⊨ E_rel_o e1 e2 →
  n ⊨ G_rel γ1 γ2 →
  n ⊨ E_rel (bind γ1 e1) (bind γ2 e2).
Proof.
  intros He Hγ.
  apply E_rel_o_elim in He.
  iapply He. exact Hγ.
Qed.

Lemma V_rel_o_intro {V} (v1 v2 : val V) n :
  (n ⊨ ∀ᵢ γ1 γ2, G_rel γ1 γ2 →ᵢ V_rel (bind γ1 v1) (bind γ2 v2)) →
  n ⊨ V_rel_o v1 v2.
Proof. auto. Qed.

Lemma V_rel_o_elim {V} (v1 v2 : val V) n :
  n ⊨ V_rel_o v1 v2 →
  n ⊨ ∀ᵢ γ1 γ2, G_rel γ1 γ2 →ᵢ V_rel (bind γ1 v1) (bind γ2 v2).
Proof. auto. Qed.

Lemma V_rel_o_elimV {V} (v1 v2 : val V) (γ1 γ2 : V [⇒] ∅) n :
  n ⊨ V_rel_o v1 v2 →
  n ⊨ G_rel γ1 γ2 →
  n ⊨ V_rel (bind γ1 v1) (bind γ2 v2).
Proof.
  intros Hv Hγ.
  apply V_rel_o_elim in Hv.
  iapply Hv. exact Hγ.
Qed.

Lemma O_rel_o_intro {V} (e1 e2 : expr V) n :
  (n ⊨ ∀ᵢ γ1 γ2, G_rel γ1 γ2 →ᵢ O_rel (bind γ1 e1) (bind γ2 e2)) →
  n ⊨ O_rel_o e1 e2.
Proof. auto. Qed.

Lemma O_rel_o_elim {V} (e1 e2 : expr V) n :
  n ⊨ O_rel_o e1 e2 →
  n ⊨ ∀ᵢ γ1 γ2, G_rel γ1 γ2 →ᵢ O_rel (bind γ1 e1) (bind γ2 e2).
Proof. auto. Qed.

Lemma O_rel_o_elimO {V} (e1 e2 : expr V) (γ1 γ2 : V [⇒] ∅) n :
  n ⊨ O_rel_o e1 e2 →
  n ⊨ G_rel γ1 γ2 →
  n ⊨ O_rel (bind γ1 e1) (bind γ2 e2).
Proof.
  intros He Hγ.
  apply O_rel_o_elim in He.
  iapply He. exact Hγ.
Qed.

Lemma K_rel_o_intro {V} (E1 E2 : ectx V) n :
  n ⊨ (∀ᵢ γ1 γ2, G_rel γ1 γ2 →ᵢ K_rel (bind γ1 E1) (bind γ2 E2)) →
  n ⊨ K_rel_o E1 E2.
Proof. auto. Qed.

Lemma K_rel_o_elim {V} (E1 E2 : ectx V) n :
  n ⊨ K_rel_o E1 E2 →
  n ⊨ ∀ᵢ γ1 γ2, G_rel γ1 γ2 →ᵢ K_rel (bind γ1 E1) (bind γ2 E2).
Proof. auto. Qed.

Lemma K_rel_o_elimK {V} (E1 E2 : ectx V) (γ1 γ2 : V [⇒] ∅) n :
  n ⊨ K_rel_o E1 E2 →
  n ⊨ G_rel γ1 γ2 →
  n ⊨ K_rel (bind γ1 E1) (bind γ2 E2).
Proof.
  intros HE Hγ.
  apply K_rel_o_elim in HE.
  iapply HE. exact Hγ.
Qed.

(** Compatibility lemmas *)

Lemma compat_val_closed v1 v2 n :
  n ⊨ V_rel v1 v2 →
  n ⊨ E_rel v1 v2.
Proof.
  intros Hv.
  apply E_rel_intro. iintros E1 E2 HE.
  apply K_rel_elimO; assumption.
Qed.

(* aka val inclusion *)
Lemma compat_val {V} (v1 v2 : val V) n :
  n ⊨ V_rel_o v1 v2 →
  n ⊨ E_rel_o v1 v2.
Proof.
  intros Hv.
  apply V_rel_o_elim in Hv.
  apply E_rel_o_intro. iintros γ1 γ2 Hγ. term_simpl.
  apply compat_val_closed. iapply Hv. exact Hγ.
Qed.

Lemma compat_app_closed_val (v1 v2 u1 u2 : val ∅) n :
  n ⊨ V_rel v1 v2 →
  n ⊨ V_rel u1 u2 →
  n ⊨ E_rel (e_app v1 u1) (e_app v2 u2).
Proof.
  intros Hv Hu.
  apply E_rel_intro.
  iintros E1 E2 HE.
  apply R_rel_elimO.
  - apply V_rel_elimR. exact Hv.
    later_shift. exact Hu.
  - later_shift. exact HE.
Qed.

Lemma compat_app_closed e1 e2 e1' e2' n :
  n ⊨ E_rel e1 e2 →
  n ⊨ E_rel e1' e2' →
  n ⊨ E_rel (e_app e1 e1') (e_app e2 e2').
Proof.
  intros He He'.
  apply E_rel_intro. iintros E1 E2 HE. term_simpl.
  (* The functions e1/e2 are evaluated first, so we "zap" them down using He.
     To use He, we have to give two contexts s.t. if we can prove them to be
     related, plugging e1/e2 into them will be in O_rel. We give ectx_app1
     because the plugging will give us exactly the goal we need. *)
  apply E_rel_elim in He.
  ispecialize He (ectx_app1 E1 e1').
  ispecialize He (ectx_app1 E2 e2').
  iapply He. clear He.
  (* Now, we need to show that the two app contexts are related. *)
  apply K_rel_intro. iintros v1 v2 Hv. simpl.
  (* Given that they are plugged with two related values, we now have to prove
     that the result is in O_rel. We use He' for a similar purpose. We give
     ectx_app2 because plugging e1'/e2' into it will match the goal. *)
  apply E_rel_elim in He'.
  ispecialize He' (ectx_app2 v1 E1).
  ispecialize He' (ectx_app2 v2 E2).
  iapply He'. clear He'.
  (* Now we have to prove the ectx_app2 are related. *)
  apply K_rel_intro. iintros v1' v2' Hv'. simpl.
  (* Now, we have that the two values and contexts are related.
     We "zap" (app v1 v1') and (app v2 v2') down using E_rel_elimO *)
  apply E_rel_elimO.
  apply compat_app_closed_val; [exact Hv | exact Hv'].
  (* Finally, we are left with just E1 and E2.
     They are related according to our hypothesis *)
  exact HE.
Qed.

Lemma compat_app {V} (e1 e2 e1' e2' : expr V) n :
  n ⊨ E_rel_o e1 e2 →
  n ⊨ E_rel_o e1' e2' →
  n ⊨ E_rel_o (e_app e1 e1') (e_app e2 e2').
Proof.
  intros He He'.
  apply E_rel_o_intro. iintros γ1 γ2 Hγ. term_simpl.
  (* Use the lemma about closed app *)
  apply compat_app_closed.
  - apply E_rel_o_elimE. exact He. exact Hγ.
  - apply E_rel_o_elimE. exact He'. exact Hγ.
Qed.

Lemma compat_var {V : Set} (x : V) n :
  n ⊨ V_rel_o (v_var x) (v_var x).
Proof.
  apply V_rel_o_intro.
  iintros γ1 γ2 Hγ. term_simpl.
  apply G_rel_elimV. exact Hγ.
Qed.

Lemma L_rel_red_l (e1 e1' e2 : expr ∅) n :
  contextual_step e1 e1' →
  n ⊨ ▷ L_rel e1' e2 →
  n ⊨ L_rel e1 e2.
Proof.
  intros H_step He.
  apply L_rel_intro.
  - intros v1 H_eq.
    rewrite -> H_eq in H_step.
    contradict (not_contextual_step_val _ _ H_step).
  - iintros e1'' H_step'.
    idestruct H_step'.
    rewrite -> (contextual_step_is_deterministic _ _ _ H_step' H_step).
    exact He.
Qed.

Lemma L_rel_red_r (e1 e2 e2' : expr ∅) n :
  contextual_step e2 e2' →
  n ⊨ L_rel e1 e2' →
  n ⊨ L_rel e1 e2.
Proof.
  intros H_step He1.
  irevert e1 He1.
  loeb_induction IH.
  iintros e1 He.
  apply L_rel_elim in He as [He1 He2].
  apply L_rel_intro.
  - intros v1 H_eq.
    specialize (He1 v1 H_eq).
    eapply contextual_step_terminates; eauto.
  - iintros e1' H_step'.
    ispec He2 e1' H_step'.
    later_shift. iapply IH. exact He2.
Qed.

Lemma O_rel_red_l (e1 e1' e2 : expr ∅) n :
  contextual_step e1 e1' →
  n ⊨ O_rel e1' e2 →
  n ⊨ O_rel e1 e2.
Proof.
  intros H_step He.
  apply O_rel_elim in He as [He1 He2].
  apply O_rel_intro.
  - eapply L_rel_red_l.
    + exact H_step.
    + later_shift. exact He1.
  - eapply L_rel_red_r.
    + exact H_step.
    + exact He2.
Qed.

(* symmetric to the proof of O_rel_red_l *)
Lemma O_rel_red_r (e1 e2 e2' : expr ∅) n :
  contextual_step e2 e2' →
  n ⊨ O_rel e1 e2' →
  n ⊨ O_rel e1 e2.
Proof.
  intros H_step He.
  apply O_rel_elim in He as [He1 He2].
  apply O_rel_intro.
  - eapply L_rel_red_r.
    + exact H_step.
    + exact He1.
  - eapply L_rel_red_l.
    + exact H_step.
    + later_shift. exact He2.
Qed.

Lemma O_rel_red_both (e1 e1' e2 e2' : expr ∅) n :
  contextual_step e1 e1' →
  contextual_step e2 e2' →
  n ⊨ ▷ O_rel e1' e2' →
  n ⊨ O_rel e1 e2.
Proof.
  intros H_step1 H_step2 He.
  unfold O_rel in He.
  apply I_conj_later_down in He.
  idestruct He as He1 He2.
  apply O_rel_intro.
  - eapply L_rel_red_l. { exact H_step1. }
    later_shift.
    eapply L_rel_red_r. { exact H_step2. }
    exact He1.
  - eapply L_rel_red_r. { exact H_step1. }
    eapply L_rel_red_l. { exact H_step2. }
    later_shift. exact He2.
Qed.

(* Observation: later_shift is significant in O_rel_red_both,
   but is not significant in O_rel_red_l and O_rel_red_r. We
   hypothesize that O_rel_red_l and O_rel_red_r are stronger
   property:
   - O_rel_red_both → O_rel_red_l ∧ O_rel_red_r
   - But not: O_rel_red_l ∧ O_rel_red_r → O_rel_red_both *)

Lemma R_rel_red_both (e1 e1' e2 e2' : expr ∅) n :
  contextual_step e1 e1' →
  contextual_step e2 e2' →
  n ⊨ ▷ E_rel e1' e2' →
  n ⊨ R_rel e1 e2.
Proof.
  intros H_step1 H_step2 He.
  apply R_rel_intro.
  iintros E1 E2 HE.
  eapply O_rel_red_both.
  - by apply contextual_step_comp.
  - by apply contextual_step_comp.
  - later_shift. by apply E_rel_elimO.
Qed.

Lemma compat_lambda {V} (e1 e2 : expr (inc V)) n :
  n ⊨ E_rel_o e1 e2 →
  n ⊨ V_rel_o (v_lambda e1) (v_lambda e2).
Proof.
  intros He.
  apply V_rel_o_intro. iintros γ1 γ2 Hγ.
  apply V_rel_intro. iintros u1 u2 Hu. term_simpl.
  eapply R_rel_red_both.
  { eapply (Ectx_step ectx_hole). constructor. }
  { eapply (Ectx_step ectx_hole). constructor. }
  later_shift. simpl. unfold subst.
  rewrite -> bind_bind_comp'.
  rewrite -> bind_bind_comp'.
  apply E_rel_o_elim in He. iapply He.
  apply G_rel_intro.
  iintros x. destruct x as [| x'].
  - term_simpl. exact Hu.
  - term_simpl. apply G_rel_elimV. exact Hγ.
Qed.

Lemma fundamental_property_e {V} (e : expr V) n :
  n ⊨ E_rel_o e e
with fundamental_property_v {V} (v : val V) n :
  n ⊨ V_rel_o v v.
Proof.
  { induction e.
    - apply compat_val. apply fundamental_property_v.
    - apply compat_app; auto. }
  { induction v.
    - apply compat_var.
    - apply compat_lambda.
      apply fundamental_property_e. }
Qed.

(** General program contexts *)
Inductive ctx : Set → Type :=
| ctx_hole : ctx ∅
| ctx_fmap {A B} : (A [→] B) → ctx B → ctx A
| ctx_bind {A B} : (A [⇒] B) → ctx B → ctx A
| ctx_lam {V} : ctx V → ctx (inc V)
| ctx_app1 {V} : ctx V → expr V → ctx V
| ctx_app2 {V} : expr V → ctx V → ctx V.

(** Inside-out plugging, always result in a closed expression *)
Fixpoint ciplug {V} (C : ctx V) : expr V → expr ∅ :=
  match C with
  | ctx_hole => λ e, e
  | ctx_fmap f C => λ e, ciplug C (fmap f e)
  | ctx_bind f C => λ e, ciplug C (bind f e)
  | ctx_lam C => λ e, ciplug C (v_lambda e)
  | ctx_app1 C e2 => λ e, ciplug C (e_app e e2)
  | ctx_app2 e1 C => λ e, ciplug C (e_app e1 e)
  end.

Inductive ctxr : Set → Set → Type :=
| ctxr_hole {A} : ctxr A A
| ctxr_fmap {A B C} : (B [→] C) → ctxr A B → ctxr A C
| ctxr_bind {A B C} : (B [⇒] C) → ctxr A B → ctxr A C
| ctxr_lam {A B} : ctxr A (inc B) → ctxr A B
| ctxr_app1 {A B} : ctxr A B → expr B → ctxr A B
| ctxr_app2 {A B} : expr B → ctxr A B → ctxr A B.

(* Outside-in plugging *)
Fixpoint crplug {A B} (C : ctxr A B) : expr A → expr B :=
  match C with
  | ctxr_hole => λ e, e
  | ctxr_fmap f C => λ e, fmap f (crplug C e)
  | ctxr_bind f C => λ e, bind f (crplug C e)
  | ctxr_lam C => λ e, v_lambda (crplug C e)
  | ctxr_app1 C e2 => λ e, e_app (crplug C e) e2
  | ctxr_app2 e1 C => λ e, e_app e1 (crplug C e)
  end.

Fixpoint ctxr_comp {A B C} (C1 : ctxr B C) : ctxr A B → ctxr A C :=
  match C1 with
  | ctxr_hole => λ C2, C2
  | ctxr_fmap f C1 => λ C2, ctxr_fmap f (ctxr_comp C1 C2)
  | ctxr_bind f C1 => λ C2, ctxr_bind f (ctxr_comp C1 C2)
  | ctxr_lam C1 => λ C2, ctxr_lam (ctxr_comp C1 C2)
  | ctxr_app1 C1 e2 => λ C2, ctxr_app1 (ctxr_comp C1 C2) e2
  | ctxr_app2 e1 C1 => λ C2, ctxr_app2 e1 (ctxr_comp C1 C2)
  end.

Lemma ctxr_comp_correct {A B C} (C1 : ctxr B C) (C2 : ctxr A B) (e : expr A) :
  crplug (ctxr_comp C1 C2) e = crplug C1 (crplug C2 e).
Proof.
  induction C1.
  - simpl. reflexivity.
  - simpl. rewrite -> IHC1. reflexivity.
  - simpl. rewrite -> IHC1. reflexivity.
  - simpl. rewrite -> IHC1. reflexivity.
  - simpl. rewrite -> IHC1. reflexivity.
  - simpl. rewrite -> IHC1. reflexivity.
Qed.

(** Observational approximation for complete programs *)
Definition obs_approx (e1 e2 : expr ∅) : Prop :=
  terminates e1 → terminates e2.

(** Observational equivalence for complete programs *)
Definition obs_equiv (e1 e2 : expr ∅) : Prop :=
  terminates e1 ↔ terminates e2.

Infix "≼obs" := obs_approx (at level 80, right associativity, only printing).
Infix "≡obs" := obs_equiv (at level 80, right associativity, only printing).

#[global]
Instance Reflexive_obs_approx : Reflexive obs_approx.
Proof. unfold Reflexive, obs_approx. auto. Qed.

#[global]
Instance Transitive_obs_approx : Transitive obs_approx.
Proof. unfold Transitive, obs_approx. auto. Qed.

#[global]
Instance Reflexive_obs_equiv : Reflexive obs_equiv.
Proof. unfold Reflexive, obs_equiv. auto. Qed.

#[global]
Instance Symmetric_obs_equiv : Symmetric obs_equiv.
Proof. unfold Symmetric, obs_equiv. auto. Qed.

#[global]
Instance Transitive_obs_equiv : Transitive obs_equiv.
Proof. unfold Transitive, obs_equiv. intuition auto. Qed.

(** Contextual approximation, where the context closes off Γ *)
Definition ctx_approx {V} (e1 e2 : expr V) : Prop :=
  ∀ C, obs_approx (crplug C e1) (crplug C e2).

(** Contextual equivalence *)
Definition ctx_equiv {V} (e1 e2 : expr V) : Prop :=
  ∀ C, obs_equiv (crplug C e1) (crplug C e2).

Infix "≼ctx" := ctx_approx (at level 80, right associativity, only printing).
Infix "≡ctx" := ctx_equiv (at level 80, right associativity, only printing).

#[global]
Instance Reflexive_ctx_approx {V} : Reflexive (@ctx_approx V).
Proof. unfold Reflexive, ctx_approx. reflexivity. Qed.

#[global]
Instance Transitive_ctx_approx {V} : Transitive (@ctx_approx V).
Proof. unfold Transitive, ctx_approx. etransitivity; eauto. Qed.

#[global]
Instance Reflexive_ctx_equiv {V} : Reflexive (@ctx_equiv V).
Proof. unfold Reflexive, ctx_equiv. reflexivity. Qed.

#[global]
Instance Symmetric_ctx_equiv {V} : Symmetric (@ctx_equiv V).
Proof. unfold Symmetric, ctx_equiv. symmetry. auto. Qed.

#[global]
Instance Transitive_ctx_equiv {V} : Transitive (@ctx_equiv V).
Proof. unfold Transitive, ctx_equiv. etransitivity; eauto. Qed.

Lemma obs_equiv_intro_approx (e1 e2 : expr ∅) :
  obs_approx e1 e2 →
  obs_approx e2 e1 →
  obs_equiv e1 e2.
Proof.
  unfold obs_approx, obs_equiv. done.
Qed.

Lemma obs_equiv_elim_approx (e1 e2 : expr ∅) :
  obs_equiv e1 e2 →
  obs_approx e1 e2 ∧
  obs_approx e2 e1.
Proof.
  unfold obs_approx, obs_equiv. done.
Qed.

Lemma ctx_equiv_intro_approx {V} (e1 e2 : expr V) :
  ctx_approx e1 e2 →
  ctx_approx e2 e1 →
  ctx_equiv e1 e2.
Proof.
  unfold ctx_approx, ctx_equiv.
  intros He1 He2 C.
  apply obs_equiv_intro_approx; auto.
Qed.

Lemma ctx_equiv_elim_approx {V} (e1 e2 : expr V) :
  ctx_equiv e1 e2 →
  ctx_approx e1 e2 ∧
  ctx_approx e2 e1.
Proof.
  unfold ctx_equiv, ctx_approx.
  intros He. split.
  - intros C. specialize (He C). by apply obs_equiv_elim_approx in He as [].
  - intros C. specialize (He C). by apply obs_equiv_elim_approx in He as [].
Qed.

Definition ciu_approx {V} (e1 e2 : expr V) : Prop :=
  ∀ E γ, obs_approx (plug E (bind γ e1)) (plug E (bind γ e2)).

Definition ciu_equiv {V} (e1 e2 : expr V) : Prop :=
  ∀ E γ, obs_equiv (plug E (bind γ e1)) (plug E (bind γ e2)).

Lemma ciu_equiv_intro_approx {V} (e1 e2 : expr V) :
  ciu_approx e1 e2 →
  ciu_approx e2 e1 →
  ciu_equiv e1 e2.
Proof.
  unfold ciu_approx, ciu_equiv.
  intros He1 He2 E γ.
  apply obs_equiv_intro_approx; auto.
Qed.

Lemma ciu_equiv_elim_approx {V} (e1 e2 : expr V) :
  ciu_equiv e1 e2 →
  ciu_approx e1 e2 ∧
  ciu_approx e2 e1.
Proof.
  unfold ciu_approx, ciu_equiv.
  intros He. split.
  - intros E γ. specialize (He E γ). by apply obs_equiv_elim_approx in He as [].
  - intros E γ. specialize (He E γ). by apply obs_equiv_elim_approx in He as [].
Qed.

Definition n_big_step {V} n (e : expr V) (v : val V) := nsteps contextual_step n e v.
Definition b_big_step {V} n (e : expr V) (v : val V) := bsteps contextual_step n e v.
Definition n_terminates {V} n (e : expr V) := ∃ v, n_big_step n e v.
Definition b_terminates {V} n (e : expr V) := ∃ v, b_big_step n e v.

Lemma big_step_iff_n_big_step {V} (e : expr V) (v : val V) :
  big_step e v ↔ ∃ n, n_big_step n e v.
Proof.
  unfold big_step, n_big_step.
  apply rtc_nsteps.
Qed.

Lemma big_step_iff_b_big_step {V} (e : expr V) (v : val V) :
  big_step e v ↔ ∃ n, b_big_step n e v.
Proof.
  unfold big_step, b_big_step.
  apply rtc_bsteps.
Qed.

Lemma terminates_iff_n_terminates {V} (e : expr V) :
  terminates e ↔ ∃ n, n_terminates n e.
Proof.
  unfold terminates, n_terminates.
  split.
  - intros [v H_big_step].
    apply big_step_iff_n_big_step in H_big_step as [n H_n_big_step].
    eauto.
  - intros (n & v & H_n_big_step).
    exists v. apply big_step_iff_n_big_step.
    exists n. exact H_n_big_step.
Qed.

Lemma terminates_iff_b_terminates {V} (e : expr V) :
  terminates e ↔ ∃ n, b_terminates n e.
Proof.
  unfold terminates, b_terminates.
  split.
  - intros [v H_big_step].
    apply big_step_iff_b_big_step in H_big_step as [n H_b_big_step].
    eauto.
  - intros (n & v & H_b_big_step).
    exists v. apply big_step_iff_b_big_step.
    exists n. exact H_b_big_step.
Qed.

Lemma n_big_step_O_inv {V} e (v : val V) :
  n_big_step O e v → e = v.
Proof.
  unfold n_big_step.
  inversion_clear 1. auto.
Qed.

Lemma b_big_step_O_inv {V} e (v : val V) :
  b_big_step O e v → e = v.
Proof.
  unfold b_big_step.
  inversion_clear 1. auto.
Qed.

Lemma n_big_step_S_inv {V} n e (v : val V) :
  n_big_step (S n) e v →
  ∃ e', contextual_step e e' ∧ n_big_step n e' v.
Proof.
  unfold n_big_step.
  inversion_clear 1. eauto.
Qed.

Lemma n_terminates_O_inv {V} (e : expr V) :
  n_terminates O e →
  ∃ (v : val V), e = v.
Proof.
  unfold n_terminates.
  intros [v H_n_big_step].
  apply n_big_step_O_inv in H_n_big_step. eauto.
Qed.

Lemma n_terminates_S_inv {V} n (e : expr V) :
  n_terminates (S n) e →
  ∃ e', contextual_step e e' ∧ n_terminates n e'.
Proof.
  unfold n_terminates.
  intros [v H_n_big_step].
  apply n_big_step_S_inv in H_n_big_step as (e' & H_step & H_n_big_step).
  eauto.
Qed.

Lemma b_terminates_O_inv {V} (e : expr V) :
  b_terminates O e →
  ∃ (v : val V), e = v.
Proof.
  unfold b_terminates.
  intros [v H_b_big_step].
  apply b_big_step_O_inv in H_b_big_step. eauto.
Qed.

Lemma L_rel_adequacy_n (e1 e2 : expr ∅) n :
  {| nw_index := n |} ⊨ L_rel e1 e2 →
  n_terminates n e1 →
  terminates e2.
Proof.
  revert e1.
  induction n as [| n' IHn']; intros e1 He He1.
  - apply n_terminates_O_inv in He1 as [v He1].
    apply L_rel_elim in He as [He _]. eauto.
  - apply n_terminates_S_inv in He1 as (e' & H_step & He1).
    apply (IHn' e'); [| exact He1].
    apply I_world_lift_later.
    apply L_rel_elim in He as [_ He]. iapply He.
    iintro. exact H_step.
Qed.

Lemma L_rel_adequacy (e1 e2 : expr ∅) :
  (∀ n, n ⊨ L_rel e1 e2) →
  terminates e1 →
  terminates e2.
Proof.
  intros He He1.
  apply terminates_iff_n_terminates in He1 as (n & He1).
  eapply L_rel_adequacy_n.
  - apply He.
  - exact He1.
Qed.

Theorem O_rel_adequacy e1 e2 :
  (∀ n, n ⊨ O_rel e1 e2) → obs_equiv e1 e2.
Proof.
  intros He. split.
  - apply L_rel_adequacy.
    intros n. specialize (He n).
    by apply O_rel_elim in He as [].
  - apply L_rel_adequacy.
    intros n. specialize (He n).
    by apply O_rel_elim in He as [].
Qed.

Lemma L_rel_val (v1 v2 : val ∅) n :
  n ⊨ L_rel v1 v2.
Proof.
  apply L_rel_intro.
  - intros _ _. apply terminates_val.
  - iintros e1 He. idestruct He.
    by apply not_contextual_step_val in He.
Qed.

Lemma O_rel_val (v1 v2 : val ∅) n :
  n ⊨ O_rel v1 v2.
Proof.
  apply O_rel_intro.
  - apply L_rel_val.
  - apply L_rel_val.
Qed.

Lemma compat_empty_subst n :
  n ⊨ G_rel (arrow_id ∅) (arrow_id ∅).
Proof.
  apply G_rel_intro.
  iintros x. destruct x.
Qed.

Lemma fundamental_property_v_closed (v : val ∅) n :
  n ⊨ V_rel v v.
Proof.
  rewrite <- (bind_pure' v).
  apply V_rel_o_elimV.
  - apply fundamental_property_v.
  - apply compat_empty_subst.
Qed.

Lemma fundamental_property_e_closed (e : expr ∅) n :
  n ⊨ E_rel e e.
Proof.
  rewrite <- (bind_pure' e).
  apply E_rel_o_elimE.
  - apply fundamental_property_e.
  - apply compat_empty_subst.
Qed.

Lemma fundamental_property_g {V} (γ : V [⇒] ∅) n :
  n ⊨ G_rel γ γ.
Proof.
  apply G_rel_intro.
  iintros x. apply fundamental_property_v_closed.
Qed.

Lemma compat_ectx_hole_closed n :
  n ⊨ K_rel ectx_hole ectx_hole.
Proof.
  apply K_rel_intro.
  iintros v1 v2 Hv. simpl.
  apply O_rel_val.
Qed.

Lemma compat_ectx_hole {V} n :
  n ⊨ @K_rel_o V ectx_hole ectx_hole.
Proof.
  apply K_rel_o_intro.
  iintros γ1 γ2 _. term_simpl.
  apply compat_ectx_hole_closed.
Qed.

Lemma compat_ectx_app1_closed E1 E2 e1 e2 n :
  n ⊨ K_rel E1 E2 →
  n ⊨ E_rel e1 e2 →
  n ⊨ K_rel (ectx_app1 E1 e1) (ectx_app1 E2 e2).
Proof.
  intros HE He.
  apply K_rel_intro.
  iintros v1 v2 Hv. simpl.
  apply E_rel_elimO.
  - apply compat_app_closed.
    apply compat_val_closed. exact Hv.
    exact He.
  - exact HE.
Qed.

Lemma compat_ectx_app1 {V} (E1 E2 : ectx V) e1 e2 n :
  n ⊨ K_rel_o E1 E2 →
  n ⊨ E_rel_o e1 e2 →
  n ⊨ K_rel_o (ectx_app1 E1 e1) (ectx_app1 E2 e2).
Proof.
  intros HE He.
  apply K_rel_o_intro.
  iintros γ1 γ2 Hγ. term_simpl.
  apply compat_ectx_app1_closed.
  - apply K_rel_o_elimK. exact HE. exact Hγ.
  - apply E_rel_o_elimE. exact He. exact Hγ.
Qed.

Lemma compat_ectx_app2_closed v1 v2 E1 E2 n :
  n ⊨ V_rel v1 v2 →
  n ⊨ K_rel E1 E2 →
  n ⊨ K_rel (ectx_app2 v1 E1) (ectx_app2 v2 E2).
Proof.
  intros Hv HE.
  apply K_rel_intro.
  iintros u1 u2 Hu. simpl.
  apply E_rel_elimO.
  - apply compat_app_closed_val. exact Hv. exact Hu.
  - exact HE.
Qed.

Lemma compat_ectx_app2 {V} (v1 v2 : val V) E1 E2 n :
  n ⊨ V_rel_o v1 v2 →
  n ⊨ K_rel_o E1 E2 →
  n ⊨ K_rel_o (ectx_app2 v1 E1) (ectx_app2 v2 E2).
Proof.
  intros Hv HE.
  apply K_rel_o_intro.
  iintros γ1 γ2 Hγ. term_simpl.
  apply compat_ectx_app2_closed.
  - apply V_rel_o_elimV. exact Hv. exact Hγ.
  - apply K_rel_o_elimK. exact HE. exact Hγ.
Qed.

Lemma fundamental_property_k {V} (E : ectx V) n :
  n ⊨ K_rel_o E E.
Proof.
  induction E.
  - apply compat_ectx_hole.
  - apply compat_ectx_app1.
    + exact IHE.
    + apply fundamental_property_e.
  - apply compat_ectx_app2.
    + apply fundamental_property_v.
    + exact IHE.
Qed.

Lemma fundamental_property_k_closed E n :
  n ⊨ K_rel E E.
Proof.
  rewrite <- (bind_pure' E).
  apply K_rel_o_elimK.
  - apply fundamental_property_k.
  - apply compat_empty_subst.
Qed.

Lemma compat_expr_o_closed (e1 e2 : expr ∅) n :
  n ⊨ E_rel e1 e2 →
  n ⊨ O_rel e1 e2.
Proof.
  intros He.
  rewrite <- (fold_unfold_plug_ectx_hole e1).
  rewrite <- (fold_unfold_plug_ectx_hole e2).
  apply E_rel_elimO.
  - exact He.
  - apply compat_ectx_hole_closed.
Qed.

Lemma compat_expr_o {V} (e1 e2 : expr V) n :
  n ⊨ E_rel_o e1 e2 →
  n ⊨ O_rel_o e1 e2.
Proof.
  intros He.
  apply O_rel_o_intro. iintros γ1 γ2 Hγ.
  apply compat_expr_o_closed.
  apply E_rel_o_elimE; assumption.
Qed.

Lemma compat_fmap {A B} (f : A [→] B) e1 e2 n :
  n ⊨ E_rel_o e1 e2 →
  n ⊨ E_rel_o (fmap f e1) (fmap f e2).
Proof.
  intros He.
  apply E_rel_o_intro. iintros γ1 γ2 Hγ.
  rewrite -> (map_to_bind f).
  rewrite -> (map_to_bind f).
  rewrite -> bind_bind_comp'.
  rewrite -> bind_bind_comp'.
  apply E_rel_o_elimE. exact He.
  apply G_rel_intro. iintros x. term_simpl.
  apply G_rel_elimV. exact Hγ.
Qed.

Lemma compat_bind {A B} (f : A [⇒] B) e1 e2 n :
  n ⊨ E_rel_o e1 e2 →
  n ⊨ E_rel_o (bind f e1) (bind f e2).
Proof.
  intros He.
  apply E_rel_o_intro. iintros γ1 γ2 Hγ.
  rewrite -> bind_bind_comp'.
  rewrite -> bind_bind_comp'.
  apply E_rel_o_elimE. exact He.
  apply G_rel_intro. iintros x. term_simpl.
  apply V_rel_o_elimV.
  - apply fundamental_property_v.
  - exact Hγ.
Qed.

Lemma precongruence {A B} (e1 e2 : expr A) (C : ctxr A B) n :
  n ⊨ E_rel_o e1 e2 →
  n ⊨ E_rel_o (crplug C e1) (crplug C e2).
Proof.
  intros He.
  induction C; simpl.
  - exact He.
  - apply compat_fmap. apply IHC. exact He.
  - apply compat_bind. apply IHC. exact He.
  - apply compat_val.
    apply compat_lambda.
    apply IHC. exact He.
  - apply compat_app.
    + apply IHC. exact He.
    + apply fundamental_property_e.
  - apply compat_app.
    + apply fundamental_property_e.
    + apply IHC. exact He.
Qed.

Theorem E_rel_o_soundness' {V} (e1 e2 : expr V) :
  (∀ n, n ⊨ E_rel_o e1 e2) →
  ciu_equiv e1 e2.
Proof.
  unfold ciu_equiv.
  intros He E γ.
  apply O_rel_adequacy. intros n.
  apply E_rel_elimO.
  - specialize (He n).
    apply E_rel_o_elimE.
    + exact He.
    + apply fundamental_property_g.
  - apply fundamental_property_k_closed.
Qed.

Lemma L_rel_obs_approx_trans e1 e2 e3 n :
  n ⊨ L_rel e1 e2 →
  obs_approx e2 e3 →
  n ⊨ L_rel e1 e3.
Proof.
  unfold obs_approx.
  intros He1 He2.
  irevert e1 He1. loeb_induction IH.
  iintros e1 He1.
  apply L_rel_elim in He1 as [He1_val He1_step].
  apply L_rel_intro.
  - intros v Hv. exact (He2 (He1_val v Hv)).
  - iintros e1' H_step.
    ispec He1_step e1' H_step.
    later_shift. iapply IH.
    exact He1_step.
Qed.

Lemma O_rel_obs_equiv_trans e1 e2 e3 n :
  n ⊨ O_rel e1 e2 →
  obs_equiv e2 e3 →
  n ⊨ O_rel e1 e3.
Proof.
  intros He1 He2.
  apply O_rel_elim in He1 as [He1_l He1_r].
  apply obs_equiv_elim_approx in He2 as [He2_l He2_r].
  apply O_rel_intro.
  - by eapply L_rel_obs_approx_trans.
  - (* This direction is impossible to prove:
       If e3 terminates in n steps, we need to prove that e1 MUST
       terminate. Using He2_r, we can conclude that e2 terminates
       in some m steps. However, if m > n, then He1_r does not imply
       that e1 terminates. *)
Abort.

Theorem L_rel_completeness (e1 e2 : expr ∅) n :
  obs_approx e1 e2 →
  n ⊨ L_rel e1 e2.
Proof.
  intros He. irevert e1 He.
  loeb_induction IH.
  iintros e1 He.
  apply L_rel_intro.
  - intros v ->. apply He. apply terminates_val.
  - iintros e1' H_step. idestruct H_step.
    later_shift.
    assert (He1' : obs_approx e1' e2).
    { unfold obs_approx in *.
      intros He1'. apply He.
      by eapply contextual_step_terminates. }
    ispec IH e1' He1'.
    exact IH.
Qed.

Theorem O_rel_completeness (e1 e2 : expr ∅) n :
  obs_equiv e1 e2 →
  n ⊨ O_rel e1 e2.
Proof.
  intros He.
  apply obs_equiv_elim_approx in He as [He1 He2].
  apply O_rel_intro.
  - by apply L_rel_completeness.
  - by apply L_rel_completeness.
Qed.

Theorem E_rel_o_completeness' {V} (e1 e2 : expr V) n :
  ciu_equiv e1 e2 →
  n ⊨ E_rel_o e1 e2.
Proof.
  intros He.
  apply ciu_equiv_elim_approx in He as [He1 He2].
  unfold ciu_approx in *.
  apply E_rel_o_intro. iintros γ1 γ2 Hγ.
  apply E_rel_intro. iintros E1 E2 HE.
  apply O_rel_intro.
  - assert (He1' : n ⊨ L_rel (plug E1 (bind γ1 e1)) (plug E2 (bind γ2 e1))).
    { apply O_rel_elim1.
      apply E_rel_elimO.
      apply E_rel_o_elimE.
      apply fundamental_property_e.
      exact Hγ. exact HE. }
    specialize (He1 E2 γ2).
    exact (L_rel_obs_approx_trans _ _ _ _ He1' He1).
  - assert (He2' : n ⊨ L_rel (plug E2 (bind γ2 e2)) (plug E1 (bind γ1 e2))).
    { apply O_rel_elim2.
      apply E_rel_elimO.
      apply E_rel_o_elimE.
      apply fundamental_property_e.
      exact Hγ. exact HE. }
    specialize (He2 E1 γ1).
    exact (L_rel_obs_approx_trans _ _ _ _ He2' He2).
Qed.

Theorem E_rel_o_soundness {V} (e1 e2 : expr V) :
  (∀ n, n ⊨ E_rel_o e1 e2) →
  ctx_equiv e1 e2.
Proof.
  unfold ctx_equiv.
  intros He C.
  apply O_rel_adequacy. intros n.
  specialize (He n).
  apply (precongruence _ _ C) in He.
  apply compat_expr_o in He.
  rewrite <- (bind_pure' (crplug C e1)).
  rewrite <- (bind_pure' (crplug C e2)).
  apply O_rel_o_elimO. exact He.
  apply G_rel_intro. iintros x. destruct x.
Qed.

Fixpoint rctx_to_ctxr {V} (R : rctx V) : ctxr V V :=
  match R with
  | rctx_hole => ctxr_hole
  | rctx_app1 R e => ctxr_app1 (rctx_to_ctxr R) e
  | rctx_app2 v R => ctxr_app2 v (rctx_to_ctxr R)
  end.

Definition ectx_to_ctxr {V} (E : ectx V) : ctxr V V :=
  rctx_to_ctxr (ectx_to_rctx E).

Lemma rctx_to_ctxr_correct {V} (R : rctx V) (e : expr V) :
  crplug (rctx_to_ctxr R) e = rplug R e.
Proof.
  induction R.
  - simpl. reflexivity.
  - simpl. rewrite -> IHR. reflexivity.
  - simpl. rewrite -> IHR. reflexivity.
Qed.

Lemma ectx_to_ctxr_correct {V} (E : ectx V) (e : expr V) :
  crplug (ectx_to_ctxr E) e = plug E e.
Proof.
  unfold ectx_to_ctxr.
  rewrite -> rctx_to_ctxr_correct.
  rewrite -> ectx_to_rctx_correct.
  reflexivity.
Qed.

Theorem ciu_equiv_completeness {V} (e1 e2 : expr V) :
  ctx_equiv e1 e2 →
  ciu_equiv e1 e2.
Proof.
  unfold ctx_equiv, ciu_equiv.
  intros He E γ.
  specialize (He (ctxr_comp (ectx_to_ctxr E) (ctxr_bind γ ctxr_hole))).
  rewrite ->! ctxr_comp_correct in He. simpl in He.
  rewrite ->! ectx_to_ctxr_correct in He.
  exact He.
Qed.

Theorem E_rel_o_completeness {V} (e1 e2 : expr V) n :
  ctx_equiv e1 e2 →
  n ⊨ E_rel_o e1 e2.
Proof.
  intros He.
  apply E_rel_o_completeness'.
  apply ciu_equiv_completeness.
  exact He.
Qed.

(** Auxilliary definitions and lemmas *)

Definition e_rel_o {V} (e1 e2 : expr V) : Prop :=
  ∀ n, n ⊨ E_rel_o e1 e2.

Instance Reflexive_e_rel_o {V} : Reflexive (@e_rel_o V).
Proof. unfold Reflexive, e_rel_o. by apply fundamental_property_e. Qed.

Instance Symmetric_e_rel_o {V} : Symmetric (@e_rel_o V).
Proof.
  unfold Symmetric, e_rel_o.
  intros x y Hxy n.
  apply E_rel_o_completeness. symmetry.
  by apply E_rel_o_soundness.
Qed.

Instance Transitive_e_rel_o {V} : Transitive (@e_rel_o V).
Proof.
  unfold Transitive, e_rel_o.
  intros x y z Hxy Hyz n.
  apply E_rel_o_completeness. etransitivity.
  by apply E_rel_o_soundness.
  by apply E_rel_o_soundness.
Qed.

Lemma terminates_contextual_step {V} (e e' : expr V) :
  terminates e →
  contextual_step e e' →
  terminates e'.
Proof.
  unfold terminates, big_step.
  intros [v H_steps] H_step.
  exists v.
  apply rtc_inv in H_steps.
  destruct H_steps as [-> | (e'' & H_step' & H_steps')].
  - by apply not_contextual_step_val in H_step.
  - rewrite -> (contextual_step_is_deterministic _ _ _ H_step H_step').
    exact H_steps'.
Qed.

Lemma ciu_approx_beta {V} (e : expr (inc V)) (v : val V) :
  ciu_approx (e_app (v_lambda e) v) (subst e v).
Proof.
  unfold ciu_approx, obs_approx.
  intros E γ H_terminates. term_simpl in H_terminates. term_simpl.
  eapply terminates_contextual_step. exact H_terminates.
  constructor. constructor.
Qed.

Lemma ciu_approx_unbeta {V} (e : expr (inc V)) (v : val V) :
  ciu_approx (subst e v) (e_app (v_lambda e) v).
Proof.
  unfold ciu_approx, obs_approx.
  intros E γ H_terminates. term_simpl in H_terminates. term_simpl.
  eapply contextual_step_terminates; [| exact H_terminates].
  constructor. constructor.
Qed.

Lemma ciu_equiv_beta {V} (e : expr (inc V)) (v : val V) :
  ciu_equiv (e_app (v_lambda e) v) (subst e v).
Proof.
  apply ciu_equiv_intro_approx.
  - apply ciu_approx_beta.
  - apply ciu_approx_unbeta.
Qed.

Lemma e_rel_o_beta {V} (e : expr (inc V)) (v : val V) :
  e_rel_o (e_app (v_lambda e) v) (subst e v).
Proof.
  unfold e_rel_o. intros n.
  apply E_rel_o_completeness'.
  apply ciu_equiv_beta.
Qed.
