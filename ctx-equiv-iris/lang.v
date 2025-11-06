
From CtxEquivIris Require Import persistent_pred.

From iris.prelude Require Import options.
From iris.base_logic Require Import invariants bi algebra.
From iris.heap_lang Require Import proofmode.
From stdpp Require Export binders.
From stdpp Require Export gmap.

Definition loc : Set := nat.

Inductive expr :=
  (* | ret (v : val) *)
  (* | eint (z : Z) *)
  (* | eunit *)
  | evalue (v:val)

  (* | ens (H : hprop) *)
  (* | ensp (P : prop) *)
  (* | var (x : binder) *)
  | var (x : string)
  (* | bind (e1 : expr) (x : binder) (e2 : expr) *)
  | app (e1 e2: expr)
  (* | abs (x : binder) (e : expr) *)
  | eplus (e1 e2: expr)

with val :=
  | vint (z : Z)
  | vlambda (x : binder) (e: expr)
  (* | vbool (b : bool) *)
  (* | vloc (l : loc) *)
  | vunit.

Definition to_val (e : expr) : option val :=
  match e with
  | evalue v => Some v
  (* | abs x e => Some (vlambda x e) *)
  | _ => None
  end.

Inductive hprop :=
  | emp
  | pts (l : loc) (v : val)
  | sep (h1 h2: hprop).

Fixpoint subst_val (x : string) (es : expr) (v : val)  : val :=
  match v with
  | vunit => vunit
  | vint n => vint n
  | vlambda y e =>
      vlambda y $ if decide (BNamed x = y) then e else
        (subst x es e)
  end

with subst (x : string) (es : expr) (e : expr)  : expr :=
  match e with
  (* | eunit => eunit *)
  | evalue v => evalue (subst_val x es v)
  (* The function [decide] can be used to decide propositions.
    [decide P] is of type {P} + {¬ P}.
    It can only be applied to propositions for which, by type class inference,
    it can be determined that the proposition is decidable. *)
  | var y => if decide (x = y) then es else var y
  (* | abs y e =>
      abs y $ if decide (BNamed x = y) then e else subst x es e *)
  | app e1 e2 => app (subst x es e1) (subst x es e2)
  | eplus e1 e2 => eplus (subst x es e1) (subst x es e2)
  end.

Definition subst' (mx : binder) (es : expr) : expr → expr :=
  match mx with BNamed x => subst x es | BAnon => id end.

Definition is_val (e : expr) : Prop :=
  match e with
  | evalue v => True
  (* | abs x e => True *)
  | _ => False
  end.

(* Definition of_val (v : val) : expr :=
  match v with
  | vunit => eunit
  | vint n => eint n
  | vlambda x e => abs x e
  end. *)

Notation of_val := evalue.
Coercion evalue : val >-> expr.

Inductive base_step : expr → expr → Prop :=
  | BetaS x e1 e2 e' :
     is_val e2 →
     e' = subst' x e2 e1 →
     base_step (app (evalue (vlambda x e1)) e2) e'
  (* | PlusS e1 e2 (n1 n2 n3 : Z):
     e1 = (eint n1) →
     e2 = (eint n2) →
     (n1 + n2)%Z = n3 →
     base_step (Plus e1 e2) (eint n3) *)
  .

Inductive evctx :=
  | HoleCtx
  | AppLCtx (K: evctx) (v2 : val)
  | AppRCtx (e1 : expr) (K: evctx)
  | PlusLCtx (K: evctx) (v2 : val)
  | PlusRCtx (e1 : expr) (K: evctx)
  .

Fixpoint fill (K : evctx) (e : expr) : expr :=
  match K with
  | HoleCtx => e
  | AppLCtx K v2 => app (fill K e) (of_val v2)
  | AppRCtx e1 K => app e1 (fill K e)
  | PlusLCtx K v2 => eplus (fill K e) (of_val v2)
  | PlusRCtx e1 K => eplus e1 (fill K e)
  end.

(* filling a context with another context *)
Fixpoint comp_ectx (Ko Ki: evctx) :=
  match Ko with
  | HoleCtx => Ki
  | AppLCtx K v2 => AppLCtx (comp_ectx K Ki) v2
  | AppRCtx e1 K => AppRCtx e1 (comp_ectx K Ki)
  | PlusLCtx K v2 => PlusLCtx (comp_ectx K Ki) v2
  | PlusRCtx e1 K => PlusRCtx e1 (comp_ectx K Ki)
  end.

Inductive contextual_step (e1 : expr) (e2 : expr) : Prop :=
  Ectx_step K e1' e2' :
    e1 = fill K e1' →
    e2 = fill K e2' →
    base_step e1' e2' →
    contextual_step e1 e2.

Definition contextual_reducible (e : expr) :=
  ∃ e', contextual_step e e'.

Definition bigstep e1 (v:val) :=
  ∃ e2, rtc contextual_step e1 e2 /\ ∃ v, Some v = to_val e2.

Definition terminates e := ∃ v, bigstep e v.

Definition equiterminate e1 e2 := terminates e1 <-> terminates e2.

Definition obs_eqv e1 e2 :=
  ∀ C, equiterminate (fill C e1) (fill C e2).

Infix "≈" := equiterminate (at level 80, right associativity, only printing).
Infix "≡obs" := obs_eqv (at level 80, right associativity, only printing).

Section logrel.
Context `{heapGS Σ}.

(* Definition valO := leibnizO val.
Definition exprO := leibnizO expr.
Definition evctxO := leibnizO evctx. *)

(* Definition val_rel := valO -n> valO -n> iProp Σ.
Definition ctx_rel := evctxO -n> evctxO -n> iProp Σ.
Definition expr_rel := exprO -n> exprO -n> iProp Σ. *)

Definition val_rel := persistent_pred (val * val) (iPropI Σ).
Definition expr_rel := persistent_pred (expr * expr) (iPropI Σ).
Definition evctx_rel := persistent_pred (evctx * evctx) (iPropI Σ).

Definition val_relO := persistent_predO (val * val) (iPropI Σ).
Definition expr_relO := persistent_predO (expr * expr) (iPropI Σ).
Definition evctx_relO := persistent_predO (evctx * evctx) (iPropI Σ).

Definition mk_val_rel (pred : (val * val) → iProp Σ) {Pers : ∀ v, Persistent (pred v)} : val_rel :=
  @PersPred _ _ pred Pers.
Global Instance val_rel_pers (τ : val_relO) : ∀ v, Persistent (τ v) := _.

Definition mk_expr_rel (pred : (expr * expr) → iProp Σ) {Pers : ∀ e, Persistent (pred e)} : expr_rel :=
  @PersPred _ _ pred Pers.
Global Instance expr_rel_pers (τ : expr_relO) : ∀ e, Persistent (τ e) := _.

Definition mk_evctx_rel (pred : (evctx * evctx) → iProp Σ) {Pers : ∀ E, Persistent (pred E)} : evctx_rel :=
  @PersPred _ _ pred Pers.
Global Instance evctx_rel_pers (τ : evctx_relO) : ∀ E, Persistent (τ E) := _.

(* Print val_rel_pers. *)

(* Locate "<pers>". *)

(* Definition semtypeO := persistent_predO val (iPropI Σ). *)

Definition L_rel_pre (L_rel:expr_rel) : expr_rel :=
  mk_expr_rel (fun e =>
    ((∀ v1, ⌜to_val e.1 = Some v1⌝ → ⌜terminates e.2⌝) ∗
      (∀ e1', ⌜base_step e.1 e1'⌝ → ▷ L_rel (e1', e.2)))%I).

Definition O_rel_pre (L_rel:expr_rel) : expr_rel :=
  mk_expr_rel (fun e =>
    (L_rel (e.1, e.2) ∧ L_rel (e.2, e.1))%I).

Instance L_rel_pre_contractive :
  Contractive L_rel_pre.
Proof. solve_contractive. Qed.

Definition L_rel : expr_rel := fixpoint L_rel_pre.
Definition O_rel : expr_rel := O_rel_pre L_rel.

Definition K_rel_pre (V_rel:val_rel) : evctx_rel :=
  mk_evctx_rel (fun E =>
    ∀ (v1 v2:val), □ (V_rel (v1, v2) →
      O_rel (fill E.1 (of_val v1), fill E.2 (of_val v2))))%I.

Definition R_rel_pre (V_rel:val_rel) : expr_rel :=
  mk_expr_rel (fun e =>
    ∀ (E1 E2:evctx), □ (▷ K_rel_pre V_rel (E1, E2) →
      O_rel (fill E1 e.1, fill E2 e.2)))%I.

Definition V_rel_pre (V_rel:val_rel) : val_rel :=
  mk_val_rel (fun v =>
    ∀ (v1' v2':val), □ (▷ V_rel (v1', v2') →
      R_rel_pre V_rel (app (of_val v.1) (of_val v1'),
        app (of_val v.2) (of_val v2'))))%I.

Instance V_rel_pre_contractive :
  Contractive (V_rel_pre).
Proof. solve_contractive. Qed.

Definition V_rel : val_rel := fixpoint V_rel_pre.
Definition K_rel : evctx_rel := K_rel_pre V_rel.
Definition R_rel : expr_rel := R_rel_pre V_rel.

Definition E_rel : expr_rel :=
  mk_expr_rel (fun e =>
    ∀ (E1 E2:evctx), □ (K_rel (E1, E2) →
      O_rel (fill E1 e.1, fill E2 e.2)))%I.

(* open relations *)

Definition sub := gmap string val.

Fixpoint subst_map_val (xs : sub) (v : val) : val :=
  match v with
  | vunit => vunit
  | vint n => vint n
  | vlambda x e => vlambda x (subst_map (binder_delete x xs) e)
  end

with subst_map (xs : sub) (e : expr) : expr :=
  match e with
  | evalue v => evalue (subst_map_val xs v)
  (* | eunit => eunit *)
  | var y => match xs !! y with Some es => of_val es | _ =>  var y end
  | app e1 e2 => app (subst_map xs e1) (subst_map xs e2)
  (* | abs x e => abs x (subst_map (binder_delete x xs) e) *)
  | eplus e1 e2 => eplus (subst_map xs e1) (subst_map xs e2)
  end.

(* Definition subO := leibnizO sub. *)
(* Definition sub_rel := subO -n> subO -n> iProp Σ. *)

Definition sub_rel := persistent_pred (sub * sub) (iPropI Σ).
Definition sub_relO := persistent_predO (sub * sub) (iPropI Σ).

Definition mk_sub_rel (pred : (sub * sub) → iProp Σ) {Pers : ∀ g, Persistent (pred g)} : sub_rel :=
  @PersPred _ _ pred Pers.
Global Instance sub_rel_pers (τ : sub_relO) : ∀ g, Persistent (τ g) := _.


Definition G_rel : sub_rel :=
  mk_sub_rel (fun g =>
    ∀ x v1 v2,
      ⌜g.1 !! x = Some v1⌝ →
      ⌜g.2 !! x = Some v2⌝ →
      V_rel (v1, v2))%I.

(* relations for open terms *)
Definition E_rel_o : expr_rel :=
  mk_expr_rel (fun e =>
    ∀ (g1 g2:sub), □ (G_rel (g1, g2) →
      E_rel (subst_map g1 e.1, subst_map g2 e.2)))%I.

Definition O_rel_o : expr_rel :=
  mk_expr_rel (fun e =>
    ∀ (g1 g2:sub),
      □ (G_rel (g1, g2) →
        O_rel (subst_map g1 e.1, subst_map g2 e.2)))%I.

(* Definition V_rel_o : val_rel :=
  mk_val_rel (fun v =>
    (∀ (g1 g2:sub) (v1' v2':val),
      ⌜to_val (subst_map g1 (of_val v.1)) = Some v1'⌝ →
      ⌜to_val (subst_map g2 (of_val v.2)) = Some v2'⌝ →
      V_rel (v1', v2')))%I. *)

Definition V_rel_o : val_rel :=
  mk_val_rel (fun v =>
    (∀ (g1 g2:sub),
      V_rel (subst_map_val g1 v.1, subst_map_val g2 v.2)))%I.

(* compatibility lemmas *)

(* TODO it should possible to prevent iris from "leaking out" here,
  so it is only used to define these things *)
Lemma erel_to_vrel e1 e2 v1 v2:
  ⊢ E_rel_o (e1, e2) →
    ⌜to_val e1 = Some v1⌝ →
    ⌜to_val e2 = Some v2⌝ →
    V_rel_o (v1, v2)%I.
Proof.
Admitted.

Lemma RelK_elim (E1 E2 : evctx) (v1 v2 : val) :
  (⊢ K_rel (E1, E2)) →
  (⊢ V_rel (v1, v2)) →
  ⊢ O_rel (fill E1 (of_val v1), fill E2 (of_val v2)).
Proof.
  intros HE Hv.
  (* unfold K_rel, K_rel_pre in HE. simpl in HE. *)
  (* unfold O_rel, O_rel_pre. simpl. *)
  iApply HE.
  iApply Hv.
Qed.

Lemma RelK_elim1 (E1 E2 : evctx) (v1 v2 : val) :
  K_rel (E1, E2) ∧ V_rel (v1, v2)
  ⊢ O_rel (fill E1 (of_val v1), fill E2 (of_val v2)).
Proof.
  iIntros "[#HE #Hv]".
  (* intros HE Hv. *)
  (* unfold K_rel, K_rel_pre in HE. simpl in HE. *)
  (* unfold O_rel, O_rel_pre. simpl. *)
  iApply "HE".
  iApply "Hv".
Qed.

(* Search (⊢ _ → _). *)
(* Check bi.entails_impl. *)
(* Check bi.impl_entails. *)

(* aka val_inclusion *)
Theorem compat_val: ∀ v1 v2,
  V_rel_o (v1, v2)
  ⊢ E_rel_o (of_val v1, of_val v2).
Proof.
  (* intros * Hv. *)
  iIntros "%v1 %v2 #Hv".
  Opaque E_rel.
  Opaque V_rel_o.
  Opaque G_rel.
  unfold E_rel_o. simpl.
  iIntros "%g1 %g2". iModIntro. iIntros "#H".
  Transparent E_rel.
  unfold E_rel.
  Opaque O_rel.
  Opaque K_rel.
  simpl.
  iIntros "%E1 %E2".
  iModIntro.
  iIntros "#HK".

  (* iApply "Hv". *)

  (* Check RelK_elim1. *)
  (* iUnfold V_rel_o in "Hv". *)

  (* iPoseProof (RelK_elim1 $! E1 E2 with "[HE]") as "H1". *)
 (* g2 v1 v2 with "HE" *)
  (* iAssert RelK_elim as "H1". *)
  (* iSpecialize (RelK_elim). *)

  iApply RelK_elim1.
  iSplit.
  - iApply "HK".
  -
  iApply "Hv".
Qed.


Theorem compat_var: ∀ x,
  ⊢ E_rel_o (var x, var x).
Proof.
Admitted.

Theorem compat_app: ∀ e1 e2 e1' e2',
  E_rel_o (e1, e2) ∧
  E_rel_o (e1', e2')
  ⊢ E_rel_o (app e1 e1', app e2 e2').
Proof.
Admitted.

Theorem compat_abs: ∀ e1 e2 x,
  E_rel_o (e1, e2)
  ⊢ V_rel_o (vlambda x e1, vlambda x e2).
Proof.
Admitted.

Theorem compat_plus: ∀ e1 e2,
  E_rel_o (e1, e1) ∧
  E_rel_o (e2, e2)
  ⊢ E_rel_o (eplus e1 e2, eplus e1 e2).
Proof.
Admitted.

Fixpoint fundmental_e e:
  ⊢ E_rel_o (e, e)
with fundmental_v v:
  ⊢ V_rel_o (v, v).
Proof.
  { induction e.
    - pose proof (compat_val v v).
      eauto.
    - apply compat_var.
    - iApply compat_app. iSplit; auto.
    - iApply compat_plus. iSplit; auto.
  }
  { (* value *)
    admit.
  }
Abort.

Theorem L_adequacy: ∀ e1 e2,
  L_rel (e1, e2)
  ⊢ ⌜equiterminate e1 e2⌝.
Proof.
Abort.

Theorem O_adequacy: ∀ e1 e2,
  O_rel (e1, e2)
  ⊢ ⌜equiterminate e1 e2⌝.
Proof.
Abort.

Theorem soundness: ∀ e1 e2,
  E_rel_o (e1, e2) ⊢ ⌜obs_eqv e1 e2⌝.
Proof.
Abort.

Theorem completeness: ∀ e1 e2,
  ⌜obs_eqv e1 e2⌝ ⊢ E_rel_o (e1, e2).
Proof.
Abort.

End logrel.
