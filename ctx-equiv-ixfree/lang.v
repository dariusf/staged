
From IxFree Require Import Lib Nat.
From CtxEquivIxFree Require Import ixfree_tactics.
(* From stdpp Require Export binders. *)
From stdpp Require Export gmap.
From stdpp Require Export strings.

Definition loc : Set := nat.

Inductive expr :=
  (* | eint (z : Z) *)
  (* | eunit *)
  | ret (v:val)
  (* | ens (H : hprop) *)
  (* | ensp (P : prop) *)
  (* | var (x : binder) *)
  | var (x : string)
  (* | bind (e1 : expr) (x : binder) (e2 : expr) *)
  | app (e1 e2: expr)
  (* | abs (x : binder) (e : expr) *)
  (* | eplus (e1 e2: expr) *)

with val :=
  | vint (z : Z)
  | vlambda (x : string) (e: expr)
  (* | vbool (b : bool) *)
  (* | vloc (l : loc) *)
  | vunit.

Definition to_val (e : expr) : option val :=
  match e with
  | ret v => Some v
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
      vlambda y $ if decide (x = y) then e else
        (subst x es e)
  end

with subst (x : string) (es : expr) (e : expr)  : expr :=
  match e with
  | ret v => ret (subst_val x es v)
  (* The function [decide] can be used to decide propositions.
    [decide P] is of type {P} + {¬ P}.
    It can only be applied to propositions for which, by type class inference,
    it can be determined that the proposition is decidable. *)
  | var y => if decide (x = y) then es else var y
  (* | abs y e =>
      abs y $ if decide (BNamed x = y) then e else subst x es e *)
  | app e1 e2 => app (subst x es e1) (subst x es e2)
  (* | eplus e1 e2 => eplus (subst x es e1) (subst x es e2) *)
  end.

(* Definition subst' (mx : binder) (es : expr) : expr → expr :=
  match mx with BNamed x => subst x es | BAnon => id end. *)

Definition is_val (e : expr) : Prop :=
  match e with
  | ret v => True
  (* | abs x e => True *)
  | _ => False
  end.

(* Definition of_val (v : val) : expr :=
  match v with
  | vunit => eunit
  | vint n => eint n
  | vlambda x e => abs x e
  end. *)

Notation of_val := ret.
Coercion ret : val >-> expr.

Inductive base_step : expr → expr → Prop :=
  | BetaS x e1 e2 e' :
     is_val e2 →
     e' = subst x e2 e1 →
     base_step (app (ret (vlambda x e1)) e2) e'
  (* | PlusS e1 e2 (n1 n2 n3 : Z):
     e1 = (eint n1) →
     e2 = (eint n2) →
     (n1 + n2)%Z = n3 →
     base_step (Plus e1 e2) (eint n3) *)
  .

(* inside-out contexts *)
Inductive ectx :=
  | ectx_hole : ectx
  | ectx_app1 : ectx → expr → ectx
  | ectx_app2 : val → ectx → ectx.

Fixpoint plug (E : ectx) (e : expr) : expr :=
  match E with
  | ectx_hole => e
  | ectx_app1 E1 e1 => plug E1 (app e e1)
  | ectx_app2 v E1 => plug E1 (app v e)
  end.

(** Outside-in evaluation contexts *)
Inductive rctx :=
  | rctx_hole : rctx
  | rctx_app1 : rctx → expr → rctx
  | rctx_app2 : val → rctx → rctx.

Fixpoint rplug (E : rctx) (e : expr) : expr :=
  match E with
  | rctx_hole => e
  | rctx_app1 E1 e1 => app (rplug E1 e) e1
  | rctx_app2 v E1 => app v (rplug E1 e)
  end.

Notation fill := plug.

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

Definition sub := gmap string val.

Fixpoint subst_map_val (xs : sub) (v : val) : val :=
  match v with
  | vunit => vunit
  | vint n => vint n
  | vlambda x e => vlambda x (subst_map (delete x xs) e)
  end

with subst_map (xs : sub) (e : expr) : expr :=
  match e with
  | ret v => ret (subst_map_val xs v)
  (* | eunit => eunit *)
  | var y => match xs !! y with Some es => of_val es | _ =>  var y end
  | app e1 e2 => app (subst_map xs e1) (subst_map xs e2)
  (* | abs x e => abs x (subst_map (binder_delete x xs) e) *)
  (* | eplus e1 e2 => eplus (subst_map xs e1) (subst_map xs e2) *)
  end.

Fixpoint is_closed (X : list string) (e : expr) : bool :=
  match e with
  | var x => bool_decide (x ∈ X)
  | ret vunit | ret (vint _) => true
  | ret (vlambda x e) => is_closed (x :: X) e
  | app e1 e2
  (* | eplus e1 e2 *)
  => is_closed X e1 && is_closed X e2
  end.

Definition closed (X : list string) (e : expr) : Prop := Is_true (is_closed X e).

Definition subst_is_closed (dom : list string) (free : list string) (sub : sub) :=
  ∀ x, x ∈ dom →
    ∃ v, sub !! x = Some v ∧ closed free (ret v).

(* this is reversed compared to the normal statement? *)
Lemma subst_is_closed_subseteq: ∀ Γ (X : list string) (γ1 γ2: sub),
  γ1 ⊆ γ2 → subst_is_closed Γ X γ1 → subst_is_closed Γ X γ2.
Proof.
  intros * Hsub Hclosed2. intros x Hl.
  unfold subst_is_closed in Hclosed2.
  specialize (Hclosed2 x Hl) as (v&?&?).
  exists v.
  rewrite (map_subseteq_spec γ1 γ2) in Hsub.
  specialize (Hsub x v H).
  split; done.
Qed.

(* Relations *)

Definition expr_rel := expr ⇒ᵢ expr ⇒ᵢ IRel.
Definition val_rel := val ⇒ᵢ val ⇒ᵢ IRel.
Definition sub_rel := sub ⇒ᵢ sub ⇒ᵢ IRel.
Definition ctx_rel := ectx ⇒ᵢ ectx ⇒ᵢ IRel.

Definition L_rel_pre (L_rel : expr_rel) : expr_rel :=
  λ e1 e2,
    (closed [] e1)ᵢ ∧ᵢ
    (closed [] e2)ᵢ ∧ᵢ
    (∀ v1 : val, e1 = v1 → terminates e2)ᵢ ∧ᵢ
    ∀ᵢ e1' : expr, (contextual_step e1 e1')ᵢ →ᵢ ▷ L_rel e1' e2.

Definition L_rel_fix := I_fix L_rel_pre.
Definition L_rel := L_rel_pre L_rel_fix.
Definition O_rel e1 e2 := L_rel e1 e2 ∧ᵢ L_rel e2 e1.

Definition K_rel_pre (V_rel : val_rel) (E1 E2 : ectx) :=
  ∀ᵢ v1 v2 : val,
    V_rel v1 v2 →ᵢ
    O_rel (fill E1 v1) (fill E2 v2).

Definition R_rel_pre (V_rel : val_rel) (e1 e2 : expr) :=
  ∀ᵢ E1 E2, ▷ K_rel_pre V_rel E1 E2 →ᵢ O_rel (fill E1 e1) (fill E2 e2).

Definition V_rel_pre (V_rel : val_rel) : val_rel :=
  λ v1 v2,
    (closed [] v1)ᵢ ∧ᵢ
    (closed [] v2)ᵢ ∧ᵢ
    ∀ᵢ (u1 u2 : val),
      (closed [] u1)ᵢ →ᵢ
      (closed [] u2)ᵢ →ᵢ
      ▷ V_rel u1 u2 →ᵢ
      R_rel_pre V_rel (app v1 u1) (app v2 u2).

Definition V_rel_fix := I_fix V_rel_pre.

Definition V_rel := V_rel_pre V_rel_fix.
Definition R_rel := R_rel_pre V_rel_fix.
Definition K_rel := K_rel_pre V_rel_fix.

Definition E_rel : expr_rel :=
  λ e1 e2,
    (closed [] e1)ᵢ ∧ᵢ
    (closed [] e2)ᵢ ∧ᵢ
    ∀ᵢ E1 E2 : ectx, K_rel E1 E2 →ᵢ O_rel (fill E1 e1) (fill E2 e2).

(* Relations for open terms *)

Definition G_rel (Γ: list string) (γ1 γ2 : sub) : IProp :=
  (subst_is_closed Γ [] γ1)ᵢ ∧ᵢ
  (subst_is_closed Γ [] γ2)ᵢ ∧ᵢ
  ∀ᵢ x v1 v2,
    (γ1 !! x = Some v1)ᵢ →ᵢ
    (γ2 !! x = Some v2)ᵢ →ᵢ
    V_rel v1 v2.

Definition E_rel_o (Γ: list string) (e1 e2 : expr) : IProp :=
  (closed Γ e1)ᵢ ∧ᵢ
  (closed Γ e2)ᵢ ∧ᵢ
  ∀ᵢ γ1 γ2, G_rel Γ γ1 γ2 →ᵢ E_rel (subst_map γ1 e1) (subst_map γ2 e2).

Definition V_rel_o (Γ: list string) (v1 v2 : val) : IProp :=
  (closed Γ v1)ᵢ ∧ᵢ
  (closed Γ v2)ᵢ ∧ᵢ
  ∀ᵢ γ1 γ2, G_rel Γ γ1 γ2 →ᵢ V_rel (subst_map_val γ1 v1) (subst_map_val γ2 v2).

(** Contractiveness and unrolling fixpoint *)

Lemma L_rel_pre_contractive : contractive L_rel_pre.
Proof.
  intro n; iintros; unfold L_rel_pre; auto_contr.
Qed.

Lemma L_rel_roll p1 p2 n :
  n ⊨ L_rel p1 p2 → n ⊨ L_rel_fix p1 p2.
Proof.
  intro H; iapply (I_fix_roll expr_rel); [ | exact H ].
  apply L_rel_pre_contractive.
Qed.

Lemma L_rel_unroll p1 p2 n :
  n ⊨ L_rel_fix p1 p2 → n ⊨ L_rel p1 p2.
Proof.
  intro H; iapply (I_fix_unroll expr_rel); [ | exact H ].
  apply L_rel_pre_contractive.
Qed.

Lemma V_rel_pre_contractive : contractive V_rel_pre.
Proof.
  intro n; iintros; unfold V_rel_pre, R_rel_pre, K_rel_pre; auto_contr.
Qed.

Lemma V_rel_roll v1 v2 n :
  n ⊨ V_rel v1 v2 → n ⊨ V_rel_fix v1 v2.
Proof.
  intro H; iapply (I_fix_roll val_rel); [ | exact H ].
  apply V_rel_pre_contractive.
Qed.

Lemma V_rel_unroll v1 v2 n :
  n ⊨ V_rel_fix v1 v2 → n ⊨ V_rel v1 v2.
Proof.
  intro H; iapply (I_fix_unroll val_rel); [ | exact H ].
  apply V_rel_pre_contractive.
Qed.

(** introduction and elimination lemmas *)

Lemma V_rel_intro (v1 v2 : val) n :
  closed [] v1 →
  closed [] v2 →
  (n ⊨ ∀ᵢ (u1 u2:val),
        (closed [] u1)ᵢ →ᵢ
        (closed [] u2)ᵢ →ᵢ
        ▷ V_rel u1 u2 →ᵢ
        R_rel (app v1 u1) (app v2 u2)) →
  n ⊨ V_rel v1 v2.
Proof.
  intros H_closed1 H_closed2 Hv.
  isplit; [| isplit].
  - apply I_prop_intro. assumption.
  - apply I_prop_intro. assumption.
  - iintros u1 u2 Hucl1 Hucl2 Hv_later.
    ispecialize Hv u1.
    ispecialize Hv u2.
    iapply Hv in Hucl1.
    iapply Hucl1 in Hucl2.
    iapply Hucl2.
    later_shift.
    apply V_rel_unroll.
    assumption.
Qed.

Lemma V_rel_elim (v1 v2 : val) n :
  n ⊨ V_rel v1 v2 →
  closed [] v1 ∧
  closed [] v2 ∧
  (n ⊨ (∀ᵢ (u1 u2 : val),
         (closed [] u1)ᵢ →ᵢ
         (closed [] u2)ᵢ →ᵢ
         ▷ V_rel u1 u2 →ᵢ
         R_rel (app v1 u1) (app v2 u2))).
Proof.
  intros Hv.
  unfold V_rel in Hv.
  unfold V_rel_pre in Hv.
  idestruct Hv as H_closed1 Hv. idestruct H_closed1.
  idestruct Hv as H_closed2 Hv. idestruct H_closed2.
  split; [| split].
  - assumption.
  - assumption.
  - iintros u1 u2 Hucl1 Hucl2 Hv_later.
    ispecialize Hv u1. ispecialize Hv u2. ispec Hv Hucl1. ispec Hv Hucl2.
    iapply Hv.
    later_shift.
    apply V_rel_roll.
    assumption.
Qed.

Lemma K_rel_intro (E1 E2 : ectx) n :
  n ⊨ (∀ᵢ v1 v2, V_rel v1 v2 →ᵢ O_rel (fill E1 v1) (fill E2 v2)) →
  n ⊨ K_rel E1 E2.
Proof.
  intro HE. iintros v1 v2 Hv. iapply HE.
  apply V_rel_unroll. assumption.
Qed.

Lemma K_rel_elim (E1 E2 : ectx) (v1 v2 : val) n :
  n ⊨ K_rel E1 E2 →
  n ⊨ V_rel v1 v2 →
  n ⊨ O_rel (fill E1 v1) (fill E2 v2).
Proof.
  intros HE Hv. iapply HE. apply V_rel_roll. assumption.
Qed.

Lemma R_rel_intro (e1 e2 : expr) n :
  n ⊨ (∀ᵢ E1 E2, ▷ K_rel E1 E2 →ᵢ O_rel (fill E1 e1) (fill E2 e2)) ->
  n ⊨ R_rel e1 e2.
Proof. auto. Qed.

Lemma R_rel_elim (e1 e2 : expr) E1 E2 n :
  n ⊨ R_rel e1 e2 →
  n ⊨ ▷ K_rel E1 E2 →
  n ⊨ O_rel (fill E1 e1) (fill E2 e2).
Proof.
  intros He HE; iapply He; assumption.
Qed.

Lemma E_rel_intro (e1 e2 : expr) n :
  closed [] e1 →
  closed [] e2 →
  (n ⊨ ∀ᵢ E1 E2, K_rel E1 E2 →ᵢ O_rel (fill E1 e1) (fill E2 e2)) ->
  n ⊨ E_rel e1 e2.
Proof.
  intros H_closed1 H_closed2 HE.
  unfold E_rel.
  isplit; [| isplit].
  - apply I_prop_intro. exact H_closed1.
  - apply I_prop_intro. exact H_closed2.
  - exact HE.
Qed.

Lemma E_rel_elim (e1 e2 : expr) n :
  n ⊨ E_rel e1 e2 →
  closed [] e1 ∧
  closed [] e2 ∧
  (n ⊨ ∀ᵢ E1 E2, K_rel E1 E2 →ᵢ O_rel (fill E1 e1) (fill E2 e2)).
Proof.
  intros He.
  unfold E_rel in He.
  idestruct He as H_closed1 He. idestruct H_closed1.
  idestruct He as H_closed2 He. idestruct H_closed2.
  split; [| split]; assumption.
Qed.

(** Bind lemma *)
Lemma E_rel_elimO e1 e2 E1 E2 n :
  n ⊨ E_rel e1 e2 →
  n ⊨ K_rel E1 E2 →
  n ⊨ O_rel (fill E1 e1) (fill E2 e2).
Proof.
  intros He HE.
  apply E_rel_elim in He as (_ & _ & He).
  iapply He. exact HE.
Qed.

Lemma V_rel_elimE (v1 v2 u1 u2 : val) n :
  n ⊨ V_rel v1 v2 →
  n ⊨ V_rel u1 u2 →
  n ⊨ E_rel (app v1 u1) (app v2 u2).
Proof.
  intros Hv Hu.
  destruct (V_rel_elim _ _ _ Hv) as (Hv1_closed & Hv2_closed & Hv').
  destruct (V_rel_elim _ _ _ Hu) as (Hu1_closed & Hu2_closed & _).
  apply E_rel_intro.
  { unfold closed. simpl. rewrite -> andb_True. auto. }
  { unfold closed. simpl. rewrite -> andb_True. auto. }
  iintros E1 E2 HE. simpl.
  apply R_rel_elim.
  - iapply Hv'.
    + apply I_prop_intro. assumption.
    + apply I_prop_intro. assumption.
    + later_shift. exact Hu.
  - later_shift. exact HE.
Qed.

Lemma G_rel_intro Γ γ1 γ2 n :
  subst_is_closed Γ [] γ1 →
  subst_is_closed Γ [] γ2 →
  n ⊨
    (∀ᵢ x v1 v2,
       (γ1 !! x = Some v1)ᵢ →ᵢ
       (γ2 !! x = Some v2)ᵢ →ᵢ
       V_rel v1 v2) →
  n ⊨ G_rel Γ γ1 γ2.
Proof.
  intros H_closed1 H_closed2 Hγ.
  unfold G_rel.
  isplit; [| isplit].
  - apply I_prop_intro. exact H_closed1.
  - apply I_prop_intro. exact H_closed2.
  - exact Hγ.
Qed.

Lemma G_rel_elim Γ γ1 γ2 n :
  n ⊨ G_rel Γ γ1 γ2 →
  subst_is_closed Γ [] γ1 ∧
  subst_is_closed Γ [] γ2 ∧
  (n ⊨
     ∀ᵢ x v1 v2,
       (γ1 !! x = Some v1)ᵢ →ᵢ
       (γ2 !! x = Some v2)ᵢ →ᵢ
       V_rel v1 v2).
Proof.
  unfold G_rel.
  intros Hγ.
  idestruct Hγ as H_closed1 Hγ. idestruct H_closed1.
  idestruct Hγ as H_closed2 Hγ. idestruct H_closed2.
  auto.
Qed.

Lemma E_rel_o_intro Γ e1 e2 n :
  closed Γ e1 →
  closed Γ e2 →
  (n ⊨ ∀ᵢ γ1 γ2,
         G_rel Γ γ1 γ2 →ᵢ
         E_rel (subst_map γ1 e1) (subst_map γ2 e2)) →
  n ⊨ E_rel_o Γ e1 e2.
Proof.
  intros H_closed1 H_closed2 He.
  unfold E_rel_o.
  isplit; [| isplit].
  - apply I_prop_intro. exact H_closed1.
  - apply I_prop_intro. exact H_closed2.
  - exact He.
Qed.

Lemma E_rel_o_elim Γ e1 e2 n :
  n ⊨ E_rel_o Γ e1 e2 →
  closed Γ e1 ∧
  closed Γ e2 ∧
  (n ⊨ ∀ᵢ γ1 γ2, G_rel Γ γ1 γ2 →ᵢ E_rel (subst_map γ1 e1) (subst_map γ2 e2)).
Proof.
  unfold E_rel_o.
  intros He.
  idestruct He as H_closed1 He. idestruct H_closed1.
  idestruct He as H_closed2 He. idestruct H_closed2.
  auto.
Qed.

Lemma V_rel_o_intro Γ (v1 v2 : val) n :
  closed Γ v1 →
  closed Γ v2 →
  (n ⊨ ∀ᵢ γ1 γ2,
         G_rel Γ γ1 γ2 →ᵢ
         V_rel (subst_map_val γ1 v1) (subst_map_val γ2 v2)) →
  n ⊨ V_rel_o Γ v1 v2.
Proof.
  intros H_closed1 H_closed2 Hv.
  unfold V_rel_o.
  isplit; [| isplit].
  - apply I_prop_intro. exact H_closed1.
  - apply I_prop_intro. exact H_closed2.
  - exact Hv.
Qed.

Lemma V_rel_o_elim Γ (v1 v2 : val) n :
  n ⊨ V_rel_o Γ v1 v2 →
  closed Γ v1 ∧
  closed Γ v2 ∧
  (n ⊨ ∀ᵢ γ1 γ2,
         G_rel Γ γ1 γ2 →ᵢ
         V_rel (subst_map_val γ1 v1) (subst_map_val γ2 v2)).
Proof.
  unfold V_rel_o.
  intros Hv.
  idestruct Hv as H_closed1 Hv. idestruct H_closed1.
  idestruct Hv as H_closed2 Hv. idestruct H_closed2.
  auto.
Qed.

(** compatibility lemma *)

(* aka val inclusion *)
Lemma compat_val (Γ : list string) (v1 v2 : val) n :
  n ⊨ V_rel_o Γ v1 v2 →
  n ⊨ E_rel_o Γ v1 v2.
Proof.
  intros Hv.
  apply V_rel_o_elim in Hv as (H_closed1 & H_closed2 & Hv).
  apply E_rel_o_intro.
  { exact H_closed1. }
  { exact H_closed2. }
  clear H_closed1 H_closed2.
  iintros γ1 γ2 Hγ.
  ispecialize Hv γ1. ispecialize Hv γ2. ispec Hv Hγ.
  apply V_rel_elim in Hv as (H_closed1 & H_closed2 & Hv).
  apply E_rel_intro.
  { exact H_closed1. }
  { exact H_closed2. }
  iintros E1 E2 HE. simpl.
  apply (K_rel_elim E1 E2 _ _ _ HE).
  apply V_rel_intro.
  { exact H_closed1. }
  { exact H_closed2. }
  { exact Hv. }
Qed.

Lemma closed_app xs e1 e2:
  closed xs (app e1 e2) ↔
  closed xs e1 ∧ closed xs e2.
Proof. unfold closed. simpl. by rewrite andb_True. Qed.

Lemma compat_app (Γ:list string) (e1 e2 e1' e2' : expr) n :
  n ⊨ E_rel_o Γ e1 e2 →
  n ⊨ E_rel_o Γ e1' e2' →
  n ⊨ E_rel_o Γ (app e1 e1') (app e2 e2').
Proof.
  intros He He'.
  apply E_rel_o_elim in He as (Hc1 & Hc2 & He).
  (* From He, we have closed-ness of e1, closed-ness of e2 and
     contextual equivalence of e1 and e2, in related context *)
  apply E_rel_o_elim in He' as (Hc1' & Hc2' & He').
  apply E_rel_o_intro.
  { rewrite closed_app. auto. }
  { rewrite closed_app. auto. }
  clear Hc1 Hc2 Hc1' Hc2'.
  iintros γ1 γ2 Hγ. simpl.
  ispecialize He γ1. ispecialize He γ2. ispec He Hγ.
  ispecialize He' γ1. ispecialize He' γ2. ispec He' Hγ.
  apply E_rel_elim in He as (Hc1 & Hc2 & He).
  apply E_rel_elim in He' as (Hc1' & Hc2' & He').
  apply E_rel_intro.
  { rewrite closed_app. auto. }
  { rewrite closed_app. auto. }
  iintros E1 E2 HE.
  (* e1/e2 are evaluated first. We "zap" then down using He.
     We consider the contexts surround e1 and e2, and we are left
     with showing that the surrounding contexts are related *)
  ispecialize He (ectx_app1 E1 (subst_map γ1 e1')).
  ispecialize He (ectx_app1 E2 (subst_map γ2 e2')).
  iapply He.
  (* after e1/e2 are fully evaluated, we are left with `ectx_app1 E1 e1'`
     and `ectx_app1 E2 e2'`. Using K_rel_intro, we "assume" that e1 and
     e2 evaluated to two related values v1 and v2, respectively; and then
     we prove that the two contexts are related *)
  apply K_rel_intro. iintros v1 v2 Hv. simpl.
  (* e1'/e2' are evaluated. We "zap" then down using He' *)
  ispecialize He' (ectx_app2 v1 E1).
  ispecialize He' (ectx_app2 v2 E2).
  iapply He'.
  apply K_rel_intro. iintros v1' v2' Hv'. simpl.
  (* Now, we "zap" (app v1 v1') and (app v2 v2') down using E_rel_elimO *)
  apply E_rel_elimO.
  apply V_rel_elimE; [exact Hv | exact Hv'].
  (* Finally, we are left with just E1 and E2. They are related according
     to our hypothesis *)
  exact HE.
Qed.

Lemma closed_var Γ x : x ∈ Γ ↔ closed Γ (var x).
Proof.
  unfold closed. simpl. by rewrite bool_decide_spec. Qed.

Lemma subst_is_closed_closed_subst_map Γ γ x:
  x ∈ Γ →
  subst_is_closed Γ [] γ →
  closed [] (subst_map γ (var x)).
Proof.
  unfold subst_is_closed, closed. intros Hd Hs.
  simpl.
  destruct (γ !! x) eqn:He.
  - specialize (Hs x Hd). destruct Hs as (v0&H1&H2). congruence.
  - specialize (Hs x Hd). destruct Hs as (v0&H1&H2). congruence.
Qed.

Lemma compat_var Γ (x : string) n :
  x ∈ Γ →
  n ⊨ E_rel_o Γ (var x) (var x).
Proof.
  intros Hdom.
  apply E_rel_o_intro.
  { by apply closed_var. }
  { by apply closed_var. }
  iintros γ1 γ2 Hγ.
  apply G_rel_elim in Hγ as (Hc1 & Hc2 & Hγ).
  apply E_rel_intro.
  { apply (subst_is_closed_closed_subst_map _ _ _ Hdom Hc1). }
  { apply (subst_is_closed_closed_subst_map _ _ _ Hdom Hc2). }
  iintros E1 E2 HE. simpl.
  unfold subst_is_closed in *.
  specialize (Hc1 x Hdom) as (v1 & H_lookup1 & Hc1).
  specialize (Hc2 x Hdom) as (v2 & H_lookup2 & Hc2).
  ispec Hγ x v1 v2 H_lookup1 H_lookup2.
  rewrite H_lookup1.
  rewrite H_lookup2.
  by apply K_rel_elim.
Qed.

Lemma G_sub_closed Γ γ1 γ2 n :
  n ⊨ G_rel Γ γ1 γ2 →
  subst_is_closed Γ [] γ1 ∧ subst_is_closed Γ [] γ2.
Proof. intros Hγ. apply G_rel_elim in Hγ. easy. Qed.

Lemma closed_lambda e X x : closed X (vlambda x e) ↔ closed (x :: X) e.
Proof. split. auto. auto. Qed.

Lemma subst_val_closed v X x es :
  closed X (of_val v) → x ∉ X → subst_val x es v = v
with subst_closed X e x es :
  closed X e → x ∉ X → subst x es e = e.
Proof.
  { induction v.
    { reflexivity. }
    { simpl.
      case_decide.
      - reflexivity.
      - intros.
        f_equal.
        rewrite closed_lambda in H0.
        apply (subst_closed _ _ _ _ H0).
        set_solver. }
    { reflexivity. } }
 { induction e; intros; simpl.
    { f_equal.
      eapply subst_val_closed.
      apply H. assumption. }
    { case_decide.
      - subst.
        unfold closed in H. simpl in H. apply bool_decide_unpack in H.
        set_solver.
      - reflexivity. }
    { apply closed_app in H.
      destruct H as (H1&H2).
      specialize (IHe1 H1 H0).
      specialize (IHe2 H2 H0).
      f_equal.
      - assumption.
      - assumption. } }
Qed.

(* Lemma subst_closed_nil e x es : closed [] e → subst x es e = e.
Proof.
  intros. apply subst_closed with []; set_solver.
Qed. *)

Lemma L_rel_red_l (e1 e1' e2 : expr) n :
  closed [] e1 →
  closed [] e2 →
  contextual_step e1 e1' →
  n ⊨ ▷ L_rel e1' e2 →
  n ⊨ L_rel e1 e2.
Proof.
  intros Hc1 Hc2 Hred HL.
  unfold L_rel. unfold L_rel_pre.
  repeat isplit.
  - iintro. assumption.
  - iintro. assumption.
  - iintro.
    intros v1 H_eq.
    rewrite -> H_eq in Hred.
    (* absurd *)
    admit.
  - iintros e1'' Hred'.
    idestruct Hred'.
    replace e1'' with e1' by admit. (* deterministic *)
    later_shift. apply L_rel_roll.
    exact HL.
Admitted.

Lemma L_rel_red_r (e2 e2' : expr) n :
  (*closed [] e1 →*)
  closed [] e2 →
  contextual_step e2 e2' →
  n ⊨ (∀ᵢ e1, L_rel e1 e2' →ᵢ L_rel e1 e2).
Proof.
  intros Hc2 Hred.
  loeb_induction.
  iintros e1 HL.
  unfold L_rel in HL.
  unfold L_rel_pre in HL.
  idestruct HL as Hc1 HL.
  idestruct HL as Hc2' HL.
  idestruct HL as HL1 HL2.
  repeat isplit.
  - assumption.
  - iintro. assumption.
  - iintro. intros v1 H_eq.
    idestruct HL1.
    specialize (HL1 v1 H_eq).
    unfold terminates in *.
    unfold bigstep in *.
    admit.
  - iintros e1' Hred'.
    ispec HL2 e1' Hred'.
    later_shift.
    apply L_rel_unroll in HL2.
    apply L_rel_roll.
    iapply IH. exact HL2.
Admitted.

Lemma O_rel_red_l (e1 e1' e2 : expr) n :
  closed [] e1 →
  closed [] e2 →
  contextual_step e1 e1' →
  n ⊨ O_rel e1' e2 →
  n ⊨ O_rel e1 e2.
Proof.
  intros Hc1 Hc2 Hred HO.
  unfold O_rel in *.
  idestruct HO as HL1 HL2.
  isplit.
  - eapply L_rel_red_l.
    + exact Hc1.
    + exact Hc2.
    + exact Hred.
    + later_shift. exact HL1.
  - iapply L_rel_red_r.
    + exact Hc1.
    + exact Hred.
    + exact HL2.
Qed.

Lemma O_rel_red_r (e1 e2 e2' : expr) n :
  (* contextual_step e1 e1' → contextual_step e2 e2' → *)
  closed [] e1 →
  closed [] e2 →
  contextual_step e2 e2' →
  n ⊨ O_rel e1 e2' →
  n ⊨ O_rel e1 e2.
Proof.
  intros Hc1 Hc2 Hred HO.
  unfold O_rel in *.
  idestruct HO as HL1 HL2.
  isplit.
  - iapply L_rel_red_r.
    + exact Hc2.
    + exact Hred.
    + exact HL1.
  - iapply L_rel_red_l.
    + exact Hc2.
    + exact Hc1.
    + exact Hred.
    + later_shift. exact HL2.
Qed.

Lemma O_rel_red_both (e1 e1' e2 e2' : expr) n :
  closed [] e1 →
  closed [] e2 →
  contextual_step e1 e1' →
  contextual_step e2 e2' →
  n ⊨ ▷ O_rel e1' e2' →
  n ⊨ O_rel e1 e2.
Proof.
  intros Hc1 Hc2 Hred1 Hred2 HO.
  unfold O_rel in *.
  apply I_conj_later_down in HO.
  idestruct HO as HL1 HL2.
  isplit.
  - iapply L_rel_red_r.
    { exact Hc2. }
    { exact Hred2. }
    iapply L_rel_red_l.
    { exact Hc1. }
    { admit. }
    { exact Hred1. }
    { later_shift. exact HL1. }
  - iapply L_rel_red_r.
    { exact Hc1. }
    { exact Hred1. }
    iapply L_rel_red_l.
    { exact Hc2. }
    { admit. }
    { exact Hred2. }
    { later_shift. exact HL2. }
Admitted.

(* Observation: later_shift is significant in O_rel_red_both,
   but is not significant in O_rel_red_l and O_rel_red_r. We
   hypothesize that O_rel_red_l and O_rel_red_r are stronger
   property:
   - O_rel_red_both → O_rel_red_l ∧ O_rel_red_r
   - But not: O_rel_red_l ∧ O_rel_red_r → O_rel_red_both *)

Lemma R_rel_red_both (e1 e1' e2 e2' : expr) n :
  contextual_step e1 e1' →
  contextual_step e2 e2' →
  n ⊨ ▷ E_rel e1' e2' →
  n ⊨ R_rel e1 e2.
Proof.
  intros Hred1 Hred2 He.
  apply R_rel_intro.
  iintros E1 E2 HE.
  eapply O_rel_red_both.
  { admit. } (* need: closed-ness for context *)
  { admit. }
  { admit. }
  { admit. }
  { later_shift. apply E_rel_elimO.
    - exact He.
    - exact HE. }
Admitted.

(* Abort. *)

(* Lemma sem_context_rel_closed Γ γ1 γ2 n:
  n ⊨ G_rel Γ γ1 γ2 →
  ∀ x (v1 v2 : val),
    γ1 !! x = Some v1 →
    γ2 !! x = Some v2 →
    closed [] v1 ∧ closed [] v2.
Proof.
  (* unfold G_rel.
  intros Hg x v1 v2 H_lookup1 H_lookup2.
  (* apply I_prop_intro with (w := n) in H_lookup1. *)
  (* apply I_prop_intro with (w := n) in H_lookup2. *)
  (* ispec Hg H_lookup1.
  ispecialize Hg x.
  ispecialize Hg v1.
  ispecialize Hg v2. *)
  iapply Hg in H_lookup1.
  iapply H_lookup1 in H_lookup2.
  unfold V_rel in H_lookup2.
  unfold V_rel_pre in H_lookup2. *)
Admitted. *)

Lemma subst_subst_map : ∀ (e:expr) Γ (x : string) (es : val) (map : sub),
  (* x ∉ Γ → *)
  subst_is_closed Γ [] map →
  subst x es (subst_map (delete x map) e) =
  subst_map (insert x es map) e
with subst_subst_map_val : ∀ (v:val) Γ (x : string) (es : val) (map : sub),
  (* x ∉ Γ → *)
  subst_is_closed Γ [] map →
  subst x es (subst_map_val (delete x map) v) =
  subst_map_val (insert x es map) v.
Proof.
(* Admitted. *)
  { intros e. induction e.
    { intros. apply (subst_subst_map_val _ _ _ _ _ H). }
    { (* e is a variable x *)
      intros. simpl. destruct (decide (x0=x)) as [->|Hne].
      { (* if x=x0, we'll end up substituting es into x *)
        rewrite lookup_delete_eq with (m:=map).
        rewrite lookup_insert_eq with (m:=map).
        simpl.
        by rewrite decide_True. }
      { (* if not equal, the deletion and insertion will have no effect *)
        rewrite lookup_delete_ne with (m:=map). 2: { assumption. }
        rewrite lookup_insert_ne with (m:=map). 2: { assumption. }
        (* we then need to see if x is in the map to begin with *)
        destruct (map !! x) as [v1|] eqn:Hkey.
        { Fail rewrite Hkey. (* why does regular rewrite not work? *)
          setoid_rewrite Hkey.
          simpl.
          rewrite (subst_val_closed _ [] _ _).
          - reflexivity.
          -
          (* TODO we don't know anything about gamma *)
          (* to be able to use H, we need to know that x ∈ Γ *)
            unfold subst_is_closed in H.
            specialize (H x).

          (* apply (H _ _ Hkey). *)
          admit.
          - set_solver. }
      { setoid_rewrite Hkey.
        simpl.
        by rewrite decide_False. } } }
    { intros. simpl. f_equal.
    admit.
    admit.
      (* apply IHe1. assumption. *)
      (* apply IHe2. assumption. *)
      } }
  { intros v. induction v; intros.
    { reflexivity. }
    { (* the lambda case *)
      simpl. f_equal. f_equal.
      case_decide.
      { subst.
        rewrite delete_delete_eq with (m:=map).
        rewrite delete_insert_eq with (m:=map). done. }
      { rewrite delete_insert_ne with (m:=map). 2: { congruence. }
        rewrite delete_delete with (m:=map).
        admit.
        (* apply subst_subst_map. *)
        (* apply (subst_is_closed_subseteq _ _ map). *)
        (* apply delete_subseteq. *)
        (* assumption. *)
        } }
    { reflexivity. } }
(* Qed. *)
Admitted.

(** lemma a1 from erlang. scoping of extended substitutions: given a closed substitution,
  we can add a closed value to it *)
Lemma scope_extend x Γ X v γ:
  closed X (ret v) →
  subst_is_closed Γ X γ →
  x ∉ Γ →
  subst_is_closed (x::Γ) X (<[x := v]> γ).
Proof.
Abort.

Lemma elem_of_cons_r {A} (x0 x:A) Γ:
  x0 ∈ x :: Γ → x0 ≠ x → x0 ∈ Γ.
Proof.
  intros Hd Hne.
  pose proof (elem_of_cons Γ x0 x) as [H1 _].
  specialize (H1 Hd). destruct H1. congruence. assumption.
Qed.

(** special case of [scope_extend] *)
Lemma scope_extend1 Γ x (v:val) (γ:sub):
  closed [] v →
  subst_is_closed Γ [] γ →
  subst_is_closed (x::Γ) [] (<[x := v]> γ).
Proof.
  intros Hc Hsc.
  unfold subst_is_closed.
  intros x0 Hd.
  destruct (decide (x=x0)) as [->|Hne].
  - exists v. rewrite lookup_insert_eq with (m:=γ).
    split; done.
  - unfold subst_is_closed in Hsc.
    apply not_eq_sym in Hne.
    pose proof (elem_of_cons_r _ _ _ Hd Hne) as H.
    specialize (Hsc x0 H).
    destruct Hsc as (v0&?&?).
    exists v0.
    rewrite lookup_insert_ne with (m:=γ); [ | congruence ].
    split; done.
Qed.

Lemma sem_context_rel_insert Γ x v1 v2 γ1 γ2 n:
  n ⊨ V_rel v1 v2 →
  n ⊨ G_rel Γ γ1 γ2 →
  n ⊨ G_rel (x :: Γ) (<[x := v1]> γ1) (<[x := v2]> γ2).
Proof.
  intros.
  unfold G_rel.
  isplit; [ | isplit ].
  { iintro.
    apply V_rel_elim in H as (Hcv1&_).
    apply G_sub_closed in H0 as [H _].
    apply (scope_extend1 _ x _ _ Hcv1 H). }
  { iintro.
    apply V_rel_elim in H as (_&Hcv2&_).
    apply G_sub_closed in H0 as [_ H].
    apply (scope_extend1 _ x _ _ Hcv2 H). }

  iintros x0 v0 v3 H1 H2.
  destruct (decide (x=x0)).
  { subst.
    rewrite lookup_insert_eq with (m:=γ2) in H2. idestruct H2. injection H2 as ->.
    rewrite lookup_insert_eq with (m:=γ1) in H1. idestruct H1. injection H1 as ->.
    assumption. }
  { rewrite lookup_insert_ne with (m:=γ2) in H2. idestruct H2. 2: { assumption. }
    rewrite lookup_insert_ne with (m:=γ1) in H1. idestruct H1. 2: { assumption. }

    apply V_rel_elim in H as (Hcv1&Hcv2&?).
    ispec H v1 v2 Hcv1 Hcv2.
    iapply H0.
    - iintro. apply H1.
    - iintro. apply H3. }
Qed.

Lemma subst_map_closed' e X Y (Θ:sub):
  closed Y e →
  (∀ x, x ∈ Y → match Θ !! x with Some e' => closed X (ret e') | None => x ∈ X end) →
  closed X (subst_map Θ e).
Proof.
  (* induction e; intros. *)
Abort.
 (* in X, Θ, Y |-*; simpl. *)
  (* - *)


  (* - intros Hel%bool_decide_unpack Hcl.
    eapply Hcl in Hel.
    destruct (Θ !! x); first done.
    simpl. by eapply bool_decide_pack.
  - intros Hcl Hcl'. destruct x as [|x]; simpl; first naive_solver.
    eapply IHe; first done.
    intros y [|]%elem_of_cons.
    + subst. rewrite lookup_delete_eq. set_solver.
    + destruct (decide (x = y)); first by subst; rewrite lookup_delete_eq; set_solver.
      rewrite lookup_delete_ne //=. eapply Hcl' in H.
      destruct lookup; last set_solver.
      eapply closed_weaken; eauto with set_solver.
  - rewrite !andb_True. intros [H1 H2] Hcl. split; eauto.
  - auto.
  - rewrite !andb_True. intros [H1 H2] Hcl. split; eauto. *)
(* Qed. *)

Lemma subst_map_closed'_2 Γ X γ e:
  closed (X ++ Γ) e ->
  subst_is_closed Γ X γ ->
  closed X (subst_map γ e).
Proof.
  (* intros Hcl Hsubst.
  eapply subst_map_closed'; first eassumption.
  intros x Hx.
  destruct (Θ !! x) as [e'|] eqn:Heq.
  - eauto.
  - by eapply elem_of_app in Hx as [H|H%elem_of_elements%not_elem_of_dom].
Qed. *)
Admitted.

Lemma closed_var_in_subst (v:val) x Γ (γ:sub):
  closed Γ (var x) →
  subst_is_closed Γ [] γ →
  γ !! x = Some v →
  closed [] v.
Proof.
  intros Hc%closed_var Hsc Hg.
  unfold subst_is_closed in Hsc.
  specialize (Hsc x Hc).
  destruct Hsc as (v0&?&?).
  rewrite H in Hg. injection Hg. intros. subst.
  assumption.
Qed.

Lemma closed_var_not_in_subst x Γ (γ:sub):
  closed Γ (var x) →
  subst_is_closed Γ [] γ →
  γ !! x = None →
  False.
Proof.
  intros Hc%closed_var Hsc Hg.
  unfold subst_is_closed in Hsc.
  specialize (Hsc x Hc).
  destruct Hsc as (v0&?&?).
  congruence.
Qed.

(* lemma a2 erlang: scope weakening: Γ overapproximates the domain of γ? not sure if true *)
Lemma scope_weakening Γ x X γ:
  subst_is_closed Γ X γ →
  subst_is_closed (x::Γ) X γ.
Proof.
  unfold subst_is_closed.
  intros.
  destruct (decide (x=x0)) as [->|Hne].
  (* {

  } *)
  (* {
  specialize (H x0).
  } *)
Admitted.

Lemma scope_weakening1 Γ Γ1 X γ:
  Γ1 ⊆ Γ →
  subst_is_closed Γ X γ →
  subst_is_closed Γ1 X γ.
  (* closed X e → X ⊆ Y → closed Y e *)
Proof.
  unfold subst_is_closed.
  intros Hsub H. intros x Hd.
  specialize (H x).
  assert (x ∈ Γ).
  eapply elem_of_weaken.
  apply Hd.
  apply Hsub.
  specialize (H H0).
  assumption.
Abort.

Lemma closed_weaken e X Y:
  closed X e → X ⊆ Y → closed Y e
with closed_weaken_val (v:val) X Y:
  closed X v → X ⊆ Y → closed Y v.
Proof.
  { revert X Y.
    induction e; intros.
    - apply (closed_weaken_val _ _ _ H H0).
    - unfold closed, is_closed in *.
      apply bool_decide_unpack in H.
      apply bool_decide_pack.
      set_solver.
    - unfold closed in *. simpl in *.
      apply andb_prop_intro.
      apply andb_prop_elim in H.
      destruct H.
      split.
      apply (IHe1 _ _ H H0).
      apply (IHe2 _ _ H1 H0). }
  { revert X Y.
    induction v; intros.
    - constructor.
    - rewrite closed_lambda in H.
      rewrite closed_lambda.
      apply (closed_weaken _ _ _ H).
      set_solver.
    - constructor. }
Qed.

(* Lemma subst_closed_weaken Γ X Y map1 map2 :
  Y ⊆ X → map1 ⊆ map2 → subst_is_closed Γ Y map2 → subst_is_closed Γ X map1.
Proof.
  intros Hsub1 Hsub2 Hclosed2 x e Hl.
  eapply closed_weaken. 1:eapply Hclosed2, map_subseteq_spec; done. done.
Qed. *)

(* Lemma subst_closed_weaken X Y map1 map2 :
  Y ⊆ X → map1 ⊆ map2 → subst_closed Y map2 → subst_closed X map1.
Proof.
  intros Hsub1 Hsub2 Hclosed2 x e Hl.
  eapply closed_weaken. 1:eapply Hclosed2, map_subseteq_spec; done. done.
Qed. *)


(* Lemma lambda_closed_under_subst Γ γ x e:
  closed Γ (vlambda x e) →
  subst_is_closed Γ [] γ →
  closed [] (vlambda x (subst_map (delete x γ) e)).
Proof.
  (* intros. *)
Admitted. *)

  (* closed (elements (dom (<[x:=A]> Γ))) e →
  𝒢 Γ θ →
  closed [] (Lam x (subst_map (delete x θ) e)). *)

Lemma closed_subst_extension (e:expr): ∀ Γ γ x,
  closed Γ (subst_map γ e) →
  closed (x::Γ) (subst_map (delete x γ) e)
with closed_subst_extension_val (v:val): ∀ Γ γ x,
  closed Γ (subst_map_val γ v) →
  closed (x::Γ) (subst_map_val (delete x γ) v).
Proof.
  {
  induction e; intros.
  - apply (closed_subst_extension_val _ _ _ _ H).
  -
  simpl in H.
    simpl.
    admit.
  - admit.
  }
  {
    induction v; intros.
    admit.
    admit.
    admit.
  }
Admitted.

Lemma closed_subst_extension_lambda γ e x:
  closed [] (subst_map γ e) →
  closed [] (vlambda x (subst_map (delete x γ) e)).
Proof.
  intros.
  pose proof (closed_subst_extension _ [] _ x H).
  unfold closed in *.
  simpl in *.
  assumption.
Qed.

Lemma subst_map_closed'_3 e Γ γ:
  closed Γ e ->
  subst_is_closed Γ [] γ ->
  closed [] (subst_map γ e)
with subst_map_closed'_3_val (v:val) Γ γ:
  closed Γ v ->
  subst_is_closed Γ [] γ ->
  closed [] (subst_map_val γ v).
Proof.
  { induction e;
    intros Hc Hsc.
    { simpl. by apply subst_map_closed'_3_val with (Γ:=Γ). }
    { simpl.
      destruct (γ !! x) eqn:H.
      { apply (closed_var_in_subst _ _ _ _ Hc Hsc H). }
      { apply (closed_var_not_in_subst _ _ _ Hc Hsc H). } }
    { simpl.
      rewrite closed_app.
      rewrite closed_app in Hc.
      destruct Hc.
      split.
      apply (IHe1 H Hsc).
      apply (IHe2 H0 Hsc). } }
  { induction v; intros Hs Hsc.
    { constructor. }
    { simpl.
      rename subst_map_closed'_3 into IHe.
      rewrite closed_lambda in Hs.
      apply (scope_weakening _ x _ _) in Hsc.
      specialize (IHe e (x::Γ) γ Hs Hsc).
      apply (closed_subst_extension_lambda _ _ _ IHe).
      }
    { constructor. }
  }
Qed.

Lemma compat_lam Γ (e1 e2 : expr) n x :
  n ⊨ E_rel_o (x::Γ) e1 e2 →
  n ⊨ V_rel_o Γ (vlambda x e1) (vlambda x e2).
Proof.
  intros He.
  unfold V_rel_o.
  isplit; [ | isplit ].
  { iintro.
    unfold E_rel_o in He. idestruct He as Hc1 He.
    idestruct Hc1.
    rewrite closed_lambda.
    assumption. }
  { iintro.
    unfold E_rel_o in He. idestruct He as _ He. idestruct He as Hc2 He.
    idestruct Hc2.
    rewrite closed_lambda.
    assumption. }

  iintros γ1 γ2 Hγ.
  apply V_rel_intro.

  { apply (subst_map_closed'_3 (vlambda x e1) Γ γ1).
    { (* this part of the proof is repeated from before *)
      unfold E_rel_o in He. idestruct He as Hc1 _.
      idestruct Hc1.
      rewrite closed_lambda.
      assumption. }
    { unfold G_rel in Hγ.
      idestruct Hγ as Hcg1 Hγ. idestruct Hcg1.
      assumption. } }

  { apply (subst_map_closed'_3 (vlambda x e2) Γ γ2).
    { (* more repetition *)
      unfold E_rel_o in He. idestruct He as _ He. idestruct He as Hc2 _. idestruct Hc2.
      rewrite closed_lambda.
      assumption. }
    { unfold G_rel in Hγ.
      idestruct Hγ as Hcg1 Hγ. idestruct Hγ as Hcg2 Hγ. idestruct Hcg1. idestruct Hcg2.
      assumption. } }

  (* we now have the arguments *)
  iintros u1 u2 Hu1 Hu2 Hv.

  eapply R_rel_red_both.
  { simpl. eapply (Ectx_step _ _ ectx_hole _ _ eq_refl eq_refl).
    simpl. constructor.
    simpl. constructor.
    reflexivity. }
  { simpl. eapply (Ectx_step _ _ ectx_hole _ _ eq_refl eq_refl).
    simpl. constructor.
    simpl. constructor.
    reflexivity. }
  { later_shift.

    rewrite subst_subst_map with (Γ:=Γ).
    2: { pose proof (G_sub_closed _ _ _ _ Hγ) as [? _]. assumption. }
    rewrite subst_subst_map with (Γ:=Γ).
    2: { pose proof (G_sub_closed _ _ _ _ Hγ) as [_ ?]. assumption. }
    iapply He.
    apply (sem_context_rel_insert _ _ _ _ _ _ _ Hv Hγ). }
Qed.

(* R_rel_red_both *)
(* scope_weakening *)
(* subst_subst_map *)
(* closed_subst_extension *)
Print Assumptions compat_lam.
Print Assumptions subst_map_closed'_3.

Lemma fundamental_property_e Γ (e : expr) n :
  closed Γ e →
  n ⊨ E_rel_o Γ e e
with fundamental_property_v Γ (v : val) n :
  closed Γ v →
  n ⊨ V_rel_o Γ v v.
Proof.
  { intros H_closed.
    induction e.
    - apply compat_val. apply fundamental_property_v. assumption.
    - apply compat_var. rewrite closed_var. assumption.
    - rewrite closed_app in H_closed. destruct H_closed.
      apply compat_app; auto. }
  { intros H_closed.
    induction v.
    - admit.
    - apply compat_lam. apply fundamental_property_e. rewrite <- closed_lambda. assumption.
    - admit. }
Admitted.
