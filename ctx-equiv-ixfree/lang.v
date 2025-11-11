
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
    ∀ᵢ e1' : expr, (base_step e1 e1')ᵢ →ᵢ ▷ L_rel e1' e2.

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
  ∀ᵢ γ1 γ2, G_rel Γ γ1 γ2 →ᵢ E_rel (subst_map γ1 e1) (subst_map γ2 e2).

Definition V_rel_o (Γ: list string) (v1 v2 : val) : IProp :=
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

(* aka val inclusion *)
Lemma compat_val (Γ : list string) (v1 v2 : val) n :
  n ⊨ V_rel_o Γ v1 v2 →
  n ⊨ E_rel_o Γ v1 v2.
Proof.
  unfold V_rel_o, E_rel_o. simpl.
  intro Hv.
  iintros γ1 γ2 Hγ.
  ispecialize Hv γ1. ispecialize Hv γ2. ispec Hv Hγ.
  apply V_rel_elim in Hv as (H_closed1 & H_closed2 & Hv).
  apply E_rel_intro.
  { exact H_closed1. }
  { exact H_closed2. }
  iintros E1 E2 HE.
  apply (K_rel_elim E1 E2 _ _ _ HE).
  apply V_rel_intro.
  { exact H_closed1. }
  { exact H_closed2. }
  { exact Hv. }
Qed.

Lemma closed_app xs e1 e2:
  closed xs (app e1 e2) ↔
  closed xs e1 ∧ closed xs e2.
Proof. unfold closed. simpl. by rewrite -> andb_True. Qed.

Lemma compat_app (Γ:list string) (e1 e2 e1' e2' : expr) n :
  n ⊨ E_rel_o Γ e1 e2 →
  n ⊨ E_rel_o Γ e1' e2' →
  n ⊨ E_rel_o Γ (app e1 e1') (app e2 e2').
Proof.
  unfold E_rel_o. simpl.
  intros He He'. iintros γ1 γ2 Hγ.
  ispecialize He γ1. ispecialize He γ2. ispec He Hγ.
  ispecialize He' γ1. ispecialize He' γ2. ispec He' Hγ.
  apply E_rel_elim in He as (Hc1 & Hc2 & He).
  (* From He, we have:
     - closed-ness of e1
     - closed-ness of e2
     - contextual equivalence of e1 and e2, in related context *)
  apply E_rel_elim in He' as (Hc1' & Hc2' & He').
  apply E_rel_intro.
  { rewrite closed_app. auto. } (* closed-ness: subst_map γ1 (app e1 e1') is closed *)
  { rewrite closed_app. auto. } (* closed-ness: subst_map γ2 (app e2 e2') is closed *)
  iintros E1 E2 HE.
  (* e1/e2 are evaluated first. We "zap" then down using He.
     We consider the contexts surround e1 and e2, and we are left
     with showing that the surrounding contexts are related *)
  ispecialize He (ectx_app1 E1 (subst_map γ1 e1')).
  ispecialize He (ectx_app1 E2 (subst_map γ2 e2')).
  iapply He.
  (* after e1/e2 are fully evaluated, we are left with `ectx_app1 E1 e1'` and
     `ectx_app1 E2 e2'`. Using K_rel_intro, we "assume" that e1 and e2 evaluated
     to two related values v1 and v2, respectively; and then we prove that the
     two contexts are related *)
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

Lemma closed_lambda e X x : closed X (vlambda x e) → closed (x :: X) e.
Proof. auto. Qed.

Fixpoint subst_val_closed v X x es :
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
        apply closed_lambda in H0.
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

Lemma G_sub_closed n Γ γ1 γ2:
  n ⊨ G_rel Γ γ1 γ2 →
  subst_is_closed Γ [] γ1 ∧ subst_is_closed Γ [] γ2.
Proof.
  unfold G_rel. intros.
  split.
  - unfold subst_is_closed. intros x Hdom.
    idestruct H as Hc1 _. idestruct Hc1.
    unfold subst_is_closed in Hc1.
    apply (Hc1 x Hdom).
  - unfold subst_is_closed. intros x Hdom.
    idestruct H as _ H. idestruct H as Hc2 _. idestruct Hc2.
    unfold subst_is_closed in Hc2.
    apply (Hc2 x Hdom).
Qed.

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

(* Lemma subst_closed_nil e x es : closed [] e → subst x es e = e.
Proof.
  intros. apply subst_closed with []; set_solver.
Qed. *)

Lemma closed_subst_map γ x:
  closed [] (subst_map γ (var x)) →
  ∃ v, γ !! x = Some v ∧ subst_map γ (var x) = ret v ∧ closed [] v.
Proof.
  intros.
  unfold closed in H.
  unfold subst_map in H.
  destruct (γ !! x) eqn:H1. 2: { simpl in H. inversion H. }
  exists v.
  split; [ | split ].
  - reflexivity.
  - simpl. rewrite H1. reflexivity.
  - unfold closed. assumption.
Qed.

Lemma compat_var Γ (x : string) n :
  x ∈ Γ →
  n ⊨ E_rel_o Γ (var x) (var x).
Proof.
  intros Hdom.
  iintros γ₁ γ₂ Hγ.
  apply E_rel_intro.
  { apply G_sub_closed in Hγ as [Hc1 Hc2].
    apply (subst_is_closed_closed_subst_map _ _ _ Hdom Hc1). }
  { apply G_sub_closed in Hγ as [Hc1 Hc2].
    apply (subst_is_closed_closed_subst_map _ _ _ Hdom Hc2). }

  (* TODO use an elim principle for G_rel *)
  iintros E1 E2 HE. simpl.
  unfold G_rel in Hγ.
  idestruct Hγ as Hc1 Hγ.
  idestruct Hγ as Hc2 H.
  idestruct Hc1.
  idestruct Hc2.
  unfold subst_is_closed in Hc1.
  specialize (Hc1 x Hdom).
  destruct Hc1 as (v&?&?).
  specialize (Hc2 x Hdom).
  destruct Hc2 as (v0&?&?).
  rewrite H0. rewrite H2.

  ispec H x v v0 H0 H4.

  apply K_rel_elim.
  assumption.
  assumption.
Qed.

Lemma R_rel_red_both (e₁ e₁' e₂ e₂' : expr) n :
  (* contextual_step e₁ e₁' → contextual_step e₂ e₂' → *)
  base_step e₁ e₁' → base_step e₂ e₂' →
  n ⊨ ▷ E_rel e₁' e₂' →
  n ⊨ R_rel e₁ e₂.
Proof.
  (* intros Hred₁ Hred₂ He; iintros E₁ E₂ HE.
  eapply Obs_red_both.
  + apply red_in_ectx; eassumption.
  + apply red_in_ectx; eassumption.
  + later_shift; iapply He; assumption. *)
(* Qed. *)
Admitted.

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

Lemma subst_subst_map : ∀ Γ (e:expr) (x : string) (es : val) (map : sub),
  subst_is_closed Γ [] map →
  subst x es (subst_map (delete x map) e) =
  subst_map (insert x es map) e
with subst_subst_map_val : ∀ Γ (v:val) (x : string) (es : val) (map : sub),
  subst_is_closed Γ [] map →
  subst x es (subst_map_val (delete x map) v) =
  subst_map_val (insert x es map) v.
Proof.
Admitted.

  (* { intros e. induction e; intros; simpl.
    { apply (subst_subst_map_val _ _ _ _ H). }
    { (* the variable case *)
      destruct (decide (x0=x)) as [->|Hne].
      { rewrite lookup_delete_eq with (m:=map).
        rewrite lookup_insert_eq with (m:=map).
        simpl.
        by rewrite decide_True. }
      { rewrite lookup_delete_ne with (m:=map). 2: { assumption. }
        rewrite lookup_insert_ne with (m:=map). 2: { assumption. }
        destruct (map !! x) as [v1|] eqn:Hkey.
        { Fail rewrite Hkey. (* why does regular rewrite not work? *)
          setoid_rewrite Hkey.
          simpl.
          rewrite (subst_val_closed _ [] _ _).
          - reflexivity.
          - apply (H _ _ Hkey).
          - set_solver. }
      { setoid_rewrite Hkey.
        simpl.
        by rewrite decide_False. } } }
    { simpl. f_equal.
      apply IHe1. assumption.
      apply IHe2. assumption. } }
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
        apply subst_subst_map.
        apply (subst_is_closed_subseteq _ _ map).
        apply delete_subseteq.
        assumption. } }
    { reflexivity. } }
Qed. *)

Lemma sem_context_rel_insert Γ x v1 v2 γ1 γ2 n:
  n ⊨ V_rel v1 v2 →
  n ⊨ G_rel Γ γ1 γ2 →
  n ⊨ G_rel (x :: Γ) (<[x := v1]> γ1) (<[x := v2]> γ2).
Proof.
(* Admitted. *)
Abort.

  (* intros.
  unfold G_rel.
  isplit; [ | isplit ].
  { apply G_sub_closed in H0 as [? ?].
    iintro.
    pose proof (subst_is_closed_subseteq Γ [] γ1 (insert x v1 γ1)).
    apply H2.
    Search (_ ⊆ insert _ _ _).
    apply insert_subseteq.
    (* set_solver. *)

    }
  (* { apply G_sub_closed in H0 as [? ?].
    iintro.
    pose proof (subst_is_closed_subseteq Γ [] γ1 (insert x v1 γ1)).
    apply H2.
    set_solver.
    assumption. } *)
  {
    admit.
  }
  {
    admit.
  } *)

  (* iintros x0 v0 v3 H1 H2.
  destruct (decide (x=x0)).
  { subst.
    rewrite lookup_insert_eq with (m:=γ2) in H2. idestruct H2. injection H2 as ->.
    rewrite lookup_insert_eq with (m:=γ1) in H1. idestruct H1. injection H1 as ->.
    assumption. }
  { rewrite lookup_insert_ne with (m:=γ2) in H2. idestruct H2. 2: { assumption. }
    rewrite lookup_insert_ne with (m:=γ1) in H1. idestruct H1. 2: { assumption. }
    unfold G_rel in H0.
    ispecialize H0 x0.
    ispecialize H0 v0.
    ispecialize H0 v3.
    iapply H0.
    - iintro. apply H1.
    - iintro. apply H2. } *)
(* Qed. *)

Lemma rel_v_compat_lam Γ (e1 e2 : expr) n x :
  n ⊨ E_rel_o Γ e1 e2 →
  n ⊨ V_rel_o Γ (vlambda x e1) (vlambda x e2).
Proof.
  intro He.
  unfold V_rel_o. iintros γ1 γ2 Hγ.
  apply V_rel_intro.

  simpl.
  (* Search (closed). *)

  (* { apply G_sub_closed in Hγ as [Hc1 Hc2].
    apply (subst_is_closed_closed_subst_map _ _ _ Hdom Hc1). } *)
  { admit. }
  { admit. }

  iintros u1 u2 Hcu1 Hcu2 Hv.
  simpl.
  (* simpl in *. *)
  (* idestruct Hce1. *)
  (* idestruct Hce2. *)
  idestruct Hcu1.
  idestruct Hcu2.
  eapply R_rel_red_both.
  { constructor.
    simpl. constructor.
    reflexivity. }
  { constructor.
    simpl. constructor.
    reflexivity. }
  { later_shift.
    rewrite subst_subst_map with (Γ:=Γ).
    2: { pose proof (G_sub_closed _ _ _ _ Hγ) as [? _]. assumption. }
    rewrite subst_subst_map with (Γ:=Γ).
    2: { pose proof (G_sub_closed _ _ _ _ Hγ) as [_ ?]. assumption. }
    iapply He.
    (* apply (sem_context_rel_insert _ _ _ _ _ _ _ Hv Hγ). } *)
Abort.

(* Fixpoint fundamental_property_e {V : Set} (e : expr V) n :
  n ⊨ E_rel e e
with fundamental_property_v {V : Set} (v : value V) n :
  n ⊨ rel_v v v.
Proof.
+ destruct e.
  - apply rel_e_compat_value, fundamental_property_v.
  - apply compat_app; apply fundamental_property_e.
  - apply rel_e_compat_callcc, fundamental_property_e.
  -  apply rel_e_compat_abort, fundamental_property_p.
+ destruct v.
  - apply rel_v_compat_var.
  - apply rel_v_compat_lam, fundamental_property_e.
+ destruct p.
  - apply rel_p_compat_expr, fundamental_property_e.
Qed. *)
