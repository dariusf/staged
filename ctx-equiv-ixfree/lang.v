
From IxFree Require Import Lib Nat.
From CtxEquivIxFree Require Import ixfree_tactics.
From CtxEquivIxFree Require Import tactics.
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
  (* TODO reenable context tests when this is restored *)
  (*| vint (z : Z) *)
  | vlambda (x : string) (e: expr)
  (* | vbool (b : bool) *)
  (* | vloc (l : loc) *)
  (* | vunit *).

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
  (*| vunit => vunit
  | vint n => vint n*)
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

Fixpoint ectx_comp (E1 E2 : ectx) : ectx :=
  match E1 with
  | ectx_hole => E2
  | ectx_app1 E1 e => ectx_app1 (ectx_comp E1 E2) e
  | ectx_app2 v E1 => ectx_app2 v (ectx_comp E1 E2)
  end.

Notation fill := plug.

Lemma ectx_comp_correct :
  ∀ E1 E2 e, plug E1 (plug E2 e) = plug (ectx_comp E2 E1) e.
Proof.
  intros E1 E2.
  induction E2; intros e'.
  - simpl in *. reflexivity.
  - simpl in *. rewrite (IHE2 (app e' e)). reflexivity.
  - simpl in *. rewrite (IHE2 (app v e')). reflexivity.
Qed.

(** Outside-in evaluation contexts *)
(*
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
*)

Inductive contextual_step (e1 : expr) (e2 : expr) : Prop :=
  Ectx_step K e1' e2' :
    e1 = fill K e1' →
    e2 = fill K e2' →
    base_step e1' e2' →
    contextual_step e1 e2.

Definition contextual_reducible (e : expr) :=
  ∃ e', contextual_step e e'.

Definition bigstep e1 (v:val) :=
  ∃ e2, rtc contextual_step e1 e2 /\ to_val e2 = Some v.

Definition terminates e := ∃ v, bigstep e v.

Definition equiterminate e1 e2 := terminates e1 <-> terminates e2.

Definition obs_eqv e1 e2 :=
  ∀ C, equiterminate (fill C e1) (fill C e2).

Infix "≈" := equiterminate (at level 80, right associativity, only printing).
Infix "≡obs" := obs_eqv (at level 80, right associativity, only printing).

Lemma contextual_step_comp :
  ∀ K e1 e2,
    contextual_step e1 e2 →
    contextual_step (fill K e1) (fill K e2).
Proof.
  intros K e1 e2 H_step.
  inversion H_step. subst. econstructor.
  - by apply ectx_comp_correct.
  - by apply ectx_comp_correct.
  - assumption.
Qed.

Notation name := string.
Definition sub : Set := gmap name val.
Definition scope : Set := gset name.

Fixpoint subst_map_val (xs : sub) (v : val) : val :=
  match v with
  (*| vunit => vunit
  | vint n => vint n*)
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

Fixpoint is_closed (X : scope) (e : expr) : bool :=
  match e with
  | var x => bool_decide (x ∈ X)
  (*| ret vunit | ret (vint _) => true*)
  | ret (vlambda x e) => is_closed (X ∪ {[x]}) e
  | app e1 e2
  (* | eplus e1 e2 *)
  => is_closed X e1 && is_closed X e2
  end.

(* aka a scoping judgment, the untyped equivalent of a typing judgment *)
Definition closed (X : scope) (e : expr) : Prop := Is_true (is_closed X e).

Definition ectx_is_closed (X : scope) (E : ectx) :=
  ∀ e, closed ∅ e → closed X (fill E e).

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
    (*- constructor.*)
    - unfold closed in *.
      simpl in *.
      apply (closed_weaken e _ _ H).
      set_solver.
    (*- constructor.*) }
Qed.

Lemma closed_subst :
  ∀ Γ x e1 e2,
    closed (Γ ∪ {[x]}) e1 →
    closed ∅ e2 →
    closed Γ (subst x e2 e1)
with closed_subst_val :
  ∀ Γ x (v : val) e,
    closed (Γ ∪ {[x]}) v →
    closed ∅ e →
    closed Γ (subst_val x e v).
Proof.
  {
    unfold closed in *.
    intros Γ x e1 e2 H_closed1 H_closed2.
    induction e1.
    - simpl in *. auto.
    - simpl in *.
      rewrite -> decide_bool_decide.
      destruct (bool_decide_reflect (x = x0)) as [H_eq | H_neq].
      + eapply closed_weaken.
        exact H_closed2.
        set_solver.
      + simpl in *.
        apply bool_decide_unpack in H_closed1.
        apply bool_decide_pack.
        set_solver.
    - simpl in *.
      apply andb_prop_elim in H_closed1 as [Hc1 Hc2].
      apply andb_prop_intro. split.
      + exact (IHe1_1 Hc1).
      + exact (IHe1_2 Hc2).
  }
  {
    unfold closed in *.
    intros Γ x v e H_closed1 H_closed2.
    induction v.
    (* - simpl in *. auto. *)
    - simpl in *.
      rewrite -> decide_bool_decide.
      destruct (bool_decide_reflect (x = x0)) as [H_eq | H_neq].
      + rewrite -> H_eq in H_closed1.
        eapply closed_weaken.
        exact H_closed1. set_solver.
      + simpl in *.
        apply closed_subst.
        eapply closed_weaken.
        exact H_closed1. set_solver.
        exact H_closed2.
    (*- simpl in *. auto.*)
  }
Qed.

Lemma closed_app xs e1 e2:
  closed xs (app e1 e2) ↔
  closed xs e1 ∧ closed xs e2.
Proof. unfold closed. simpl. by rewrite andb_True. Qed.

Lemma closed_lambda e X x : closed X (vlambda x e) ↔ closed (X ∪ {[x]}) e.
Proof. split. auto. auto. Qed.

Lemma closed_var Γ x : x ∈ Γ ↔ closed Γ (var x).
Proof. unfold closed. simpl. by rewrite bool_decide_spec. Qed.

Lemma base_step_preserve_closedness :
  ∀ e1 e1',
    base_step e1 e1' →
    closed ∅ e1 →
    closed ∅ e1'.
Proof.
  unfold closed.
  intros e1 e1' Hred H_closed.
  inversion Hred. subst. simpl in *.
  apply andb_prop_elim in H_closed as [Hc1 Hc2].
  exact (closed_subst ∅ x e0 e2 Hc1 Hc2).
Qed.

Lemma closed_decompose :
  ∀ E e,
    closed ∅ (fill E e) →
    ectx_is_closed ∅ E ∧ closed ∅ e.
Proof.
  unfold ectx_is_closed.
  intros E.
  induction E; intros e' H_closed.
  - simpl in *. auto.
  - simpl in *.
    apply IHE in H_closed as [H_fill H_closed].
    apply closed_app in H_closed as [H_closed1 H_closed2].
    split.
    + intros e'' H_closed3.
      apply H_fill.
      apply closed_app. auto.
    + auto.
  - simpl in *.
    apply IHE in H_closed as [H_fill H_closed].
    apply closed_app in H_closed as [H_closed1 H_closed2].
    split.
    + intros e'' H_closed3.
      apply H_fill.
      apply closed_app. auto.
    + auto.
Qed.

Lemma closed_compose :
  ∀ E e,
    ectx_is_closed ∅ E →
    closed ∅ e →
    closed ∅ (fill E e).
Proof. unfold ectx_is_closed. auto. Qed.

Lemma contextual_step_preserve_closedness :
  ∀ e1 e1',
    contextual_step e1 e1' →
    closed ∅ e1 →
    closed ∅ e1'.
Proof.
  unfold closed.
  intros e1 e1' Hred H_closed.
  inversion Hred. subst. simpl in *. clear Hred.
  apply closed_decompose in H_closed as [H_closed1 H_closed2].
  apply (base_step_preserve_closedness _ _ H1) in H_closed2.
  apply closed_compose; auto.
Qed.

(** subscoped from Erlang paper *)
Definition subst_is_closed (Γ free : scope) (sub : sub) :=
  Γ = dom sub ∧
  ∀ x, x ∈ Γ →
    ∀ v, sub !! x = Some v → closed free (ret v).

Lemma subst_is_closed_subseteq: ∀ (Γ1 Γ2 X : scope) (γ1 γ2: sub),
  Γ1 = dom γ1 →
  γ1 ⊆ γ2 → Γ1 ⊆ Γ2 → subst_is_closed Γ2 X γ2 → subst_is_closed Γ1 X γ1.
Proof.
  intros * Hd Hγ HΓ Hclosed2.
  destruct Hclosed2 as [Hd2 Hc2].
  split.
  assumption.
  intros x Hl v Hs.
  rewrite (map_subseteq_spec γ1 γ2) in Hγ.
  (* specialize (Hγ _ _ Hs). *)
  specialise Hγ Hs.
  apply (Hc2 x ltac:(set_solver) _ Hγ).
Qed.

(* Relations *)

Definition expr_rel := expr ⇒ᵢ expr ⇒ᵢ IRel.
Definition val_rel := val ⇒ᵢ val ⇒ᵢ IRel.
Definition sub_rel := sub ⇒ᵢ sub ⇒ᵢ IRel.
Definition ctx_rel := ectx ⇒ᵢ ectx ⇒ᵢ IRel.

Definition L_rel_pre (L_rel : expr_rel) : expr_rel :=
  λ e1 e2,
    (closed ∅ e1)ᵢ ∧ᵢ
    (closed ∅ e2)ᵢ ∧ᵢ
    (∀ v1 : val, e1 = v1 → terminates e2)ᵢ ∧ᵢ
    ∀ᵢ e1' : expr, (contextual_step e1 e1')ᵢ →ᵢ ▷ L_rel e1' e2.

Definition L_rel_fix := I_fix L_rel_pre.
Definition L_rel := L_rel_pre L_rel_fix.
Definition O_rel e1 e2 := L_rel e1 e2 ∧ᵢ L_rel e2 e1.

Definition K_rel_pre (V_rel : val_rel) :=
  λ E1 E2,
    (ectx_is_closed ∅ E1)ᵢ ∧ᵢ
    (ectx_is_closed ∅ E2)ᵢ ∧ᵢ
    (∀ᵢ (v1 v2 : val),
      V_rel v1 v2 →ᵢ
      O_rel (fill E1 v1) (fill E2 v2)).

Definition R_rel_pre (V_rel : val_rel) (e1 e2 : expr) :=
  ∀ᵢ E1 E2,
    (ectx_is_closed ∅ E1)ᵢ →ᵢ
    (ectx_is_closed ∅ E2)ᵢ →ᵢ
    ▷ K_rel_pre V_rel E1 E2 →ᵢ O_rel (fill E1 e1) (fill E2 e2).

Definition V_rel_pre (V_rel : val_rel) : val_rel :=
  λ v1 v2,
    (closed ∅ v1)ᵢ ∧ᵢ
    (closed ∅ v2)ᵢ ∧ᵢ
    ∀ᵢ (u1 u2 : val),
      (closed ∅ u1)ᵢ →ᵢ
      (closed ∅ u2)ᵢ →ᵢ
      ▷ V_rel u1 u2 →ᵢ
      R_rel_pre V_rel (app v1 u1) (app v2 u2).

Definition V_rel_fix := I_fix V_rel_pre.

Definition V_rel := V_rel_pre V_rel_fix.
Definition R_rel := R_rel_pre V_rel_fix.
Definition K_rel := K_rel_pre V_rel_fix.

Definition E_rel : expr_rel :=
  λ e1 e2,
    (closed ∅ e1)ᵢ ∧ᵢ
    (closed ∅ e2)ᵢ ∧ᵢ
    ∀ᵢ E1 E2 : ectx, K_rel E1 E2 →ᵢ O_rel (fill E1 e1) (fill E2 e2).

(* Relations for open terms *)

Definition G_rel (Γ: scope) (γ1 γ2 : sub) : IProp :=
  (subst_is_closed Γ ∅ γ1)ᵢ ∧ᵢ
  (subst_is_closed Γ ∅ γ2)ᵢ ∧ᵢ
  ∀ᵢ x v1 v2,
    (γ1 !! x = Some v1)ᵢ →ᵢ
    (γ2 !! x = Some v2)ᵢ →ᵢ
    V_rel v1 v2.

Definition E_rel_o (Γ: scope) (e1 e2 : expr) : IProp :=
  (closed Γ e1)ᵢ ∧ᵢ
  (closed Γ e2)ᵢ ∧ᵢ
  ∀ᵢ γ1 γ2, G_rel Γ γ1 γ2 →ᵢ E_rel (subst_map γ1 e1) (subst_map γ2 e2).

Definition V_rel_o (Γ: scope) (v1 v2 : val) : IProp :=
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
  closed ∅ v1 →
  closed ∅ v2 →
  (n ⊨ ∀ᵢ (u1 u2:val),
        (closed ∅ u1)ᵢ →ᵢ
        (closed ∅ u2)ᵢ →ᵢ
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
  closed ∅ v1 ∧
  closed ∅ v2 ∧
  (n ⊨ (∀ᵢ (u1 u2 : val),
         (closed ∅ u1)ᵢ →ᵢ
         (closed ∅ u2)ᵢ →ᵢ
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
  ectx_is_closed ∅ E1 →
  ectx_is_closed ∅ E2 →
  n ⊨ (∀ᵢ v1 v2, V_rel v1 v2 →ᵢ O_rel (fill E1 v1) (fill E2 v2)) →
  n ⊨ K_rel E1 E2.
Proof.
  intros Hc1 Hc2 HE.
  unfold K_rel, K_rel_pre.
  repeat isplit.
  - iintro. exact Hc1.
  - iintro. exact Hc2.
  - iintros v1 v2 Hv.
    iapply HE. apply V_rel_unroll. exact Hv.
Qed.

Lemma K_rel_elim (E1 E2 : ectx) n :
  n ⊨ K_rel E1 E2 →
  ectx_is_closed ∅ E1 ∧
  ectx_is_closed ∅ E2 ∧
  (n ⊨ ∀ᵢ v1 v2, V_rel v1 v2 →ᵢ O_rel (fill E1 v1) (fill E2 v2)).
Proof.
  unfold K_rel, K_rel_pre.
  intros HE.
  idestruct HE as Hc1 HE. idestruct Hc1.
  idestruct HE as Hc2 HE. idestruct Hc2.
  split; [| split].
  - exact Hc1.
  - exact Hc2.
  - iintros v1 v2 Hv.
    iapply HE. apply V_rel_roll. exact Hv.
Qed.

Lemma K_rel_elimO E1 E2 v1 v2 n :
  n ⊨ K_rel E1 E2 →
  n ⊨ V_rel v1 v2 →
  n ⊨ O_rel (fill E1 v1) (fill E2 v2).
Proof.
  intros HE Hv.
  apply K_rel_elim in HE as (_ & _ & HE).
  iapply HE. exact Hv.
Qed.

Lemma R_rel_intro (e1 e2 : expr) n :
  n ⊨ (∀ᵢ E1 E2,
        (ectx_is_closed ∅ E1)ᵢ →ᵢ
        (ectx_is_closed ∅ E2)ᵢ →ᵢ
        ▷ K_rel E1 E2 →ᵢ O_rel (fill E1 e1) (fill E2 e2)) ->
  n ⊨ R_rel e1 e2.
Proof. auto. Qed.

Lemma R_rel_elim (e1 e2 : expr) E1 E2 n :
  n ⊨ R_rel e1 e2 →
  ectx_is_closed ∅ E1 →
  ectx_is_closed ∅ E2 →
  n ⊨ ▷ K_rel E1 E2 →
  n ⊨ O_rel (fill E1 e1) (fill E2 e2).
Proof.
  intros He Hc1 Hc2 HE.
  unfold R_rel, R_rel_pre in He.
  iapply He.
  - iintro. exact Hc1.
  - iintro. exact Hc2.
  - exact HE.
Qed.

Lemma E_rel_intro (e1 e2 : expr) n :
  closed ∅ e1 →
  closed ∅ e2 →
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
  closed ∅ e1 ∧
  closed ∅ e2 ∧
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
  destruct (K_rel_elim _ _ _ HE) as (HE1_closed & HE2_closed & _).
  apply R_rel_elim.
  - iapply Hv'.
    + iintro. assumption.
    + iintro. assumption.
    + later_shift. exact Hu.
  - exact HE1_closed.
  - exact HE2_closed.
  - later_shift. exact HE.
Qed.

Lemma G_rel_intro Γ γ1 γ2 n :
  subst_is_closed Γ ∅ γ1 →
  subst_is_closed Γ ∅ γ2 →
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
  - iintro. exact H_closed1.
  - iintro. exact H_closed2.
  - exact Hγ.
Qed.

Lemma G_rel_elim Γ γ1 γ2 n :
  n ⊨ G_rel Γ γ1 γ2 →
  subst_is_closed Γ ∅ γ1 ∧
  subst_is_closed Γ ∅ γ2 ∧
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
Lemma compat_val (Γ : scope) (v1 v2 : val) n :
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
  apply (K_rel_elimO E1 E2 _ _ _ HE).
  apply V_rel_intro.
  { exact H_closed1. }
  { exact H_closed2. }
  { exact Hv. }
Qed.

Lemma closed_ectx_app1 :
  ∀ E e,
    ectx_is_closed ∅ E →
    closed ∅ e →
    ectx_is_closed ∅ (ectx_app1 E e).
Proof.
  intros E e Hc1 Hc2.
  unfold ectx_is_closed in *.
  intros e' Hc3. simpl.
  apply Hc1. apply closed_app. auto.
Qed.

Lemma closed_ectx_app2 :
  ∀ (v : val) E,
    closed ∅ v →
    ectx_is_closed ∅ E →
    ectx_is_closed ∅ (ectx_app2 v E).
Proof.
  intros v E Hc1 Hc2.
  unfold ectx_is_closed in *.
  intros e' Hc3. simpl.
  apply Hc2. apply closed_app. auto.
Qed.

Lemma compat_app (Γ:scope) (e1 e2 e1' e2' : expr) n :
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
  destruct (K_rel_elim _ _ _ HE) as (HEc1 & HEc2 & _).
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
  apply K_rel_intro.
  { by apply closed_ectx_app1. }
  { by apply closed_ectx_app1. }
  iintros v1 v2 Hv. simpl.
  destruct (V_rel_elim _ _ _ Hv) as (Hvc1 & Hvc2 & _).
  (* e1'/e2' are evaluated. We "zap" then down using He' *)
  ispecialize He' (ectx_app2 v1 E1).
  ispecialize He' (ectx_app2 v2 E2).
  iapply He'.
  apply K_rel_intro.
  { by apply closed_ectx_app2. }
  { by apply closed_ectx_app2. }
  iintros v1' v2' Hv'. simpl.
  (* Now, we "zap" (app v1 v1') and (app v2 v2') down using E_rel_elimO *)
  apply E_rel_elimO.
  apply V_rel_elimE; [exact Hv | exact Hv'].
  (* Finally, we are left with just E1 and E2. They are related according
     to our hypothesis *)
  exact HE.
Qed.

Lemma subst_is_closed_elim_closed Γ (γ:sub) x X (v:val):
  subst_is_closed Γ X γ →
  γ !! x = Some v →
  closed X v.
Proof.
  intros [Hdom Hsc] He.
  assert (H := elem_of_dom_2 _ _ _ He).
  (* have: elem_of_dom_2 He. *)
  (* pose proof (elem_of_dom_2 _ _ _ He). *)
  assert (x ∈ Γ). set_solver.
  apply (Hsc x H0 v He).
Qed.

Lemma subst_is_closed_closed_subst_map Γ γ x:
  x ∈ Γ →
  subst_is_closed Γ ∅ γ →
  closed ∅ (subst_map γ (var x)).
Proof.
  intros Hxg Hsc.
  pose proof Hsc.
  unfold subst_is_closed, closed in H.
  simpl.
  destruct (γ !! x) eqn:He.
  - (* if x is in γ, it must be closed according to the premise *)
    apply (subst_is_closed_elim_closed _ _ _ _ _ Hsc He).
  - (* absurd *)
    destruct H.
    pose proof (not_elem_of_dom_2 _ _ He).
    set_solver.
Qed.

Lemma subset_is_closed_absurd x Γ γ:
  x ∈ Γ →
  subst_is_closed Γ ∅ γ →
  γ !! x = None →
  False.
Proof.
  intros Hx Hs He.
  pose proof (not_elem_of_dom_2 _ _ He).
  destruct Hs as [? _].
  setoid_rewrite <- H0 in H.
  set_solver.
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
  destruct (γ1 !! x) eqn:Hx1.
  2: { destruct (subset_is_closed_absurd _ _ _ Hdom Hc1 Hx1). }
  destruct (γ2 !! x) eqn:Hx2.
  2: { destruct (subset_is_closed_absurd _ _ _ Hdom Hc2 Hx2). }
  destruct Hc1 as [_ Hc1].
  destruct Hc2 as [_ Hc2].
  ispec Hγ x v v0 Hx1 Hx2.
  by apply K_rel_elimO.
Qed.

Lemma G_sub_closed Γ γ1 γ2 n :
  n ⊨ G_rel Γ γ1 γ2 →
  subst_is_closed Γ ∅ γ1 ∧ subst_is_closed Γ ∅ γ2.
Proof. intros Hγ. apply G_rel_elim in Hγ. easy. Qed.

Lemma subst_val_closed v X x es :
  closed X (of_val v) → x ∉ X → subst_val x es v = v
with subst_closed X e x es :
  closed X e → x ∉ X → subst x es e = e.
Proof.
  { induction v.
    (*{ reflexivity. }*)
    { simpl.
      case_decide.
      - reflexivity.
      - intros.
        f_equal.
        rewrite closed_lambda in H0.
        apply (subst_closed _ _ _ _ H0).
        set_solver. }
    (*{ reflexivity. }*) }
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

Lemma not_base_step_val : ∀ (v : val) e, ¬ base_step v e.
Proof. intros v e Hstep. inversion Hstep. Qed.

Lemma val_eq_fill_inv : ∀ (v : val) K e, ret v = fill K e → e = v ∧ K = ectx_hole.
Proof.
  intros v K.
  induction K; intros e' H_eq. simpl in *.
  - auto.
  - specialize (IHK _ H_eq) as (H_absurd & _). discriminate.
  - specialize (IHK _ H_eq) as (H_absurd & _). discriminate.
Qed.

Lemma not_contextual_step_val : ∀ (v : val) e, ¬ contextual_step v e.
Proof.
  intros v e Hstep.
  inversion Hstep.
  apply val_eq_fill_inv in H as [-> ->].
  by eapply not_base_step_val.
Qed.

Lemma base_step_is_deterministic :
  ∀ e1 e2 e3,
    base_step e1 e2 →
    base_step e1 e3 →
    e2 = e3.
Proof.
  intros e1 e2 e3 Hstep2 Hstep3.
  inversion Hstep2.
  inversion Hstep3.
  congruence.
Qed.

Lemma unique_decomposition :
  ∀ E1 E2 e1 e2 e1' e2',
    base_step e1 e1' →
    base_step e2 e2' →
    fill E1 e1 = fill E2 e2 →
    E1 = E2 ∧ e1 = e2.
Proof.
  intros E1 E2 e1 e2 e1' e2' Hstep1 Hstep2.
  revert E2.
  induction E1; intros E2 Heq; simpl in *.
  - destruct E2.
    + simpl in *. auto.
    + simpl in *. (* e1 is not a potential redex *) admit.
    + simpl in *. admit.
  - destruct E2.
    + simpl in *. admit.
    + simpl in *. admit.
    + simpl in *. admit.
Admitted. (* hard *)

Lemma contextual_step_is_deterministic :
  ∀ e1 e2 e3,
    contextual_step e1 e2 →
    contextual_step e1 e3 →
    e2 = e3.
Proof.
  intros e1 e2 e3 Hstep2 Hstep3.
  inversion Hstep2.
  inversion Hstep3.
  destruct (unique_decomposition K K0 e1' e1'0 e2' e2'0 H1 H4) as [HK_eq He_eq].
  { congruence. }
  rewrite -> He_eq in H1.
  assert (He_eq' := base_step_is_deterministic e1'0 e2' e2'0 H1 H4).
  congruence.
Qed.

Lemma L_rel_red_l (e1 e1' e2 : expr) n :
  closed ∅ e1 →
  closed ∅ e2 →
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
    exfalso. by eapply not_contextual_step_val.
  - iintros e1'' Hred'.
    idestruct Hred'.
    replace e1'' with e1' by admit. (* deterministic *)
    later_shift. apply L_rel_roll.
    exact HL.
Admitted.

Lemma L_rel_red_r (e2 e2' : expr) n :
  (*closed [] e1 →*)
  closed ∅ e2 →
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
    Print bigstep.
    unfold bigstep in *.
    destruct HL1 as (v & e3 & Hrtc & H_terminates).
    exists v, e3. split.
    + eapply rtc_l. exact Hred. exact Hrtc.
    + exact H_terminates.
  - iintros e1' Hred'.
    ispec HL2 e1' Hred'.
    later_shift.
    apply L_rel_unroll in HL2.
    apply L_rel_roll.
    iapply IH. exact HL2.
Qed.

Lemma O_rel_red_l (e1 e1' e2 : expr) n :
  closed ∅ e1 →
  closed ∅ e2 →
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
  closed ∅ e1 →
  closed ∅ e2 →
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
  closed ∅ e1 →
  closed ∅ e2 →
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
    { by eapply contextual_step_preserve_closedness. }
    { exact Hred1. }
    { later_shift. exact HL1. }
  - iapply L_rel_red_r.
    { exact Hc1. }
    { exact Hred1. }
    iapply L_rel_red_l.
    { exact Hc2. }
    { by eapply contextual_step_preserve_closedness. }
    { exact Hred2. }
    { later_shift. exact HL2. }
Qed.

(* Observation: later_shift is significant in O_rel_red_both,
   but is not significant in O_rel_red_l and O_rel_red_r. We
   hypothesize that O_rel_red_l and O_rel_red_r are stronger
   property:
   - O_rel_red_both → O_rel_red_l ∧ O_rel_red_r
   - But not: O_rel_red_l ∧ O_rel_red_r → O_rel_red_both *)

Lemma R_rel_red_both (e1 e1' e2 e2' : expr) n :
  closed ∅ e1 →
  closed ∅ e2 →
  contextual_step e1 e1' →
  contextual_step e2 e2' →
  n ⊨ ▷ E_rel e1' e2' →
  n ⊨ R_rel e1 e2.
Proof.
  intros Hc1 Hc2 Hred1 Hred2 He.
  apply R_rel_intro.
  iintros E1 E2 HEc1 HEc2 HE. idestruct HEc1. idestruct HEc2.
  eapply O_rel_red_both.
  { by apply HEc1. } (* need: closed-ness for context *)
  { by apply HEc2. }
  { by apply contextual_step_comp. }
  { by apply contextual_step_comp. }
  { later_shift. by apply E_rel_elimO. }
Qed.

(* composition of subst and subst_map,
  where the variable to be substituted doesn't appear in the substitution *)
Lemma subst_subst_map : ∀ (e:expr) Γ (x : string) (es : val) (map : sub),
  subst_is_closed Γ ∅ map →
  subst x es (subst_map (delete x map) e) =
  subst_map (insert x es map) e
with subst_subst_map_val : ∀ (v:val) Γ (x : string) (es : val) (map : sub),
  subst_is_closed Γ ∅ map →
  subst x es (subst_map_val (delete x map) v) =
  subst_map_val (insert x es map) v.
Proof.
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
          rewrite (subst_val_closed _ ∅ _ _).
          - reflexivity.
          - apply (subst_is_closed_elim_closed _ _ x _ _ H Hkey).
          - set_solver. }
      { setoid_rewrite Hkey.
        simpl.
        by rewrite decide_False. } } }
    { intros. simpl. f_equal; eauto. } }
  { intros v. induction v; intros.
    (*{ reflexivity. }*)
    { (* the lambda case *)
      simpl. f_equal. f_equal.
      case_decide.
      { subst.
        rewrite delete_delete_eq with (m:=map).
        rewrite delete_insert_eq with (m:=map). done. }
      { rewrite delete_insert_ne with (m:=map). 2: { congruence. }
        rewrite delete_delete with (m:=map).
        eapply subst_subst_map.
        apply (subst_is_closed_subseteq (Γ ∖ {[x]}) Γ _ (delete x map) map).
        destruct H as [H1 H2].
        rewrite H1.
        set_solver.
        apply delete_subseteq.
        set_solver.
        assumption. } }
    (*{ reflexivity. }*) }
Qed.

(** Special case of Theorem A.1 from Erlang paper:
  scoping of extended substitutions.
  Given a closed substitution, we can add a closed value to it. *)
Lemma scope_extend1 Γ x (v:val) (γ:sub):
  closed ∅ v →
  subst_is_closed Γ ∅ γ →
  subst_is_closed (Γ ∪ {[x]}) ∅ (<[x := v]> γ).
Proof.
  intros Hc Hsc.
  split.
  { destruct Hsc. rewrite H. set_solver. }
  intros x0 Hd v0 Hs.
  (* we have to prove that for an arbitrary binding x0 := v0 in γ, v0 is closed *)
  destruct (decide (x=x0)) as [->|Hne].
  (* if x = x0, the premise tells us v0 is closed *)
  { rewrite lookup_insert_eq with (m:=γ) in Hs.
    injection Hs. intros. subst.
    exact Hc. }
  (* if they are not equal, we know x0 is in Γ and have to use the fact
    that the subst_is_closed *)
  { rewrite elem_of_union in Hd. destruct Hd. 2: { assert (x0 = x). set_solver. done. }
    destruct Hsc as [_ Hsc].
    rewrite lookup_insert_ne with (m:=γ) in Hs. 2: { assumption. }
    specialize (Hsc x0 H v0 Hs).
    assumption. }
Qed.

(* we can extend related substitutions with related values *)
Lemma sem_context_rel_insert Γ x v1 v2 γ1 γ2 n:
  n ⊨ V_rel v1 v2 →
  n ⊨ G_rel Γ γ1 γ2 →
  n ⊨ G_rel (Γ ∪ {[x]}) (<[x := v1]> γ1) (<[x := v2]> γ2).
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

(* if e is closed under Y, we can split the variables in Y between X and γ *)
Lemma subst_map_closed' e X Y (γ:sub):
  closed Y e →
  (∀ x, x ∈ Y → match γ !! x with Some v0 => closed X (ret v0) | None => x ∈ X end) →
  closed X (subst_map γ e)
with subst_map_closed'_val v X Y (γ:sub):
  closed Y (ret v) →
  (∀ x, x ∈ Y → match γ !! x with Some v0 => closed X (ret v0) | None => x ∈ X end) →
  closed X (subst_map_val γ v).
Proof.
  {
    revert X Y γ. induction e.
    { eapply subst_map_closed'_val; eauto. }
    { intros * Hc H.
      (* e is a variable x *)
      unfold closed in Hc; simpl in Hc; apply bool_decide_unpack in Hc.
      specialize (H x Hc).
      (* it is closed, so we can use H *)
      simpl.
      destruct (γ !! x) eqn:He.
      - assumption.
      - unfold closed; simpl; apply bool_decide_pack. assumption.
    }
    { intros *.
      unfold closed. simpl.
      rewrite !andb_True. intros [? ?] **.
      split.
      by eapply IHe1.
      by eapply IHe2. }
  }
  { revert X Y γ. induction v.
    (*{ intros. assumption. }*)
    { unfold closed. simpl.
      intros * Hce H.
      eapply subst_map_closed'. eassumption.
      intros y [|]%elem_of_union.
      { destruct (decide (x = y)).
        { by subst; rewrite lookup_delete_eq with (m:=γ); set_solver. }
        rewrite lookup_delete_ne with (m:=γ). 2: { assumption. }
        eapply H in H0.
        destruct lookup; last set_solver.
        eapply closed_weaken; eauto with set_solver. }
      { rewrite elem_of_singleton in H0.
        subst. rewrite lookup_delete_eq with (m:=γ). set_solver. }
    }
    (*{ intros. assumption. }*) }
Qed.

(* simple corollary of [subst_map_closed'],
  where we have split Y into X and dom γ upfront *)
Corollary subst_map_closed'_2 Γ X γ e :
  closed (X ∪ (dom γ)) e ->
  subst_is_closed Γ X γ ->
  closed X (subst_map γ e).
Proof.
  intros Hcl Hsubst.
  eapply subst_map_closed'; first eassumption.
  intros x Hx.
  destruct (γ !! x) as [e'|] eqn:Heq.
  - apply (subst_is_closed_elim_closed _ _ _ _ _ Hsubst Heq).
  - apply not_elem_of_dom in Heq.
    set_solver.
Qed.

(* given a value and a substitution closed under the same scope,
  applying the substitution gives us a completely closed value *)
Lemma subst_map_closed'_3 (v:val) Γ γ:
  closed Γ v ->
  subst_is_closed Γ ∅ γ ->
  closed ∅ (subst_map γ v).
Proof.
  pose proof (subst_map_closed'_2 Γ ∅ γ v).
  simpl in H.
  intros.
  apply H. 2: { assumption. }
  destruct H1 as [? _].
  rewrite <- H1.
  replace (∅ ∪ Γ) with Γ. assumption.
  set_solver.
Qed.

Lemma lambda_closed Γ γ x e :
  closed (Γ ∪ {[x]}) e  →
  subst_is_closed Γ ∅ γ  →
  closed ∅ (vlambda x (subst_map (delete x γ) e)).
Proof.
  intros Hec [Heq Hγc].
  rewrite closed_lambda.
  eapply subst_map_closed'_2.
  - eapply closed_weaken.
    exact Hec.
    setoid_rewrite dom_delete.
    intros y. destruct (decide (x = y)); set_solver.
  - apply (subst_is_closed_subseteq (Γ ∖ {[x]}) Γ _ (delete x γ) γ).
    + set_solver.
    + apply delete_subseteq.
    + set_solver.
    + unfold subst_is_closed. split.
      * exact Heq.
      * intros x' Hin v Hlookup.
        specialize (Hγc x' Hin v Hlookup).
        by eapply closed_weaken.
Qed.

Lemma compat_lambda Γ (e1 e2 : expr) n x :
  n ⊨ E_rel_o (Γ ∪ {[x]}) e1 e2 →
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
  idestruct Hu1.
  idestruct Hu2.
  destruct (E_rel_o_elim _ _ _ _ He) as (Hec1 & Hec2 & He').
  destruct (G_rel_elim _ _ _ _ Hγ) as (Hγc1 & Hγc2 & Hγ').

  eapply R_rel_red_both.
  { simpl. rewrite closed_app. by eauto using lambda_closed. }
  { simpl. rewrite closed_app. by eauto using lambda_closed. }
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
    (* 2: { pose proof (G_sub_closed _ _ _ _ Hγ) as [_ ?]. assumption. } *)
    2: { have: G_sub_closed Hγ. done. }
    rewrite subst_subst_map with (Γ:=Γ).
    2: { pose proof (G_sub_closed _ _ _ _ Hγ) as [_ ?]. assumption. }
    iapply He.
    (* apply (sem_context_rel_insert _ _ _ _ _ _ _ Hv Hγ). *)
    applyy sem_context_rel_insert Hv Hγ. }
Qed.

(* Print Assumptions compat_lambda. *)

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
    - apply compat_lambda. apply fundamental_property_e. rewrite <- closed_lambda. assumption. }
Qed.
