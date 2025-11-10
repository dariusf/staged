
From IxFree Require Import Lib Nat.
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

(* Record cexpr := mk_cexpr {
  cexpr_car :> expr;
  cexpr_closed : is_closed [] cexpr_car;
}.

Record cval := mk_cval {
  cval_car :> val;
  cval_closed : is_closed [] cval_car;
}.

Definition cval_to_cexpr (v:cval) : cexpr :=
  mk_cexpr (cval_car v) (cval_closed v).

Coercion cval_to_cexpr : cval >-> cexpr. *)

(* Definition cexpr_rel := cexpr ⇒ᵢ cexpr ⇒ᵢ IRel.
Definition cval_rel := cval ⇒ᵢ cval ⇒ᵢ IRel. *)

(* Definition cexpr_rel := .
Record cexpr_rel := mk_cexpr_rel {
  cexpr_rel_car :> expr ⇒ᵢ expr ⇒ᵢ IRel;
  cexpr_rel_closed e1 e2 : cexpr_rel_car e1 e2 → is_closed [] e1 ∧ is_closed [] e2;
}. *)

(* Relations *)

Definition expr_rel := expr ⇒ᵢ expr ⇒ᵢ IRel.
Definition val_rel := val ⇒ᵢ val ⇒ᵢ IRel.
Definition sub_rel := sub ⇒ᵢ sub ⇒ᵢ IRel.
Definition ctx_rel := ectx ⇒ᵢ ectx ⇒ᵢ IRel.

Definition L_rel_pre (L_rel:expr_rel) : expr_rel :=
  λ e1 e2,
    (closed [] e1)ᵢ →ᵢ (closed [] e2)ᵢ →ᵢ
    (∀ v1 : val, e1 = v1 → terminates e2)ᵢ ∧ᵢ
    ∀ᵢ e1' : expr, (base_step e1 e1')ᵢ →ᵢ ▷ L_rel e1' e2.

Lemma L_rel_pre_contractive : contractive L_rel_pre.
Proof.
  intro n; iintros; unfold L_rel_pre; auto_contr.
Qed.

Definition L_rel_fix := I_fix L_rel_pre.
Definition L_rel := L_rel_pre L_rel_fix.

Definition O_rel e1 e2 := L_rel e1 e2 ∧ᵢ L_rel e2 e1.

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

Definition K_rel_pre (V_rel : val_rel) (E1 E2 : ectx) :=
  ∀ᵢ v1 v2 : val,
    (closed [] v1)ᵢ →ᵢ (closed [] v2)ᵢ →ᵢ
    V_rel v1 v2 →ᵢ O_rel (fill E1 v1) (fill E2 v2).

Definition R_rel_pre (V_rel : val_rel) (e1 e2 : expr) :=
  ∀ᵢ E1 E2, ▷ K_rel_pre V_rel E1 E2 →ᵢ O_rel (fill E1 e1) (fill E2 e2).

Definition V_rel_pre (V_rel : val_rel) : val_rel :=
  λ v1 v2, (closed [] v1)ᵢ →ᵢ (closed [] v2)ᵢ →ᵢ
  ∀ᵢ (u1 u2:val), (closed [] u1)ᵢ →ᵢ (closed [] u2)ᵢ →ᵢ
    ▷ V_rel u1 u2 →ᵢ R_rel_pre V_rel (app v1 u1) (app v2 u2).

Definition V_rel_fix := I_fix V_rel_pre.

Definition V_rel := V_rel_pre V_rel_fix.
Definition R_rel := R_rel_pre V_rel_fix.
Definition K_rel := K_rel_pre V_rel_fix.

Definition E_rel (e1 e2 : expr) : IProp :=
  (closed [] e1)ᵢ →ᵢ (closed [] e2)ᵢ →ᵢ
  ∀ᵢ E1 E2 : ectx, K_rel E1 E2 →ᵢ
    O_rel (fill E1 e1) (fill E2 e2).

(* Relations for open terms *)

Definition G_rel (γ1 γ2 : sub) : IProp :=
  ∀ᵢ x v1 v2,
    (γ1 !! x = Some v1)ᵢ →ᵢ
    (γ2 !! x = Some v2)ᵢ →ᵢ
    V_rel v1 v2.

Definition E_rel_o (e1 e2 : expr) : IProp :=
  ∀ᵢ γ1 γ2, G_rel γ1 γ2 →ᵢ E_rel (subst_map γ1 e1) (subst_map γ2 e2).

Definition V_rel_o (v1 v2 : val) : IProp :=
  ∀ᵢ γ1 γ2, G_rel γ1 γ2 →ᵢ V_rel (subst_map_val γ1 v1) (subst_map_val γ2 v2).

(* Contractiveness and unrolling fixpoint *)

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

Lemma V_rel_intro (v1 v2 : val) n :
  n ⊨ ((closed [] v1)ᵢ →ᵢ (closed [] v2)ᵢ →ᵢ ∀ᵢ (u1 u2:val),
    (closed [] u1)ᵢ →ᵢ (closed [] u2)ᵢ →ᵢ
    ▷ V_rel u1 u2 →ᵢ R_rel (app v1 u1) (app v2 u2)) →
  n ⊨ V_rel v1 v2.
Proof.
  intros Hv.
  iintros Hcv1 Hcv2 u1 u2 Hcu1 Hcu2 Hl.
  iapply Hv; auto.
  later_shift. apply V_rel_unroll; assumption.
Qed.

Lemma V_rel_elim (v1 v2 u1 u2 : val) n :
  n ⊨ V_rel v1 v2 →
  n ⊨ (closed [] v1)ᵢ →
  n ⊨ (closed [] v2)ᵢ →
  n ⊨ (closed [] u1)ᵢ →
  n ⊨ (closed [] u2)ᵢ →
  n ⊨ ▷ V_rel u1 u2 →
  n ⊨ R_rel (app v1 u1) (app v2 u2).
Proof.
  intros Hv Hcv1 Hcv2 Hcu1 Hcu2 Hu.
  iapply Hv; auto.
  later_shift. apply V_rel_roll. assumption.
Qed.

Lemma K_rel_intro (E1 E2 : ectx) n :
  n ⊨ (∀ᵢ (v1 v2:val), (closed [] v1)ᵢ →ᵢ (closed [] v2)ᵢ →ᵢ
    V_rel v1 v2 →ᵢ O_rel (fill E1 v1) (fill E2 v2)) →
  n ⊨ K_rel E1 E2.
Proof.
  intro HE. iintros v1 v2 Hcv1 Hcv2 Hv. iapply HE; auto.
  apply V_rel_unroll; assumption.
Qed.

Lemma K_rel_elim (E1 E2 : ectx) (v1 v2 : val) n :
  n ⊨ K_rel E1 E2 →
  n ⊨ (closed [] v1)ᵢ →
  n ⊨ (closed [] v2)ᵢ →
  n ⊨ V_rel v1 v2 →
  n ⊨ O_rel (fill E1 v1) (fill E2 v2).
Proof.
  intros HE Hc1 Hc2 Hv. iapply HE; auto. apply V_rel_roll; assumption.
Qed.

Lemma R_rel_elim (e1 e2 : expr) E1 E2 n :
  n ⊨ R_rel e1 e2 →
  n ⊨ ▷ K_rel E1 E2 →
  n ⊨ O_rel (fill E1 e1) (fill E2 e2).
Proof.
  intros He HE; iapply He; assumption.
Qed.

(* this and K_rel together seem like the bind rule *)
Lemma E_rel_elim (e1 e2 : expr) E1 E2 n :
  n ⊨ E_rel e1 e2 →
  n ⊨ (closed [] e1)ᵢ →
  n ⊨ (closed [] e2)ᵢ →
  n ⊨ K_rel E1 E2 →
  n ⊨ O_rel (fill E1 e1) (fill E2 e2).
Proof.
  intros He Hc1 Hc2 HE. iapply He; auto.
Qed.

Lemma V_rel_elimE (v1 v2 u1 u2 : val) n :
  n ⊨ V_rel v1 v2 →
  n ⊨ (closed [] v1)ᵢ →
  n ⊨ (closed [] v2)ᵢ →
  n ⊨ (closed [] u1)ᵢ →
  n ⊨ (closed [] u2)ᵢ →
  n ⊨ V_rel u1 u2 →
  n ⊨ E_rel (app v1 u1) (app v2 u2).
Proof.
  intros Hv Hcv1 Hcv2 Hcu1 Hcu2 Hu. iintros Hc1 Hc2 E1 E2 HE.
  apply R_rel_elim. 2: { later_shift; assumption. }
  apply V_rel_elim; auto.
  later_shift; assumption.
Qed.

(* aka val inclusion *)
Lemma compat_val (v1 v2 : val) n :
  n ⊨ V_rel_o v1 v2 →
  n ⊨ E_rel_o v1 v2.
Proof.
  intro Hv. iintros γ1 γ2 Hγ Hc1 Hc2 E1 E2. iintros HE. simpl.
  apply K_rel_elim; auto.
  iapply Hv. assumption.
Qed.

Lemma closed_app xs e1 e2:
  closed xs (app e1 e2) ↔
  closed xs e1 ∧ closed xs e2.
Proof.
unfold closed. simpl.
  split.
  { intros.
    unfold closed in H.
    simpl in H.
    apply andb_prop_elim in H.
    assumption. }
  { intros [? ?].
    unfold closed. simpl.
    apply andb_prop_intro.
    firstorder. }
Qed.

Lemma compat_app (e1 e2 e1' e2' : expr) n :
  n ⊨ E_rel_o e1 e2 →
  n ⊨ E_rel_o e1' e2' →
  n ⊨ E_rel_o (app e1 e1') (app e2 e2').
Proof.
  intros He He'.
  iintros γ1 γ2 Hγ Hc1 Hc2 E1 E2. iintros HE.
  simpl.
  (* this only moves the subs *)
  pose proof (@E_rel_elim
    (subst_map γ1 e1)
    (subst_map γ2 e2)
    (ectx_app1 E1 (subst_map γ1 e1'))
    (ectx_app1 E2 (subst_map γ2 e2'))).
  simpl in H.
  apply H; clear H.
  { iapply He. assumption. }
  { idestruct Hc1.
    simpl in Hc1.
    apply closed_app in Hc1.
    iintro.
    destruct Hc1.
    assumption. }
  { idestruct Hc2.
    simpl in Hc2.
    apply closed_app in Hc2.
    iintro.
    destruct Hc2.
    assumption. }
  { apply K_rel_intro. iintros u₁ u₂ Hcu1 Hcu2 Hu. simpl.
    apply E_rel_elim with (E1 := ectx_app2 _ _) (E2 := ectx_app2 _ _).
    { iapply He'. assumption. }
    {
      (* TODO look into reflection *)
      (* Search (_ && _). *)
      (* Search "reflect". *)
      idestruct Hc1.
      iintro.
      unfold closed in *.
      (* apply Is_true_reflect. *)
      simpl in *.
      auto.
      simpl in Hc1.
      apply closed_app in Hc1.
      destruct Hc1.
      assumption. }
    { idestruct Hc2.
      simpl in Hc2.
      apply closed_app in Hc2.
      iintro.
      destruct Hc2.
      assumption. }
    apply K_rel_intro. iintros v1 v2 Hcv1 Hcv2 Hv.
    simpl.
    apply E_rel_elim.
    { apply V_rel_elimE; auto. }
    { idestruct Hcu1.
      idestruct Hcv1.
      iintro. apply closed_app.
      split; auto. }
    { idestruct Hcu2.
      idestruct Hcv2.
      iintro. apply closed_app.
      split; auto. }
    { assumption. } }
Qed.

Lemma closed_lambda e X x : closed X (vlambda x e) → closed (x :: X) e.
Proof.
  simpl.
  unfold closed. simpl.
  auto.
Qed.

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

Lemma compat_var (x : string) n :
  n ⊨ E_rel_o (var x) (var x).
Proof.
  iintros γ₁ γ₂ Hγ.
  (* Check E_rel_elim. *)
  unfold E_rel. iintros Hc1 Hc2 E1 E2 HK.



  (* simpl. *)
  (* applys V. *)

  (* unfold G_rel in Hγ. *)
  (* simpl in Hc1. *)
  (* simpl in *. *)
  (* apply G_rel_elim in Hγ. *)

  (* auto. *)
  idestruct Hc1.
  apply closed_subst_map in Hc1.
  destruct Hc1 as (v1&Hg1&?&?).

  idestruct Hc2.
  apply closed_subst_map in Hc2.
  destruct Hc2 as (v2&Hg2&?&?).

  unfold G_rel in Hγ.
  ispecialize Hγ x.
  ispecialize Hγ v1.
  ispecialize Hγ v2.
  (* Search ((_)ᵢ). *)
  apply I_prop_intro with (w:=n) in Hg1.
  apply I_prop_intro with (w:=n) in Hg2.

  (* iintro Hg1. *)
  (* ispecialize Hγ Hg1. *)

  iapply Hγ in Hg1. (* ? *)

  iapply Hg1 in Hg2.
  apply I_prop_intro with (w:=n) in H0.
  apply I_prop_intro with (w:=n) in H2.

  pose proof H0.
  pose proof H2.

  iapply Hg2 in H0.
  iapply H0 in H2.

  rewrite H.
  rewrite H1.

  apply K_rel_elim; auto.
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

Definition subst_is_closed (X : list string) (map : sub) :=
  ∀ x e, map !! x = Some e → closed X (ret e).

Lemma sem_context_rel_closed γ1 γ2 n:
  n ⊨ G_rel γ1 γ2 →
  subst_is_closed [] γ1 ∧ subst_is_closed [] γ2.
Proof.
  intros H.
  unfold G_rel in H.
  unfold subst_is_closed.
  split.
  {
    intros.
    ispecialize H x.
    admit.
  }
  (* iintros x. *)

admit.
  (* induction 1.
  - done.
  - intros y e. rewrite lookup_insert_Some.
    intros [[-> <-]|[Hne Hlook]].
    + by eapply val_rel_closed.
    + eapply IHsem_context_rel; last done. *)
(* Qed. *)
(* Abort. *)
Admitted.


Lemma subst_subst_map : ∀ (e:expr) (x : string) (es : val) (map : sub),
  subst_is_closed [] map
  → subst x es (subst_map (delete x map) e) =
    subst_map (insert x es map) e
with subst_subst_map_val : ∀ (v:val) (x : string) (es : val) (map : sub),
  subst_is_closed [] map
  → subst x es (subst_map_val (delete x map) v) =
    subst_map_val (insert x es map) v.
Proof.
{
  intros e. induction e; intros.
  {
    intros.
    simpl.
    apply (subst_subst_map_val _ _ _ _ H).
  }
  {
    intros. simpl.
    (* unfold subst_is_closed in H. *)
    destruct (decide (x0=x)) as [->|Hne].
    -
    (* Unset Printing Notations. Set Printing Coercions. Set Printing Parentheses. *)
    rewrite lookup_delete_eq with (m:=map).
    rewrite lookup_insert_eq with (m:=map).
    simpl.
    by rewrite decide_True.
    (* // lookup_insert_eq //. simpl. *)
    -
    (* destruct x0. *)
    (* + *)
    (* x0 is anon *)
    (* simpl. *)
    (* reflexivity. *)
    (* + *)
    rewrite lookup_delete_ne with (m:=map).
      2: {
        (* Unset Printing Notations. Set Printing Coercions. Set Printing Parentheses. *)
        (* simplify_eq. *)
        (* inj *)
        (* discriminate . *)
        (* Search (not (eq (_ _) (_ _))). *)

        (* injection Hne. apply Hne. *)
        admit.
      }
      rewrite lookup_insert_ne with (m:=map).
      simpl.

        admit.
      (* reflexivity. *)

admit.
  }
  {
  admit.
  }

}
{
  intros v. induction v; intros.
  admit.
  admit.
  admit.
}

Admitted.

(* Lemma subst_map_closed X e xs :
  closed X e →
  (∀ x : string, x ∈ dom xs → x ∉ X) →
  subst_map xs e = e.
Proof.
Admitted. *)

Lemma sem_context_rel_insert x v1 v2 γ1 γ2 n:
  n ⊨ V_rel v1 v2 →
  n ⊨ G_rel γ1 γ2 →
  n ⊨ G_rel (<[x := v1]> γ1) (<[x := v2]> γ2).
Proof.
Admitted.

Lemma rel_v_compat_lam (e1 e2 : expr) n x :
  n ⊨ E_rel_o e1 e2 →
  n ⊨ V_rel_o (vlambda x e1) (vlambda x e2).
Proof.
  intro He.
  unfold V_rel_o. iintros γ1 γ2 Hγ.
  apply V_rel_intro. iintros Hce1 Hce2 u1 u2 Hcu1 Hcu2 Hv.
  simpl in *.
  idestruct Hce1.
  idestruct Hce2.
  idestruct Hcu1.
  idestruct Hcu2.

  eapply R_rel_red_both.
  - constructor.
    simpl. constructor.
    reflexivity.
  - constructor.
    simpl. constructor.
    reflexivity.
  - later_shift.
    rewrite subst_subst_map. 2: { apply (sem_context_rel_closed _ _ _ Hγ). }
    rewrite subst_subst_map. 2: { apply (sem_context_rel_closed _ _ _ Hγ). }
    iapply He.
    destruct x.
    (* { simpl in *.
      assumption. } *)
    { simpl in *.
      apply sem_context_rel_insert.
      assumption.
      assumption. }
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
