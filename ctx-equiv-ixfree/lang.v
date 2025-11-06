
From CtxEquivIris Require Import persistent_pred.

From IxFree Require Import Lib Nat.

(* From iris.prelude Require Import options.
From iris.base_logic Require Import invariants bi algebra.
From iris.heap_lang Require Import proofmode. *)
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

Inductive ectx :=
  | HoleCtx
  | AppLCtx (K: ectx) (v2 : val)
  | AppRCtx (e1 : expr) (K: ectx)
  | PlusLCtx (K: ectx) (v2 : val)
  | PlusRCtx (e1 : expr) (K: ectx)
  .

Fixpoint fill (K : ectx) (e : expr) : expr :=
  match K with
  | HoleCtx => e
  | AppLCtx K v2 => app (fill K e) (of_val v2)
  | AppRCtx e1 K => app e1 (fill K e)
  | PlusLCtx K v2 => eplus (fill K e) (of_val v2)
  | PlusRCtx e1 K => eplus e1 (fill K e)
  end.

(* filling a context with another context *)
Fixpoint comp_ectx (Ko Ki: ectx) :=
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



(* Section logrel.
Context `{heapGS Σ}.

(* Definition valO := leibnizO val.
Definition exprO := leibnizO expr.
Definition evctxO := leibnizO ectx. *)

(* Definition val_rel := valO -n> valO -n> iProp Σ.
Definition ctx_rel := evctxO -n> evctxO -n> iProp Σ.
Definition expr_rel := exprO -n> exprO -n> iProp Σ. *)

Definition val_rel := persistent_pred (val * val) (iPropI Σ).
Definition expr_rel := persistent_pred (expr * expr) (iPropI Σ).
Definition evctx_rel := persistent_pred (ectx * ectx) (iPropI Σ).

Definition val_relO := persistent_predO (val * val) (iPropI Σ).
Definition expr_relO := persistent_predO (expr * expr) (iPropI Σ).
Definition evctx_relO := persistent_predO (ectx * ectx) (iPropI Σ).

Definition mk_val_rel (pred : (val * val) → iProp Σ) {Pers : ∀ v, Persistent (pred v)} : val_rel :=
  @PersPred _ _ pred Pers.
Global Instance val_rel_pers (τ : val_relO) : ∀ v, Persistent (τ v) := _.

Definition mk_expr_rel (pred : (expr * expr) → iProp Σ) {Pers : ∀ e, Persistent (pred e)} : expr_rel :=
  @PersPred _ _ pred Pers.
Global Instance expr_rel_pers (τ : expr_relO) : ∀ e, Persistent (τ e) := _.

Definition mk_evctx_rel (pred : (ectx * ectx) → iProp Σ) {Pers : ∀ E, Persistent (pred E)} : evctx_rel :=
  @PersPred _ _ pred Pers.
Global Instance evctx_rel_pers (τ : evctx_relO) : ∀ E, Persistent (τ E) := _.

(* Print val_rel_pers. *)

(* Locate "<pers>". *)

(* Definition semtypeO := persistent_predO val (iPropI Σ). *)
*)


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

Fixpoint is_closed (X : list string) (e : expr) : bool :=
  match e with
  | var x => bool_decide (x ∈ X)
  | evalue vunit | evalue (vint _) => true
  | evalue (vlambda x e) => is_closed (x :b: X) e
  | app e1 e2 | eplus e1 e2 => is_closed X e1 && is_closed X e2
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

Definition expr_rel := expr ⇒ᵢ expr ⇒ᵢ IRel.
Definition val_rel := val ⇒ᵢ val ⇒ᵢ IRel.
Definition sub_rel := sub ⇒ᵢ sub ⇒ᵢ IRel.
Definition ctx_rel := ectx ⇒ᵢ ectx ⇒ᵢ IRel.
(* Definition Obs_sig := expr ⇒ᵢ expr ⇒ᵢ IRel. *)

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
(* Definition L_rel := I_fix L_rel_pre. *)

Definition O_rel e₁ e₂ := L_rel e₁ e₂ ∧ᵢ L_rel e₂ e₁.

(* ========================================================================= *)

Lemma L_rel_roll p₁ p₂ n :
  n ⊨ L_rel p₁ p₂ → n ⊨ L_rel_fix p₁ p₂.
Proof.
  intro H; iapply (I_fix_roll expr_rel); [ | exact H ].
  apply L_rel_pre_contractive.
Qed.

Lemma L_rel_unroll p₁ p₂ n :
  n ⊨ L_rel_fix p₁ p₂ → n ⊨ L_rel p₁ p₂.
Proof.
  intro H; iapply (I_fix_unroll expr_rel); [ | exact H ].
  apply L_rel_pre_contractive.
Qed.

Definition K_rel_pre (V_rel : val_rel) (E₁ E₂ : ectx) :=
  ∀ᵢ v1 v2 : val,
    (closed [] v1)ᵢ →ᵢ (closed [] v2)ᵢ →ᵢ
    V_rel v1 v2 →ᵢ O_rel (fill E₁ v1) (fill E₂ v2).

Definition R_rel_pre (V_rel : val_rel) (e₁ e₂ : expr) :=
  ∀ᵢ E₁ E₂, ▷ K_rel_pre V_rel E₁ E₂ →ᵢ O_rel (fill E₁ e₁) (fill E₂ e₂).

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

(* ========================================================================= *)
(* Open relations *)

Definition G_rel (γ1 γ2 : sub) : IProp :=
  ∀ᵢ x v1 v2,
    (γ1 !! x = Some v1)ᵢ →ᵢ
    (γ2 !! x = Some v2)ᵢ →ᵢ
    V_rel v1 v2.

Definition E_rel_o (e₁ e₂ : expr) : IProp :=
  ∀ᵢ γ₁ γ₂, G_rel γ₁ γ₂ →ᵢ E_rel (subst_map γ₁ e₁) (subst_map γ₂ e₂).

Definition V_rel_o (v₁ v₂ : val) : IProp :=
  ∀ᵢ γ₁ γ₂, G_rel γ₁ γ₂ →ᵢ V_rel (subst_map_val γ₁ v₁) (subst_map_val γ₂ v₂).

(* Definition rel_p (p₁ p₂ : expr) : IProp :=
  ∀ᵢ γ₁ γ₂, G_rel γ₁ γ₂ →ᵢ O_rel (bind γ₁ p₁) (bind γ₂ p₂). *)

(* ========================================================================= *)
(* Contractiveness and urolling fixpoint *)

Lemma V_rel_pre_contractive : contractive V_rel_pre.
Proof.
  intro n; iintros; unfold V_rel_pre, R_rel_pre, K_rel_pre; auto_contr.
Qed.

Lemma V_rel_roll v₁ v₂ n :
  n ⊨ V_rel v₁ v₂ → n ⊨ V_rel_fix v₁ v₂.
Proof.
  intro H; iapply (I_fix_roll val_rel); [ | exact H ].
  apply V_rel_pre_contractive.
Qed.

Lemma V_rel_unroll v₁ v₂ n :
  n ⊨ V_rel_fix v₁ v₂ → n ⊨ V_rel v₁ v₂.
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

Lemma K_rel_intro (E₁ E₂ : ectx) n :
  n ⊨ (∀ᵢ (v₁ v₂:val), (closed [] v₁)ᵢ →ᵢ (closed [] v₂)ᵢ →ᵢ
    V_rel v₁ v₂ →ᵢ O_rel (fill E₁ v₁) (fill E₂ v₂)) →
  n ⊨ K_rel E₁ E₂.
Proof.
  intro HE. iintros v₁ v₂ Hcv1 Hcv2 Hv. iapply HE; auto.
  apply V_rel_unroll; assumption.
Qed.

Lemma K_rel_elim (E₁ E₂ : ectx) (v₁ v₂ : val) n :
  n ⊨ K_rel E₁ E₂ →
  n ⊨ (closed [] v₁)ᵢ →
  n ⊨ (closed [] v₂)ᵢ →
  n ⊨ V_rel v₁ v₂ →
  n ⊨ O_rel (fill E₁ v₁) (fill E₂ v₂).
Proof.
  intros HE Hc1 Hc2 Hv. iapply HE; auto. apply V_rel_roll; assumption.
Qed.

Lemma R_rel_elim (e₁ e₂ : expr) E₁ E₂ n :
  n ⊨ R_rel e₁ e₂ →
  n ⊨ ▷ K_rel E₁ E₂ →
  n ⊨ O_rel (fill E₁ e₁) (fill E₂ e₂).
Proof.
  intros He HE; iapply He; assumption.
Qed.

Lemma E_rel_elim (e₁ e₂ : expr) E₁ E₂ n :
  n ⊨ E_rel e₁ e₂ →
  n ⊨ (closed [] e₁)ᵢ →
  n ⊨ (closed [] e₂)ᵢ →
  n ⊨ K_rel E₁ E₂ →
  n ⊨ O_rel (fill E₁ e₁) (fill E₂ e₂).
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
  intros Hv Hcv1 Hcv2 Hcu1 Hcu2 Hu. iintros Hc1 Hc2 E₁ E₂ HE.
  (* idestruct Hc1. *)
  (* idestruct Hc2. *)
  apply R_rel_elim. 2: { later_shift; assumption. }
  apply V_rel_elim; auto.
  later_shift; assumption.
Qed.

Lemma compat_val (v₁ v₂ : val) n :
  n ⊨ V_rel_o v₁ v₂ →
  n ⊨ E_rel_o v₁ v₂.
Proof.
  intro Hv. iintros γ₁ γ₂ Hγ Hc1 Hc2 E₁ E₂. iintros HE. simpl.
  apply K_rel_elim; auto.
  iapply Hv. assumption.
Qed.

Lemma compat_app (e₁ e₂ e₁' e₂' : expr) n :
  n ⊨ E_rel_o e₁ e₂ →
  n ⊨ E_rel_o e₁' e₂' →
  n ⊨ E_rel_o (app e₁ e₁') (app e₂ e₂').
Proof.
  intros He He'.
  iintros γ₁ γ₂ Hγ E₁ E₂ HE.
  (* term_simpl. *)
  (* Check E_rel_intro. *)
  pose proof E_rel_elim.
  (* apply E_rel_elim. *)
  (* apply (E_rel_elim _ _ (AppRCtx _ _) (AppRCtx _ _)). *)
  (* eapply (E_rel_elim _ _ (AppLCtx _ _) (AppLCtx _ _)). *)
  (* eapply E_rel_elim with (E₁ := AppRCtx _ _) (E₂ := AppRCtx _ _). *)
    (* [ *)
     - simpl.

     Print K_rel_pre.
     iapply He. assumption.
      (* | ]. *)
  apply K_rel_intro; iintros v₁ v₂ Hv.
  apply E_rel_elim with (E₁ := ectx_app2 _ _) (E₂ := ectx_app2 _ _);
    [ iapply He'; assumption | ].
  apply K_rel_intro; iintros u₁ u₂ Hu; simpl.
  iapply V_rel_elimE; assumption.
Qed.

(* Lemma rel_e_compat_callcc {V : Set} (e₁ e₂ : expr (inc V)) n :
  n ⊨ E_rel e₁ e₂ →
  n ⊨ E_rel (e_callcc e₁) (e_callcc e₂).
Proof.
  intro He.
  iintros γ₁ γ₂ Hγ E₁ E₂ HE; term_simpl.
  eapply Obs_red_both; [ auto_red | auto_red | ]; later_shift.
  unfold subst; repeat rewrite bind_bind_comp'.
  iapply He; [ | eassumption ].
  iintro x; destruct x as [ | x ]; term_simpl; [ | iapply Hγ ].
  apply V_rel_intro; iintros u₁ u₂ Hu F₁ F₂ HF.
  eapply Obs_red_both; [ auto_red | auto_red | ]; later_shift; term_simpl.
  eapply Obs_red_both; [ auto_red | auto_red | ]; later_shift; term_simpl.
  apply K_rel_elim; assumption.
Qed.

Lemma rel_e_compat_abort {V : Set} (p₁ p₂ : program V) n :
  n ⊨ rel_p p₁ p₂ →
  n ⊨ E_rel (e_abort p₁) (e_abort p₂).
Proof.
  intro Hp.
  iintros γ₁ γ₂ Hγ E₁ E₂ HE; term_simpl.
  eapply Obs_red_both; [ auto_red | auto_red | ]; later_shift; term_simpl.
  iapply Hp; assumption.
Qed. *)


Lemma rel_v_compat_var {V : Set} (x : V) n :
  n ⊨ rel_v (v_var x) (v_var x).
Proof.
  iintros γ₁ γ₂ Hγ; iapply Hγ.
Qed.

Lemma rel_v_compat_lam {V : Set} (e₁ e₂ : expr (inc V)) n :
  n ⊨ E_rel e₁ e₂ →
  n ⊨ rel_v (v_lam e₁) (v_lam e₂).
Proof.
  intro He;
  iintros γ₁ γ₂ Hγ; term_simpl.
  apply V_rel_intro; iintros u₁ u₂ Hu.
  eapply R_rel_red_both; [ auto_red | auto_red | ]; later_shift; term_simpl.
  unfold subst; repeat rewrite bind_bind_comp'.
  iapply He.
  iintro x; destruct x as [ | x ]; term_simpl.
  + assumption.
  + iapply Hγ.
Qed.

(* ========================================================================= *)
(* programs *)

Lemma rel_p_compat_expr {V : Set} (e₁ e₂ : expr V) n :
  n ⊨ E_rel e₁ e₂ →
  n ⊨ rel_p e₁ e₂.
Proof.
  intro He.
  iintros γ₁ γ₂ Hγ; term_simpl.
  apply E_rel_elim with (E₁ := ectx_hole) (E₂ := ectx_hole).
  + iapply He; assumption.
  + apply K_rel_intro; iintros v₁ v₂ Hv; apply Obs_value.
Qed.

Fixpoint fundamental_property_e {V : Set} (e : expr V) n :
  n ⊨ E_rel e e
with fundamental_property_v {V : Set} (v : value V) n :
  n ⊨ rel_v v v
with fundamental_property_p {V : Set} (p : program V) n :
  n ⊨ rel_p p p.
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
Qed.

(* Definition F_ObsL (ObsL : Obs_sig) : Obs_sig :=
  λ p₁ p₂,
  (∀ v₁ : val, p₁ = v₁ → terminates p₂)ᵢ ∧ᵢ
  ∀ᵢ p₁' : program ∅, (red p₁ p₁')ᵢ →ᵢ ▷ ObsL p₁' p₂. *)

(*

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
    ∀ (E1 E2:ectx), □ (▷ K_rel_pre V_rel (E1, E2) →
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
    ∀ (E1 E2:ectx), □ (K_rel (E1, E2) →
      O_rel (fill E1 e.1, fill E2 e.2)))%I.

(* open relations *)

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

Lemma K_rel_elim (E1 E2 : ectx) (v1 v2 : val) :
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

Lemma K_rel_elim1 (E1 E2 : ectx) (v1 v2 : val) :
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

  (* Check K_rel_elim1. *)
  (* iUnfold V_rel_o in "Hv". *)

  (* iPoseProof (K_rel_elim1 $! E1 E2 with "[HE]") as "H1". *)
 (* g2 v1 v2 with "HE" *)
  (* iAssert K_rel_elim as "H1". *)
  (* iSpecialize (K_rel_elim). *)

  iApply K_rel_elim1.
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

End logrel. *)
