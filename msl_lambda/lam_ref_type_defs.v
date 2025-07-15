(*
 * Copyright (c) 2009 Robert Dockins and Aquinas Hobor.
 *
 *)

(* Coq development: using indirection theory to model types in l-calculus *)

(* lam_ref_type_defs.v: the definition of the type system; this is the main event. *)

Require Import msl_lambda.lam_ref_tcb.
Require Import msl_lambda.lam_ref_mach_defs.
Require Import msl.msl_standard.

Require Export msl_lambda.lam_ref_type_prelim.

Open Scope pred.

(* From introduction; this is the judgment psi |- v : tau *)
Definition forces (psi : mtype) (v : value) (tau : pred world) :=
  tau (psi, v).

(* Section 4.1, equation 17 *)
Program Definition ty_nat : pred world :=
  fun w => match w with (k, v) =>
    exists n, v = v_Nat n
  end.
Next Obligation.
  destruct a; destruct a'.
  replace v0 with v; auto.
  assert (necR (m,v) (m0,v0)).
  apply rt_step; auto.
  rewrite value_knot_necR in H1.
  intuition.
Qed.

Lemma ty_nat_extends :
  boxy extendM ty_nat.
Proof.
  apply boxy_i.
  apply R_extends_refl.
  simpl; intros.
  destruct w; destruct w'; destruct H; subst.
  auto.
Qed.

Program Definition type_at (l:addr) (tau:pred world) : pred world :=
  fun w:world =>
    let (n,psi) := unsquash (fst w) in
      match psi l with
        | None => False
        | Some p => approx_eq n p tau
      end.
Next Obligation.
  unfold age, age1 in H.
  destruct a; destruct a'.
  simpl in *.
  rewrite knot_age1 in H.
  case_eq (unsquash m); intros; rewrite H1 in H, H0.
  destruct n; try discriminate.
  inv H.
  rewrite unsquash_squash.
  unfold fmap, option_map, compose.
  case_eq (f l); intros; rewrite H in H0.
  unfold approx_eq in *.
  change (approx n (approx n p)) with
    ((approx n oo approx n) p).
  rewrite <- (approx_approx1 0).
  rewrite (approx_approx1 1).
  unfold compose; simpl.
  rewrite H0; auto.
  auto.
Qed.

Lemma type_at_extends : forall l tau,
  %(type_at l tau) = type_at l tau.
Proof.
  intros; apply boxy_i.
  apply R_extends_refl.
  intros; simpl in *.
  destruct w; destruct w'.
  destruct H; subst; simpl in *.
  case_eq (unsquash m); intros; rewrite H1 in H0.
  case_eq (unsquash m0); intros.
  hnf in H.
  rewrite H1 in H; rewrite H2 in H.
  destruct H; subst.
  destruct (H3 l).
  rewrite H in H0; elim H0.
  rewrite H.
  auto.
Qed.

Program Definition just (v:value) : pred world :=
  fun w => snd w = v.
Next Obligation.
  destruct a; destruct a'; simpl in *.
  hnf in H; simpl in H.
  rewrite knot_age1 in H.
  case_eq (unsquash m); intros; rewrite H1 in H.
  destruct n; inv H; auto.
Qed.

Program Definition with_val (v:value) (p:pred world) : pred world :=
  fun w => p (fst w,v).
Next Obligation.
  apply pred_hereditary with (fst a,v).
  unfold age, age1 in *; simpl in *.
  rewrite knot_age1 in *.
  destruct a; destruct a'; simpl in *.
  case_eq (unsquash m); intros; rewrite H1 in H; auto.
  destruct n; inv H; auto.
  auto.
Qed.

Definition ty_ref (tau: pred world) : pred world :=
  Ex_ a:addr, just (v_Loc a) && type_at a tau.

(* Section 5.1, equation 28 *)
Program Definition mtype_valid (m : mem) : pred world :=
  fun w =>
  match w with (k, v) =>
   let (n,phi) := unsquash k in
    forall (a : addr),
      match phi a with
      | None => fst m <= a
      | Some tau => fst m > a /\ forces k (deref m a) (%|>(mkPred tau))
      end
  end.
Next Obligation.
  unfold age, age1 in H.
  simpl in H.
  rewrite knot_age1 in H.
  destruct a; destruct a'.
  simpl in *.
  case_eq (unsquash m0); intros; rewrite H1 in H.
  destruct n; try discriminate.
  inv H.
  rewrite H1 in H0.
  rewrite unsquash_squash; intros.
  unfold fmap, option_map, compose.
  spec H0 a.
  case_eq (f a); intros.
  rewrite H in H0.
  intuition.
  split; auto.
  apply lt_le_trans with (level (fst a')).
  change (level x' < level a').
  apply laterR_level.
  apply Rt_Rft_trans with a'0; auto.
  destruct a'; destruct H0.
  hnf in H0.
  rewrite unsquash_squash in H0.
  simpl; rewrite knot_level.
  case_eq (unsquash m1); intros; rewrite H7 in H0.
  destruct H0; subst.
  simpl; auto.
  assert ((%|>(mkPred p)) (m0,deref m a)); auto.
  rewrite later_commute in H6.
  eapply H6.
  2: apply H0.
  hnf; apply t_step.
  unfold age, age1; simpl.
  rewrite knot_age1.
  rewrite H1; auto.
  apply rt_trans with a'0; auto.
  apply Rt_Rft; auto.
  rewrite H in H0.
  auto.
Qed.

Definition expr_typeF (tau:pred world) (F: expr -> pred world) (e : expr) : pred world :=
  %All_ m:mem, mtype_valid m -->
    (All_ m':mem, All_ e':expr, !!(step (m,e) (m',e')) -->
      |>(diamond contractsM (mtype_valid m' && F e'))) &&
    (!!(stopped m e) --> Ex_ H:isValue e,
         with_val (exp_to_val e H) (%tau)).

Lemma expr_type_sub1 :
  forall tau P Q,
    All_ e:expr, |>(P e >=> Q e)
      |-- All_ e:expr, expr_typeF tau P e >=> expr_typeF tau Q e.
Proof.
  repeat intro.
  hnf in H2.
  spec H2 a'1 H3.
  spec H2 b0 a'2 H4 H5.
  destruct H2.
  split; repeat intro.
  spec H2 b1 b2 a'3 H7.
  simpl in H8.
  detach H2.
  spec H2 a'4 H9.
  destruct H2 as [w [? ?]].
  exists w; split; auto.
  destruct H10; split; auto.
  spec H b2.
  rewrite <- (box_refl_trans fashionM) in H.
  rewrite <- later_commute in H.
  spec H a' H0.
  rewrite <- (box_refl_trans fashionM) in H.
  rewrite <- later_commute in H.
  assert (box fashionM (|> (P b2 >=> Q b2)) a'0).
  apply pred_nec_hereditary with a'; auto.
  clear H; rename H12 into H.
  spec H a'1.
  detach H.
  spec H a'4.
  detach H.
  spec H w.
  detach H.
  apply H; auto.
  apply extends_fashionable.
  apply H2.
  simpl; apply Rft_Rt_trans with a'3; auto.
  apply rt_trans with a'2; auto.
  apply extends_fashionable; auto.
  simpl; apply fashionR_refl.
  simpl; exact fashionR_trans.
  simpl; apply fashionR_refl.
  simpl; exact fashionR_trans.
  simpl; auto.

  apply H6; auto.
Qed.

Lemma expr_type_cont : forall tau, HOcontractive (expr_typeF tau).
Proof.
  intros.
  apply prove_HOcontractive.
  apply expr_type_sub1.
Qed.

Definition expr_type e tau := HORec (expr_type_cont tau) e.

Lemma expr_type_eqn : forall tau e,
  expr_type e tau =
  %All_ m:mem, mtype_valid m -->
    (All_ m':mem, All_ e':expr, !!(step (m,e) (m',e')) -->
      |>(diamond contractsM (mtype_valid m' && expr_type e' tau)))
    &&
    (!!(stopped m e) --> Ex_ H:isValue e, with_val (exp_to_val e H) (%tau)).
Proof.
  intros.
  change (expr_type e tau = expr_typeF tau (fun e => expr_type e tau) e).
  unfold expr_type at 1.
  rewrite HORec_fold_unfold.
  unfold expr_type.
  auto.
Qed.

Definition ty_lam (tau1 tau2 : pred world) : pred world :=
  Ex_ e:expr, Ex_ H:closed' 1 e, just (v_Lam e H) &&
  |>%(All_ v':value, with_val v' (%tau1) --> expr_type (subst 0 v' e) tau2).

Definition etype : Type := list (pred world).

Fixpoint etype_valid (e : env) (G : etype) : pred world :=
  match (e,G) with
   | (v :: es, tau :: Gs) => with_val v (%tau) && etype_valid es Gs
   | (nil, nil) => TT
   | _ => FF
  end.

(* Not in paper, but should add.  Taken from VMM. *)
Definition Typ (G : etype) (exp : expr) (tau : pred world) : Prop :=
  closed' (length G) exp  /\
  forall env, etype_valid env G |-- expr_type (subst_env env exp) tau.

Lemma sub_with_val : forall G P P' e,
  G |-- P >=> P' ->
  G |-- with_val e P >=> with_val e P'.
Proof.
  intros.
  apply derives_cut with (P >=> P'); auto.
  clear; repeat intro.
  rewrite <- box_refl_trans in H; auto.
  spec H a' H0.
  eapply pred_nec_hereditary in H; eauto.
  destruct a'0; simpl in *.
  spec H (m,e).
  detach H.
  eapply H; eauto.
  hnf; simpl; auto.
  simpl; apply fashionR_refl.
  simpl; exact fashionR_trans.
Qed.

Lemma expr_type_sub2 :
  forall X e P Q,
    P >=> Q |-- expr_typeF P X e >=> expr_typeF Q X e.
Proof.
  repeat intro.
  spec H2 a'1 H3.
  spec H2 b a'2 H4 H5.
  destruct H2; split; auto.
  repeat intro.
  spec H6 a'3 H7 H8.
  destruct H6 as [He ?]; exists He.
  revert H6.
  eapply sub_with_val.
  apply sub_box.
  exact extends_fashionable.
  do 2 intro.
  apply H6.
  instantiate (1 := a'0).
  rewrite <- box_refl_trans in H.
  spec H a' H0.
  apply pred_nec_hereditary with a'; auto.
  simpl; apply fashionR_refl.
  simpl; exact fashionR_trans.
  simpl; apply extends_fashionable; apply H3.
  apply rt_trans with a'2; auto.
Qed.

Lemma sub_expr_type : forall G P P',
  G |-- P >=> P' ->
  G |-- All_ e:expr, expr_type e P >=> expr_type e P'.
Proof.
  intros.
  unfold expr_type.
  apply HORec_sub; auto.
  apply expr_type_sub2.
  intros; apply expr_type_sub1.
Qed.

Lemma ty_lam_sub : forall G P P' Q Q',
  G |-- |>(P' >=> P) ->
  G |-- |>(Q >=> Q') ->
  G |-- (ty_lam P Q) >=> (ty_lam P' Q').
Proof.
  unfold ty_lam; intros.
  apply sub_exists; intro e.
  apply sub_exists; intro He.
  apply sub_conj.
  apply sub_refl.
  rewrite <- sub_later.
  apply (derives_cut (|>( (P' >=> P) && (Q >=> Q')))).
  rewrite box_and.
  do 2 intro; split; auto.
  apply box_positive.
  apply sub_box.
  hnf; apply extends_fashionable.
  apply sub_forall; intro v'.
  apply sub_impl.
  apply sub_with_val.
  apply sub_box.
  hnf; apply extends_fashionable.
  intros a H1; destruct H1; auto.
  intros a H1; destruct H1; auto.
  eapply sub_expr_type; eauto.
  do 2 intro; auto.
Qed.

Lemma sub_type_at : forall G P Q l,
  G |-- |>(P <=> Q) ->
  G |-- type_at l P >=> type_at l Q.
Proof.
  intros.
  apply derives_cut with (|>(P <=> Q)); auto.
  clear; repeat intro; destruct a'0.
  simpl in H2; simpl.
  case_eq (unsquash m); intros; rewrite H3 in H2.
  generalize (refl_equal (f l)).
  case_eq (f l); intros.
  rewrite H4 in H2.
  unfold approx_eq in *.
  rewrite H2.
  apply approx_eq_sub with (m,v).
  simpl.
  rewrite knot_level.
  rewrite H3; auto.
  rewrite <- (box_refl_trans fashionM) in H.
  rewrite <- later_commute in H.
  spec H a' H0.
  apply pred_nec_hereditary with a'; auto.
  simpl; apply fashionR_refl.
  simpl; exact fashionR_trans.
  rewrite H4 in H2.
  auto.
Qed.

Lemma ty_ref_sub : forall G P Q,
  G |-- |>(P <=> Q) ->
  G |-- ty_ref P >=> ty_ref Q.
Proof.
  intros.
  unfold ty_ref.
  apply sub_exists; intro l.
  apply sub_conj.
  apply sub_refl.
  apply sub_type_at.
  auto.
Qed.

Lemma extend_nonexpansive : forall F,
  nonexpansive F ->
  nonexpansive (fun X => %(F X)).
Proof.
  intros; apply box_nonexpansive; auto.
  hnf; apply extends_fashionable.
Qed.

Lemma with_val_nonexpansive : forall F v,
  nonexpansive F ->
  nonexpansive (fun X => with_val v (F X)).
Proof.
  intros.
  hnf; intros; cbv beta.
  apply sub_equ.
  apply sub_with_val.
  apply equ_sub.
  apply H.
  apply sub_with_val.
  apply equ_sub2.
  apply H.
Qed.

Lemma expr_type_nonexpansive : forall F e,
  nonexpansive F ->
  nonexpansive (fun X => (expr_type e (F X))).
Proof.
  intros; hnf; intros; cbv beta.
  apply sub_equ.
  do 2 intro; eapply sub_expr_type; eauto.
  apply equ_sub; apply H.
  do 2 intro; eapply sub_expr_type; eauto.
  apply equ_sub2; apply H.
Qed.

Lemma ty_lam_contractive : forall F G,
  nonexpansive F ->
  nonexpansive G ->
  contractive (fun X => ty_lam (F X) (G X)).
Proof.
  intros; hnf; intros.
  apply sub_equ.
  apply ty_lam_sub.
  apply box_positive.
  apply equ_sub2; apply H.
  apply box_positive.
  apply equ_sub; apply H0.
  apply ty_lam_sub.
  apply box_positive.
  apply equ_sub; apply H.
  apply box_positive.
  apply equ_sub2; apply H0.
Qed.

Lemma type_at_contractive : forall l F,
  nonexpansive F ->
  contractive (fun X => type_at l (F X)).
Proof.
  intros; hnf; intros.
  cbv beta.
  apply sub_equ; apply sub_type_at; apply box_positive.
  apply H.
  apply sub_equ; [ apply equ_sub2 | apply equ_sub ]; apply H.
Qed.

Lemma ty_ref_contractive : forall F,
  nonexpansive F ->
  contractive (fun X => ty_ref (F X)).
Proof.
  intros; unfold ty_ref.
  apply exists_contractive; intros.
  apply conj_contractive.
  repeat intro; split; repeat intro; eauto.
  apply type_at_contractive; auto.
Qed.

Lemma just_extends : forall v,
  %just v = just v.
Proof.
  intros.
  eapply boxy_i.
  apply R_extends_refl.
  intros.
  destruct w; destruct w'.
  destruct H; subst.
  auto.
Qed.

Lemma ty_ref_extends : forall tau,
  %(ty_ref tau) = ty_ref tau.
Proof.
  intros.
  unfold ty_ref.
  apply boxy_i.
  simpl; apply R_extends_refl.
  intros.
  revert w' H.
  apply (box_ex addr extendM).
  destruct H0 as [a [? ?]]; exists a.
  rewrite box_and; split.
  rewrite just_extends; auto.
  rewrite type_at_extends; auto.
Qed.

Lemma fashionable_extends : forall P,
  %(box fashionM P) = box fashionM P.
Proof.
  intros; apply equiv_eq; repeat intro.
  spec H a (R_extends_refl a); auto.
  eapply H.
  simpl; apply fashionR_trans with a'; auto.
  apply extends_fashionable; auto.
Qed.

Lemma with_val_extends : forall v P,
  %(with_val v P) = with_val v (%P).
Proof.
  intros; apply equiv_eq; repeat intro.
  destruct a; destruct a'.
  simpl in H0; destruct H0; subst.
  spec H (m0,v0).
  apply H.
  split; auto.
  destruct a; destruct a'.
  simpl in H0; destruct H0; subst.
  simpl in *.
  apply H; split; auto.
Qed.

Lemma expr_type_extends : forall e tau,
  %expr_type e tau = expr_type e tau.
Proof.
  intros e tau.
  rewrite expr_type_eqn.
  rewrite box_refl_trans; auto.
Qed.

Lemma etype_valid_extends : forall G env,
  %etype_valid env G = etype_valid env G.
Proof.
  intros.
  apply boxy_i.
  simpl; apply R_extends_refl.
  revert env; induction G; destruct env; simpl; intuition.
  apply H1; auto.
  destruct w; destruct w'.
  destruct H; subst.
  destruct a'.
  destruct H0; subst.
  simpl; split; auto.
  apply knot_extends_trans with m0; auto.
  eapply IHG; eauto.
Qed.

Lemma ty_lam_extends : forall sigma tau,
  %ty_lam sigma tau = ty_lam sigma tau.
Proof.
  intros.
  apply boxy_i.
  simpl; apply R_extends_refl.
  unfold ty_lam; intros.
  destruct H0 as [e [He [? ?]]].
  exists e; exists He.
  split.
  destruct w; destruct w'; destruct H; subst.
  auto.
  rewrite <- (box_refl_trans extendM) in H1; auto.
  rewrite <- later_commute in H1.
  apply H1; auto.
Qed.
