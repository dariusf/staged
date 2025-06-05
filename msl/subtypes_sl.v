Require Import msl.base.
Require Import msl.ageable.
Require Import msl.sepalg.
Require Import msl.sepalg_generators.
Require Import msl.age_sepalg.
Require Import msl.predicates_hered.
Require Import msl.predicates_sl.
Require Import msl.subtypes.

Local Open Scope pred.


Lemma unfash_derives {A} `{agA : ageable A} {EO: Ext_ord A}:
  forall {P Q}, (P |-- Q) -> @derives A _ _ (! P) (! Q).
Proof.
intros. intros w ?. simpl in *. apply H. auto.
Qed.

Lemma subp_sepcon {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A}{XA: Age_alg A}{EO: Ext_ord A}{EA: Ext_alg A} : forall G P P' Q Q',
  (G |-- P >=> P') ->
  (G |-- Q >=> Q') ->
  G |-- P * Q >=> P' * Q'.
Proof.
  pose proof I.
  repeat intro.
  specialize (H0 _ H2).
  specialize (H1 _ H2).
  clear G H2.
  destruct H6 as [w1 [w2 [? [? ?]]]].
  exists w1; exists w2; split; auto.
  destruct (join_level _ _ _ H2); auto.
 apply necR_level in H4. apply ext_level in H5.
  split.
  eapply H0; auto; lia.
  eapply H1; auto; lia.
Qed.

Lemma sub_wand {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A}{XA: Age_alg A}{EO: Ext_ord A}{EA: Ext_alg A} : forall G P P' Q Q',
  (G |-- P' >=> P) ->
  (G |-- Q >=> Q') ->
  G |-- (P -* Q) >=> (P' -* Q').
Proof.
  pose proof I.
  repeat intro.
  specialize (H0 _ H2); specialize (H1 _ H2); clear G H2; pose (H2:=True).
  eapply H0 in H9; try apply necR_refl; try apply ext_refl.
  eapply H1; try apply necR_refl; try apply ext_refl.
  apply necR_level in H4. apply ext_level in H5. apply necR_level in H7. apply join_level in H8 as []. lia.
  eapply H6; eauto.
  apply necR_level in H4. apply ext_level in H5. apply necR_level in H7.
  apply join_level in H8 as []. lia.
Qed.

(*Lemma find_superprecise {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A}{XA: Age_alg A}{EO: Ext_ord A}:
   forall Q, Q |-- EX P:_, P && !(P >=> Q) && !!superprecise (P).
Proof.
intros.
intros w ?.
exists (exactly w).
split; auto.
split; auto.
hnf; eauto.
intros w' ? w'' ? ? ? ?.
hnf in H3.
destruct H3 as (x & ? & ?).
apply pred_upclosed with x; auto.
apply pred_nec_hereditary with w; auto.
do 3 red.
apply superprecise_exactly.
Qed.*)

Lemma sepcon_subp' {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A}{XA: Age_alg A}{EO: Ext_ord A}{EA: Ext_alg A}:
  forall (P P' Q Q' : pred A) (st: nat),
    (P >=> P') st ->
    (Q >=> Q') st ->
    (P * Q >=> P' * Q') st.
Proof.
 pose proof I.
intros.
intros w' ? w'' ? ?%necR_level ?%ext_level [w1 [w2 [J [? ?]]]].
destruct (join_level _ _ _ J).
exists w1; exists w2; repeat split; auto.
eapply H0; auto; lia.
eapply H1; auto; lia.
Qed.

Lemma subp_refl'  {A} `{agA : ageable A} {EO: Ext_ord A} : forall (Q: pred A) (st: nat), (Q >=> Q) st.
Proof.
intros.
intros ? ? ? ?; auto.
Qed.

Lemma subp_trans' {A} `{agA : ageable A} {EO: Ext_ord A} :
  forall (B C D: pred A) (w: nat), (B >=> C)%pred w -> (C >=> D)% pred w -> (B >=> D)%pred w.
Proof.
intros.
intros w' ? w'' ? ? ? ?.
eapply H0; eauto.
eapply H; eauto.
Qed.

Lemma andp_subp'  {A} `{agA : ageable A} {EO: Ext_ord A} :
 forall (P P' Q Q': pred A) (w: nat), (P >=> P') w -> (Q >=> Q') w -> (P && Q >=> P' && Q') w.
Proof.
intros.
intros w' ? w'' ? ? ? [? ?]; split.
eapply H; eauto.
eapply H0; eauto.
Qed.

Lemma allp_subp' {A} `{agA : ageable A} {EO: Ext_ord A} : forall T (F G: T -> pred A) (w: nat),
   (forall x,  (F x >=> G x) w) -> (allp (fun x:T => (F x >=> G x)) w).
Proof.
intros.
intro x; apply H; auto.
Qed.


Lemma pred_eq_e1 {A} `{agA : ageable A} {EO: Ext_ord A}: forall (P Q: pred A) w,
       ((P <=> Q) w -> (P >=> Q) w).
Proof.
intros.
intros w' ? w'' ? ?.
eapply H; eauto.
Qed.

Lemma pred_eq_e2 {A} `{agA : ageable A} {EO: Ext_ord A}: forall (P Q: pred A)  w,
     ((P <=> Q) w -> (Q >=> P) w).
Proof.
Proof.
intros.
intros w' ? w'' ? ?.
eapply H; eauto.
Qed.

#[export] Hint Resolve sepcon_subp' : core.
#[export] Hint Resolve subp_refl' : core.
#[export] Hint Resolve andp_subp' : core.
#[export] Hint Resolve allp_subp' : core.
#[export] Hint Resolve derives_subp : core.
#[export] Hint Resolve pred_eq_e1 : core.
#[export] Hint Resolve pred_eq_e2 : core.


Lemma allp_imp2_later_e2 {B}{A}{agA: ageable A}{EO: Ext_ord A}:
   forall (P Q: B -> pred A) (y: B) ,
      (ALL x:B, |> P x <=> |> Q x) |-- |> Q y >=> |> P y.
Proof.
  intros.  intros w ?. specialize (H y). apply pred_eq_e2. auto.
Qed.
Lemma allp_imp2_later_e1 {B}{A}{agA: ageable A}{EO: Ext_ord A}:
   forall (P Q: B -> pred A) (y: B) ,
      (ALL x:B, |> P x <=> |> Q x) |-- |> P y >=> |> Q y.
Proof.
  intros.  intros w ?. specialize (H y). apply pred_eq_e1. auto.
Qed.

(*
Lemma subp_later {A} `{agA:  ageable A} (SS: natty A):
 forall (P Q: pred A), |> (P >=> Q) |-- |> P >=> |> Q.
Proof.
intros.
rewrite later_fash; auto.
apply fash_derives.
apply axiomK.
Qed.
*)

Lemma extend_unfash {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A}{XA: Age_alg A}{EO: Ext_ord A}{EA: Ext_alg A} : forall (P: pred nat), boxy extendM (! P).
Proof.
intros.
apply boxy_i; auto; intros.
unfold unfash in *.
simpl in H. destruct H.
hnf in H0|-*.
apply join_level in H as [<-]; auto.
Qed.

#[export] Hint Resolve extend_unfash : core.

Lemma subp_unfash {A} `{Age_alg A} {EO: Ext_ord A}:
  forall (P Q : pred nat) (n: nat), (P >=> Q) n -> ( ! P >=> ! Q) n.
Proof.
intros.
intros w ?. specialize (H0 _ H1).
intros w' ? ? ?. apply (H0 _ _ (necR_level' H2)).
apply ext_level; auto.
Qed.
#[export] Hint Resolve subp_unfash : core.


Lemma unfash_sepcon_distrib:
        forall {T}{agT: ageable T}{JoinT: Join T}{PermT: Perm_alg T}{SepT: Sep_alg T}{AgeT: Age_alg T}{EO: Ext_ord T}{EA: Ext_alg T}
           (P: pred nat) (Q R: pred T),
               unfash P && (Q*R) = (unfash P && Q) * (unfash P && R).
Proof.
intros.
apply pred_ext.
intros w [? [w1 [w2 [? [? ?]]]]].
exists w1; exists w2; repeat split; auto.
apply join_level in H0. destruct H0.
hnf in H|-*. congruence.
apply join_level in H0. destruct H0.
hnf in H|-*. congruence.
intros w [w1 [w2 [? [[? ?] [? ?]]]]].
split.
apply join_level in H. destruct H.
hnf in H0|-*. congruence.
exists w1; exists w2; repeat split; auto.
Qed.
