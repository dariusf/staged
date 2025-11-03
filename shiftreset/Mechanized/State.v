
(* Helper definitions to more closely reflect Heifer's definitions. *)

From Stdlib Require Import Classes.RelationClasses.
From ShiftReset Require Import Logic Automation Entl Norm Propriety.

(* ssreflect lock from taobao *)

(* abstract out Lock with this module type
  to prevent downstream modules from automatically unfolding lock.
  this has the same effect as [Opaque lock.] *)
Module Type LOCK.
  Parameter locked : forall A, A -> A.
  Parameter lock : forall A x, x = (locked _ x) :> A.
  Parameter marked : forall (n : nat) A, A -> A.
  Parameter mark : forall n A x, x = (marked n A x) :> A.
End LOCK.

Module Lock : LOCK.
Lemma master_key : unit. Proof. exact tt. Qed.

Definition marked (n : nat) A := let tt := master_key in fun x : A => x.
Definition mark n A x : x = (marked n A x) :> A.
Proof.
  intros. unfold marked. reflexivity.
Qed.
Definition locked A := marked 0 A.
Lemma lock : forall A x, x = (locked _ x) :> A.
Proof.
  intros.
  unfold locked, marked.
  reflexivity.
Qed.

End Lock.

Definition lock := Lock.lock.
Definition locked := Lock.locked.

Definition mark := Lock.mark.
Definition marked := Lock.marked.

#[global]
Instance Proper_pointwise_eq_ens : Proper (Morphisms.pointwise_relation val eq ====> entails) ens.
Proof.
  unfold Proper, respectful, Morphisms.pointwise_relation, entails. intros.
  inverts H0.
  destruct H7 as (v&h3&P&Q&S&T). subst. apply s_ens.
  eexists. eexists.
  rewrite <- H.
  intuition.
  auto.
Qed.

#[global]
Instance Proper_pointwise_himpl_ens : Proper (Morphisms.pointwise_relation val himpl ====> entails) ens.
Proof.
  unfold Proper, respectful, Morphisms.pointwise_relation, entails. intros.
  inverts H0.
  destruct H7 as (v&h3&P&Q&S&T). subst. apply s_ens.
  eexists. eexists.
  intuition.
  apply H.
  auto.
Qed.

#[global]
Instance Proper_hstar_himpl : Proper (himpl ====> himpl ====> himpl) hstar.
Proof.
  unfold Proper, respectful, Morphisms.pointwise_relation, flip. intros.
  apply (@himpl_trans (y \* x0)); xsimpl; auto.
Qed.

#[global]
Instance Proper_qimpl_ens : Proper ((@qimpl val) ====> entails) ens.
Proof.
  unfold Proper, respectful, entails. intros * Hqimpl * Hens.
  inverts Hens. destr H5. subst. constructor. eexists. eexists. intuition. 
  unfold qimpl, himpl in Hqimpl. auto.
Qed.

#[global]
Instance Proper_himpl_ens_void : Proper (himpl ====> entails) ens_.
Proof.
  unfold Proper, respectful, entails. intros * Hhimpl * Hens.
  inverts Hens. destr H5. hinv H0. hinv H0. subst. constructor. eexists. eexists. intuition.
  hintro.
  - apply hpure_intro. auto.
  - apply Hhimpl. auto.
  - auto.
Qed.

#[global]
Instance Proper_himpl_req_void : Proper (flip himpl ====> eq ====> entails) req.
Proof.
  unfold Proper, respectful, entails. intros * Hhimpl * H. subst.
  intros * Hreq.
  inverts Hreq. 
  applys* s_req.
Qed.

Lemma bientails_iff_entails : forall f1 f2,
  bientails f1 f2 <-> (entails f1 f2 /\ entails f2 f1).
Proof.
  unfold bientails, entails.
  intros. split; intuition; apply H; auto.
Qed.


#[global]
Instance Proper_pointwise_bientails_fex : forall A,
  Proper (Morphisms.pointwise_relation A bientails ====> bientails)
  (@fex A).
Proof.
  unfold Proper, respectful, Morphisms.pointwise_relation.
  intros * Hbient.
  apply bientails_iff_entails.  
  split; fdestruct v; fexists v; lets H: Hbient v; apply bientails_iff_entails in H; intuition.
Qed.

Inductive hpred :=
  | hsplit (lhs : hpred) (rhs : hpred)
  | hpts_to (p : loc) (v : val)
  | hemp.

Fixpoint hprop_of_hpred pred :=
  match pred with
  | hsplit lhs rhs => (hprop_of_hpred lhs) \* (hprop_of_hpred rhs)
  | hpts_to p v => p ~~> v
  | hemp => \[]
  end.

(* because a lot of existing lemmas and tactics are written in terms of the shallowly-embedded
  [ens] though, it's useful to reflect the common structure of [hprop]s into our representation *)

Inductive precond_reflect : Prop -> hpred -> hprop -> Prop :=
  | prec_refl_pure : forall P, precond_reflect P hemp \[P]
  | prec_refl_loc : forall loc val, precond_reflect True (hpts_to loc val) (loc ~~> val)
  | prec_refl_star : forall P1 h1 hp1 P2 h2 hp2,
      precond_reflect P1 h1 hp1 ->
      precond_reflect P2 h2 hp2 ->
      precond_reflect (P1 /\ P2) (hsplit h1 h2) (hp1 \* hp2).

Lemma hpure_conj_star_star : forall P1 P2 H1 H2,
  \[P1 /\ P2] \* H1 \* H2 ==> (\[P1] \* H1) \* (\[P2] \* H2).
Proof.
  intros.
  rewrite <- hstar_hpure_conj.
  rewrite (hstar_comm H1).
  rewrite hstar_assoc. 
  rewrite <- (hstar_assoc \[P2] _ _).
  rewrite (hstar_comm (_ \* _)).
  rewrite <- hstar_assoc.
  apply himpl_refl.
Qed.

Lemma hpure_conj_star_star_conv : forall P1 P2 H1 H2,
  (\[P1] \* H1) \* (\[P2] \* H2) ==> \[P1 /\ P2] \* H1 \* H2.
Proof.
  intros.

  rewrite <- hstar_hpure_conj.
  rewrite hstar_assoc. 
  rewrite <- (hstar_assoc H1 _ _).
  rewrite (hstar_comm H1).
  rewrite (hstar_assoc \[P2]).
  rewrite hstar_assoc.
  apply himpl_refl.
Qed.

Lemma precond_reflect_himpl_hprop : forall P h hp,
  precond_reflect P h hp -> (\[P] \* (hprop_of_hpred h) ==> hp /\ hp ==> \[P] \* (hprop_of_hpred h)).
Proof.
  intros * Hrefl.
  induction Hrefl.
  - unfold hprop_of_hpred. intuition; xsimpl; auto.
  - unfold hprop_of_hpred. intuition; xsimpl; auto.
  - destruct IHHrefl1 as [IH1a IH1b].
    destruct IHHrefl2 as [IH2a IH2b].
    simpl. split.
    + apply (himpl_trans (hpure_conj_star_star _ _ _ _)).
      apply himpl_frame_lr; assumption.
    + eapply himpl_trans.
      apply himpl_frame_lr; [apply IH1b | apply IH2b ].
      apply hpure_conj_star_star_conv.
Qed.

Definition postcond_value {A : Type} (v : A) H Q := 
  (Q ===> (fun res => \[res = v] \* H))
  /\ ((fun res => \[res = v] \* H) ===> Q).

Lemma postcond_pure : forall (v : val), postcond_value v \[] (fun res => \[res = v]).
Proof.
  intros. unfold postcond_value. split; xsimpl; auto.
Qed.

Lemma postcond_value_split_l : forall (v : val) H1 H2 Q, 
  postcond_value v H1 Q -> postcond_value v (H1 \* H2) (fun r => Q r \* H2). 
Proof.
  unfold postcond_value. intros. destruct H as [HQ HQr]. unfold qimpl in HQ, HQr. unfold qimpl.
  split; intros; rewrite <- hstar_assoc; apply himpl_frame_l; auto.
Qed.

Lemma postcond_value_split_r : forall (v : val) H1 H2 Q, 
  postcond_value v H2 Q -> postcond_value v (H1 \* H2) (fun r => H1 \* Q r).
Proof. 
  unfold postcond_value. intros. destruct H as [HQ HQr]. unfold qimpl in HQ, HQr. unfold qimpl.
  split; intros; rewrite <- hstar_assoc. 
  - rewrite (hstar_comm _ H1). rewrite hstar_assoc. apply himpl_frame_r; auto.
  - rewrite (hstar_comm _ H1). rewrite hstar_assoc. apply himpl_frame_r; auto.
Qed.

Inductive postcond_reflect : val -> Prop -> hpred -> postcond -> Prop :=
  | postc_refl_val v P hpred HP Q
      (Hvalue : postcond_value v HP Q)
      (Hprecond: precond_reflect P hpred HP)
      : postcond_reflect v P hpred Q.

(*#[global]*)
(*Instance Proper_eq_impl_eq_eq_postcond :*)
(*  Proper (eq ====> impl ====> eq ====> (Morphisms.pointwise_relation val eq) ====> impl) postcond_reflect.*)
(*Proof.*)
(*Admitted.*)

Definition ens_state P h v := ens (fun res => \[res = v] \* \[P] \* (hprop_of_hpred h)).
Definition ens_state_ P h := ens_state P h vunit.
Definition ens_pure P := ens_state_ P hemp.
Definition ens_heap hp := ens_state_ True hp.
Definition ens_ret v := ens_state True hemp v.

Definition req_state P h f := req (\[P] \* (hprop_of_hpred h)) f.

Lemma ens_state_void_is_ens_void : forall h P,
  bientails (ens_state_ P h) (ens_ (\[P] \* (hprop_of_hpred h))).
Proof.
  intros. unfold ens_state_, ens_state, ens_. reflexivity.
Qed.

Lemma ens_state_vunit_is_ens_state_void : forall h P,
  bientails (ens_state P h vunit) (ens_state_ P h).
Proof.
  unfold ens_state_. reflexivity.
Qed.

Lemma ens_state_is_ens : forall h P v,
  bientails (ens_state P h v) (ens (fun r => \[r = v] \* \[P] \* (hprop_of_hpred h))).
Proof.
  intros. unfold ens_state. reflexivity.
Qed.

Lemma ens_vunit_is_ens_void : forall H, ens (fun res => \[res = vunit] \* H) = ens_ H.
Proof.
  unfold ens_. intros. reflexivity.
Qed.

Fixpoint simplify_hpred hp :=
  match hp with
  | hsplit hemp lhs => simplify_hpred lhs
  | hsplit rhs hemp => simplify_hpred rhs
  | hp => hp
  end.

Lemma hpred_eq_simplify_hpred : forall hp,
  hprop_of_hpred hp = hprop_of_hpred (simplify_hpred hp).
Proof.
  intros.
  induction hp; try solve [reflexivity].
  simpl.
  rewrite IHhp1. rewrite IHhp2.
  destruct hp1 eqn:H1, hp2 eqn:H2;
  solve [
    rewrite <- ?IHhp1;
    rewrite <- ?IHhp2;
    rewrite ?hstar_hempty_r;
    rewrite ?hstar_hempty_l;
    simpl;
    reflexivity
  ].
Qed.

(* Rewrites all [ens_state]s present in the goal back to an [ens]. *)
  (* TODO [rew_state_to_hprop in H] *)
Ltac rew_state_to_hprop := 
  unfold ens_pure, ens_heap, ens_ret;
  repeat (rewrite ens_state_vunit_is_ens_state_void at 1);
  repeat (rewrite ens_state_void_is_ens_void at 1);
  rewrite ?ens_state_void_is_ens_void;
  unfold ens_state_, ens_state, req_state, hprop_of_hpred;
  (* clean up the postconditions *)
  rewrite <- ?hempty_eq_hpure_true;
  autorewrite with rew_heap;
  (*rewrite <- hempty_eq_hpure_true;*)
  (*repeat (rewrite hstar_hempty_r, hstar_hempty_l);*)
  fold hprop_of_hpred.

(* now we can write a rewriting lemma *)

(* this lets us use SLF's heap rewrite lemmas inside an ens *)
Lemma ens_duplicate_pure : forall P,
  bientails (ens (fun r => \[P r])) (ens (fun r => \[P r]) ;; ens (fun r => \[P r])).
Proof.
  unfold bientails. split.
  - intros H. inverts H. destruct H6 as (v & h3 & H).
    apply (@s_seq s2 h2 v); apply s_ens; exists v; eexists; intuition; rew_fmap; auto.
    inverts H; hintro; auto.
  - intros H. inverts H. inverts H7. inverts H8. 
    destr H5. destr H6. subst. inverts H.
    + apply s_ens. eexists. eexists. intuition. hinv H4. hinv H0. subst. rewrite union_self. hintro. assumption.
    + inverts H6. destr H5. congruence.
Qed.

Lemma norm_split_ens_void : forall P h Q,
  precond_reflect P h Q -> entails (ens_ Q) (ens_state_ P h).
Proof.
  (* induct on the derivation of precond_reflect *)
  intros * Hrefl.
  induction Hrefl; rew_state_to_hprop.
  - fentailment. xsimpl; intros; intuition.
  - fentailment. xsimpl; intros; intuition.
  - rewrite norm_ens_ens_void.
    rewrite IHHrefl1.
    rewrite IHHrefl2.
    rewrite !ens_state_void_is_ens_void.
    repeat (rewrite <- norm_ens_ens_void).
    fentailment. xsimpl; intros; intuition.
Qed.

Lemma norm_combine_ens_void : forall P h Q,
  precond_reflect P h Q -> entails (ens_state_ P h) (ens_ Q).
Proof.
  intros * Hrefl.
  induction Hrefl; rew_state_to_hprop.
  - reflexivity.
  - reflexivity.
  - apply precond_reflect_himpl_hprop in Hrefl1.
    apply precond_reflect_himpl_hprop in Hrefl2.
    destruct Hrefl1 as [Hrefl1 _].
    destruct Hrefl2 as [Hrefl2 _].
    apply entl_ens_void_single.
    apply (himpl_trans (hpure_conj_star_star _ _ _ _)).
    apply himpl_frame_lr; assumption.
Qed.

Lemma norm_split_req_void : forall P h Q f,
  precond_reflect P h Q -> entails (req Q f) (req_state P h f).
Proof.
  intros * Hrefl.
  generalize dependent f.
  induction Hrefl; rew_state_to_hprop; try (intros; reflexivity).
  apply precond_reflect_himpl_hprop in Hrefl1.
  apply precond_reflect_himpl_hprop in Hrefl2.
  destruct Hrefl1 as [Hrefl1 _].
  destruct Hrefl2 as [Hrefl2 _].
  intros.
  apply entl_req_req.
  - apply (himpl_trans (hpure_conj_star_star _ _ _ _)).
    apply himpl_frame_lr; assumption.
  - reflexivity.
Qed.

Lemma norm_combine_req_void : forall P h Q f,
  precond_reflect P h Q -> entails (req_state P h f) (req Q f).
Proof.
  intros * Hrefl.
  generalize dependent f.
  induction Hrefl; rew_state_to_hprop; try (intros; reflexivity).
  intros.
  apply precond_reflect_himpl_hprop in Hrefl1.
  apply precond_reflect_himpl_hprop in Hrefl2.
  destruct Hrefl1 as [_ Hrefl1].
  destruct Hrefl2 as [_ Hrefl2].
  apply entl_req_req. 2: { reflexivity. }
  eapply himpl_trans.
  - apply himpl_frame_lr.
    + apply Hrefl1.
    + apply Hrefl2.
  - apply hpure_conj_star_star_conv.
Qed.

Lemma norm_split_ens : forall v P h Q,
  postcond_reflect v P h Q -> entails (ens Q) (ens_state P h v).
Proof.
  intros * Hrefl.
  inverts Hrefl.
  inverts Hvalue.
  apply norm_split_ens_void in Hprecond.
  rewrite H.
  rewrite <- norm_ens_ens_void_l.
  rewrite Hprecond.
  rewrite ens_state_void_is_ens_void.
  rewrite norm_ens_ens_void_l.
  rew_state_to_hprop.
  reflexivity.
Qed.

Lemma norm_combine_ens : forall v P h Q,
  postcond_reflect v P h Q -> entails (ens_state P h v) (ens Q).
Proof.
  intros * Hrefl.
  inverts Hrefl.
  apply norm_combine_ens_void in Hprecond.
  unfold ens_state.
  inverts Hvalue.
  rewrite <- H0.
  rewrite <- norm_ens_ens_void_l.
  unfold ens_.
  unfold ens_state_, ens_state in Hprecond.
  rewrite Hprecond.
  rewrite norm_ens_ens_void_l.
  reflexivity.
Qed.

Lemma norm_ens_bient_ens_state : forall v P h Q,
  postcond_reflect v P h Q -> bientails (ens Q) (ens_state P h v).
Proof.
  intros * Hrefl.
  apply bientails_iff_entails.
  split.
  - apply norm_split_ens. exact Hrefl.
  - apply norm_combine_ens. exact Hrefl.
Qed.

Lemma norm_req_bient_req_state : forall P h Q f,
  precond_reflect P h Q -> bientails (req Q f) (req_state P h f).
Proof.
  intros * Hrefl.
  apply bientails_iff_entails.
  split.
  - apply norm_split_req_void. exact Hrefl.
  - apply norm_combine_req_void. exact Hrefl.
Qed.

Lemma norm_heap_simplify_ens_state : forall v P h,
  bientails (ens_state P h v) (ens_state P (simplify_hpred h) v).
Proof.
  intros *.
  rew_state_to_hprop.
  rewrite hpred_eq_simplify_hpred.
  reflexivity.
Qed.

Lemma norm_heap_simplify_req_state : forall P h f,
  bientails (req_state P h f) (req_state P (simplify_hpred h) f).
Proof.
  intros *.
  rew_state_to_hprop.
  rewrite hpred_eq_simplify_hpred.
  reflexivity.
Qed.

Lemma rew_rule_mark_all_ens_state : forall v P h,
  bientails (ens_state P h v) ((marked 1 _ ens_state) P h v).
Proof.
  intros *.
  rewrite <- (mark 1).
  reflexivity.
Qed.

Lemma rew_rule_mark_all_req_state : forall P h f,
  bientails (req_state P h f) ((marked 1 _ req_state) P h f).
Proof.
  intros *.
  rewrite <- (mark 1).
  reflexivity.
Qed.

Lemma norm_heap_simplify_ens_state_mark : forall v P h,
  bientails ((marked 1 _ ens_state) P h v) ((marked 2 _ ens_state) P (simplify_hpred h) v).
Proof.
  intros *.
  rewrite <- (mark 1).
  rewrite <- (mark 2).
  apply norm_heap_simplify_ens_state.
Qed.

Lemma norm_heap_simplify_req_state_mark : forall P h f,
  bientails ((marked 1 _ req_state) P h f) ((marked 2 _ req_state) P (simplify_hpred h) f).
Proof.
  intros *.
  rewrite <- (mark 1).
  rewrite <- (mark 2).
  apply norm_heap_simplify_req_state.
Qed.

Ltac fsimpl_heap :=
  repeat (setoid_rewrite rew_rule_mark_all_ens_state at 1);
  repeat (setoid_rewrite norm_heap_simplify_ens_state_mark at 1);
  repeat (setoid_rewrite rew_rule_mark_all_req_state at 1);
  repeat (setoid_rewrite norm_heap_simplify_req_state_mark at 1);
  repeat (rewrite <- (mark 2));
  simpl.

Ltac fsolve_prec_reflect :=
  match goal with
  | [ |- precond_reflect _ _ (_ ~~> _) ] => apply prec_refl_loc
  | [ |- precond_reflect _ _ \[_]] => apply prec_refl_pure
  | [ |- precond_reflect _ _ \[]] => rewrite hempty_eq_hpure_true; apply prec_refl_pure
  | [ |- precond_reflect _ _ (_ \* _)] => eapply prec_refl_star; fsolve_prec_reflect
  end.

Ltac fsolve_post_value :=
  match goal with
  | [ |- postcond_value _ _ _] => 
      first [
        apply postcond_pure
        | apply postcond_value_split_l; fsolve_post_value
        | apply postcond_value_split_r; fsolve_post_value
      ]
  end.

Hint Rewrite and_True_r_eq and_True_l_eq : rew_simpl_pure.

Ltac relock_ens_state := 
  (* lock all ens_states, including the one we just rewrote *)
  (* this is to prevent the setoid_rewrite from rewriting this state,
     since it is also just an ens_ in the background *)
  try rewrite <- (lock _ ens_state);
  rewrite (lock _ ens_state).

Ltac relock_req_state :=
  (* lock all ens_states, including the one we just rewrote *)
  (* this is to prevent the setoid_rewrite from rewriting this state,
     since it is also just an ens_ in the background *)
  try rewrite <- (lock _ req_state);
  rewrite (lock _ req_state).

Ltac frewrite_req_to_req_state_one :=
  first [ rewrite norm_req_bient_req_state at 1 | setoid_rewrite norm_req_bient_req_state at 1];
  [ | fsolve_prec_reflect];
  autorewrite with rew_simpl_pure;
  relock_req_state.

Ltac frewrite_ens_to_ens_state_one :=
  first [ rewrite norm_ens_bient_ens_state at 1 | setoid_rewrite norm_ens_bient_ens_state at 1];
  [ | match goal with
      | [ |- postcond_reflect _ _ _ _ ] => 
          eapply postc_refl_val;
          [ fsolve_post_value | fsolve_prec_reflect ]
      end];
  autorewrite with rew_simpl_pure;
  relock_ens_state.

(* A hack to force Coq to only rewrite the right-hand side of an entailment. *)
Definition entailsR a b := entails b a.

Lemma entailsR_is_entails : forall a b, entailsR a b = entails b a.
Proof. reflexivity. Qed.

(* Hide the existing Proper instance for entails, since that lets Coq rewrite the
  left-hand side of an entailsR *)
Typeclasses Opaque entailsR.

Instance Proper_entails_entailsR :
  Proper (entails ====> eq ====> impl) entailsR.
Proof.
  unfold Proper, respectful, entails, entailsR, flip, impl.
  intros * H * Hx0 Hentx0. subst. fold (entails x y) in H.
  pose proof entails_trans as Ht. unfold Transitive in Ht.
  apply (Ht _ x _); auto.
Qed.

Instance Proper_bientails_entailsR :
  Proper (bientails ====> eq ====> iff) entailsR.
Proof.
  unfold Proper, respectful, entailsR, iff.
  intros. subst. apply bientails_iff_entails in H. destr H.
  pose proof entails_trans as Ht. unfold Transitive in Ht.
  split.
  - intros Hy. apply (Ht _ x _); auto.
  - intros Hy. apply (Ht _ y _); auto.
Qed.

Ltac with_entailsR_base tac :=
  rewrite <- entailsR_is_entails;
  tac;
  rewrite entailsR_is_entails.

Tactic Notation "with_entailsR" tactic(tac) := with_entailsR_base ltac:(tac).

Ltac rew_hprop_to_state :=
  (* unlock all the ens_states once we are done *)
  (repeat frewrite_ens_to_ens_state_one);
  rewrite <- ?(lock _ ens_state);
  (repeat frewrite_req_to_req_state_one);
  rewrite <- ?(lock _ req_state);
  fsimpl_heap.

(*Lemma norm_seq_ens_ret_ens_pure : *)
(*  forall P v, entails (ens_ret v ;; ens_pure P) (ens_pure P ;; ens_ret v).*)
(*Proof.*)
(*Admitted.*)
(**)
(*Lemma norm_seq_ens_ret_ens_heap :*)
(*  forall H v, entails (ens_ret v ;; ens_heap H) (ens_heap H ;; ens_ret v).*)
(*Proof.*)
(*Admitted.*)
(**)
(*Lemma norm_seq_ens_ret_combine :*)
(*  forall v, entails (ens_ret v ;; ens_ret v) (ens_ret v).*)
(*Proof.*)
(*Admitted.*)
(**)
(*Lemma norm_seq_seq_ens_ret_ens_pure : *)
(*  forall P v fk, entails (ens_ret v ;; ens_pure P ;; fk) (ens_pure P ;; ens_ret v ;; fk).*)
(*Proof.*)
(*Admitted.*)
(**)
(*Lemma norm_seq_seq_ens_ret_ens_heap :*)
(*  forall H v fk, entails (ens_ret v ;; ens_heap H ;; fk) (ens_heap H ;; ens_ret v ;; fk).*)
(*Proof.*)
(*Admitted.*)
(**)
(*Lemma norm_seq_seq_ens_ret_combine :*)
(*  forall v fk, entails (ens_ret v ;; ens_ret v ;; fk) (ens_ret v ;; fk).*)
(*Proof.*)
(*Admitted.*)
(**)
(*Hint Rewrite*)
(*  norm_seq_ens_ret_ens_pure*)
(*  norm_seq_ens_ret_ens_heap*)
(*  norm_seq_ens_ret_combine*)
(*  norm_seq_seq_ens_ret_ens_pure*)
(*  norm_seq_seq_ens_ret_ens_heap*)
(*  norm_seq_seq_ens_ret_combine*)
(*  : rew_reorder_ens.*)
(**)

Class Into (A : Type) (B : Type) : Type := {
  into : A -> B;
  into_inj : forall a b, into a = into b -> a = b
}.

Instance Into_val_val : Into val val.
Proof.
  refine ({|
    into := id;
    into_inj := _
  |}). 
  unfold id.
  intuition.
Defined.

Instance Into_loc_val : Into loc val.
Proof.
  refine ({|
    into := vloc;
    into_inj := _
  |}). 
  intros.
  inverts H.
  reflexivity.
Defined.

Instance Into_int_val : Into int val.
Proof.
  refine ({|
    into := vint;
    into_inj := _
  |}). 
  intros.
  inverts H.
  reflexivity.
Defined.

(* It may be useful to work with bound values with other types than [val].
  This implements support for [bind]ing like this, as long as there is some injection
   of the type as [val]s. *)
Definition bind_t {A : Type} `{iv : Into A val} f (fk : A -> flow) :=
  bind f (fun v => ∃' v_typed, ens_pure (v = (into v_typed)) ;; fk v_typed).

Notation "'let\'' x '=' f1 'in' f2" :=
  (bind_t f1 (fun x => f2))
  (at level 38, x binder, right associativity, only printing) : flow_scope.

(* some more Proper instances that should really be in Propriety *)

#[global]
Instance Proper_pointwise_entails_fex : forall A,
  Proper (Morphisms.pointwise_relation A entails ====> entails)
  (@fex A).
Proof.
  unfold Proper, respectful, Morphisms.pointwise_relation.
  intros * Hpointwise.
  fdestruct xn.
  fexists xn.
  auto.
Qed.

(*#[global]*)
(*Instance It_might_need_this_one_too : forall A,*)
(*  Proper (flip (Morphisms.pointwise_relation A entails) ====> flip entails)*)
(*  (@fex A).*)
(*Proof.*)
(*Admitted.*)

#[global]
Instance bient_ent_subrelation : subrelation bientails entails.
Proof.
  unfold subrelation.
  setoid_rewrite bientails_iff_entails.
  intros. intuition.
Qed.

#[global]
Instance bient_flip_ent_subrelation : subrelation bientails (flip entails).
Proof.
  unfold subrelation, flip.
  setoid_rewrite bientails_iff_entails.
  intros. intuition.
Qed.

#[global]
Instance ent_ent_under_subrelation : forall env, subrelation entails (entails_under env).
Proof.
  unfold subrelation, entails, entails_under.
  intros. intuition.
Qed.

#[global]
Instance Proper_bind_entails_l : forall f,
  ShiftFree f ->
  Proper ((Morphisms.pointwise_relation val entails) ====> entails) (bind f).
Proof.
  unfold Proper, respectful, Morphisms.pointwise_relation, entails.
  intros * Hent * Hpointwise * Hbind. subst.
  inverts Hbind.
  - applys* s_bind.
  - no_shift.
Qed.

(* we define some typeclasses weaker than ShiftFree, but still allow for nice rewriting properties *)
(*Class AssociateWithSeq (f : flow) := {*)
(*  assoc_with_seq_proof : forall f1 fk, bientails (bind (f ;; f1) fk) (f ;; bind f1 fk)*)
(*}.*)
(**)
(*#[global]*)
(*Instance Associate_with_seq_sf : forall f, ShiftFree f -> AssociateWithSeq f.*)
(*Proof.*)
(*Admitted.*)

Class RewritableBinder (f : flow) : Prop := {
  rewritable_binder_proof : forall f1 f2, (forall v, entails (f1 v) (f2 v)) -> entails (bind f f1) (bind f f2)
}.

#[global]
Instance Proper_binder_rewrite : forall f,RewritableBinder f ->
  Proper (Morphisms.pointwise_relation _ entails ====> entails) (bind f).
Proof.
  unfold Proper, respectful, Morphisms.pointwise_relation.
  intros * Hbind * Ha.
  inverts Hbind.
  apply rewritable_binder_proof0.
  assumption.
Qed.

#[global]
Instance Proper_binder_rewrite_bient : forall f,RewritableBinder f ->
  Proper (Morphisms.pointwise_relation _ bientails ====> bientails) (bind f).
Proof.
  unfold Proper, respectful, Morphisms.pointwise_relation.
  intros * Hbind * Ha.
  inverts Hbind.
  apply bientails_iff_entails. split.
  - apply rewritable_binder_proof0.
    intros. lets Hv: Ha v.
    apply bientails_iff_entails in Hv.
    intuition.
  - apply rewritable_binder_proof0.
    intros. lets Hv: Ha v.
    apply bientails_iff_entails in Hv.
    intuition.
Qed.

#[global]
Instance Proper_binder_rewrite_seq : forall f,RewritableBinder f ->
  Proper (entails ====> entails) (seq f).
Proof.
  unfold Proper, respectful.
  intros * Hbind * H.
  unfold seq.
  setoid_rewrite H.
  reflexivity.
Qed.

#[global]
Instance Proper_binder_rewrite_bient_seq : forall f,RewritableBinder f ->
  Proper (bientails ====> bientails) (seq f).
Proof.
  unfold Proper, respectful.
  intros * Hbind * H.
  unfold seq.
  setoid_rewrite H.
  reflexivity.
Qed.

#[global]
Instance Rewrite_binder_sf : forall f, ShiftFree f -> RewritableBinder f.
Proof.
  intros. inverts H. constructor. intros. unfold entails. intros.
  inverts H0. 2: { no_shift. }
  applys* s_bind.
  unfold entails in H.
  apply H.
  assumption.
Qed.

#[global]
Instance Rewrite_locked_ens_state : forall P h v, RewritableBinder ((Lock.locked _ ens_state) P h v).
Proof.
  rewrite <- (lock _ ens_state).
  intros.
  apply Rewrite_binder_sf.
  unfold ens_state. constructor. shiftfree.
Qed.

Lemma norm_bind_req_conv : forall H f fk, entails (req H (bind f fk)) (bind (req H f) fk).
Proof.
Admitted.

Lemma norm_bind_all_l_conv : forall A fk1 fk, entails (@fall A (fun b => (bind (fk1 b) fk))) (bind (fall fk1) fk).
Proof.
Admitted.

Lemma norm_bind_ex_l_conv : forall A fk1 fk, entails (@fex A (fun b => (bind (fk1 b) fk))) (bind (fex fk1) fk).
Proof.
Admitted.

#[global]
Instance Rewrite_binder_req : forall H f, RewritableBinder f -> RewritableBinder (req H f).
Proof.
  intros * H. inverts H. constructor. intros * Hf. apply rewritable_binder_proof0 in Hf.
  rewrite norm_bind_req.
  rewrite <- (norm_bind_req_conv _ _ f2).
  apply entl_req_req; try xsimpl.
  exact Hf.
Qed.

#[global]
Instance Rewrite_binder_fall : forall A f, (forall v, RewritableBinder (f v)) -> RewritableBinder (@fall A f).
Proof.
  intros * H. constructor. intros * Hf.
  (*apply rewritable_binder_proof0 in Hf.*)
  Search (bind (fall _) _).
  rewrite norm_bind_all_l.
  rewrite <- (norm_bind_all_l_conv _ _ f2).
  apply entl_all_r. intros b.
  apply entl_all_l. exists b.
  pose proof (H b).
  inverts H0.
  apply rewritable_binder_proof0.
  exact Hf.
Qed.

#[global]
Instance Rewrite_binder_fex : forall A f, (forall v, RewritableBinder (f v)) -> RewritableBinder (@fex A f).
Proof.
  intros * H. constructor. intros * Hf.
  (*apply rewritable_binder_proof0 in Hf.*)
  Search (bind (fall _) _).
  rewrite norm_bind_ex_l.
  rewrite <- (norm_bind_ex_l_conv _ _ f2).
  fdestruct b. fexists b.
  pose proof (H b).
  inverts H0.
  apply rewritable_binder_proof0.
  exact Hf.
Qed.

#[global]
Instance Proper_bind_t_entails_l : 
  forall A I,
  Proper (entails ====> eq ====> entails) (@bind_t A I).
Proof.
  unfold Proper, respectful, Morphisms.pointwise_relation, bind_t.
  intros * Hent * Hpointwise.
  rewrite Hpointwise.
  rewrite Hent.
  reflexivity.
Qed.

#[global]
Instance Proper_bind_t_entails_r :
  forall A I f, RewritableBinder f ->
  Proper ((Morphisms.pointwise_relation _ entails) ====> entails) (@bind_t A I f).
Proof.
  unfold Proper, respectful, Morphisms.pointwise_relation, bind_t.
  intros * Hent * Hpointwise.
  inverts Hent.
  apply rewritable_binder_proof0. intros v.
  fdestruct v_typed. fexists v_typed.
  apply entails_ens_seq; try (xsimpl; auto).
  apply Hpointwise.
Qed.

(**)
(*#[global]*)
(*Instance Proper_bind_t_bientails_l : *)
(*  forall A I,*)
(*  Proper (bientails ====> eq ====> bientails) (@bind_t A I).*)
(*Proof.*)
(*  unfold Proper, respectful, Morphisms.pointwise_relation, bind_t.*)
(*  intros * Hbient * Hpointwise_bient.*)
(*  apply bientails_iff_entails.*)
(*  apply bientails_iff_entails in Hbient.*)
(*  destruct Hbient as [Hxy Hyx].*)
(*  subst.*)
(*  split.*)
(*  - setoid_rewrite Hxy. reflexivity.*)
(*  - setoid_rewrite Hyx. reflexivity.*)
(*Qed.*)
(**)
(*#[global]*)
(*Instance Proper_bind_t_bientails_r :*)
(*  forall A I f,*)
(*  ShiftFree f ->*)
(*  Proper ((Morphisms.pointwise_relation _ bientails) ====> bientails) (@bind_t A I f).*)
(*Proof.*)
(*  unfold Proper, respectful, Morphisms.pointwise_relation, bind_t.*)
(*  intros * Hsf * Hpointwise_bient.*)
(*  apply bientails_iff_entails.*)
(*  setoid_rewrite bientails_iff_entails in Hpointwise_bient.*)
(*  apply forall_conj_inv_1 in Hpointwise_bient.*)
(*  destruct Hpointwise_bient as [Hxy Hyx].*)
(*  split.*)
(*  - Search (bind _ (fun _ => fex _)).*)
(*    rewrite norm_bind_ex_r. 2: { exact shift_free_pf. }*)
(*    fdestruct v_typed.*)
(**)
(*    rewrite <- entailsR_is_entails.*)
(*    rewrite norm_bind_ex_r. 2: { exact shift_free_pf. }*)
(*    rewrite entailsR_is_entails.*)
(*    fexists v_typed.*)
(**)
(*    setoid_rewrite Hxy.*)
(*    reflexivity.*)
(*  - rewrite norm_bind_ex_r. 2: { exact shift_free_pf. }*)
(*    fdestruct v_typed.*)
(**)
(*    rewrite <- entailsR_is_entails.*)
(*    rewrite norm_bind_ex_r. 2: { exact shift_free_pf. }*)
(*    rewrite entailsR_is_entails.*)
(*    fexists v_typed.*)
(**)
(*    setoid_rewrite Hyx.*)
(*    reflexivity.*)
(*Qed.*)
