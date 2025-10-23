
(* Helper definitions to more closely reflect Heifer's definitions. *)

From ShiftReset Require Import Logic Automation Entl Norm Propriety.

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

Definition hpred_biab (antiframe h1 h2 frame : hpred) (obligations : Prop) : Prop :=
  obligations -> (hprop_of_hpred antiframe \* hprop_of_hpred h1 ==> hprop_of_hpred h2 \* hprop_of_hpred frame).

Definition hpred_solve_biab (h1 : hpred) (h2 : hpred)
  : exists antiframe_p antiframe_h frame_h,
    hpred_biab antiframe_h h1 h2 frame_h antiframe_p.
Proof. Admitted.


(* because a lot of existing lemmas and tactics are written in terms of the shallowly-embedded
  [ens] though, it's useful to reflect the common structure of [hprop]s into our representation *)

Inductive precond_reflect : Prop -> hpred -> hprop -> Prop :=
  | prec_refl_pure : forall P, precond_reflect P hemp \[P]
  | prec_refl_loc : forall loc val, precond_reflect True (hpts_to loc val) (loc ~~> val)
  | prec_refl_star : forall P1 h1 hp1 P2 h2 hp2,
      precond_reflect P1 h1 hp1 ->
      precond_reflect P2 h2 hp2 ->
      precond_reflect (P1 /\ P2) (hsplit h1 h2) (hp1 \* hp2).

Definition postcond_value {A : Type} (v : A) H Q := 
  (Q ===> (fun res => \[res = v] \* H))
  /\ ((fun res => \[res = v] \* H) ===> Q).

Lemma postcond_pure : forall (v : val), postcond_value v \[] (fun res => \[res = v]).
Proof. Admitted.

Lemma postcond_value_split_l : forall (v : val) H1 H2 Q, 
  postcond_value v H1 Q -> postcond_value v (H1 \* H2) (fun r => Q r \* H2). 
Proof. Admitted.

Lemma postcond_value_split_r : forall (v : val) H1 H2 Q, 
  postcond_value v H2 Q -> postcond_value v (H1 \* H2) (fun r => H1 \* Q r).
Proof. Admitted.

Inductive postcond_reflect : val -> Prop -> hpred -> postcond -> Prop :=
  | postc_refl_val v P hpred HP Q
      (Hvalue : postcond_value v HP Q)
      (Hprecond: precond_reflect P hpred HP)
      : postcond_reflect v P hpred Q.

#[global]
Instance Proper_eq_impl_eq_eq_postcond :
  Proper (eq ====> impl ====> eq ====> (Morphisms.pointwise_relation val eq) ====> impl) postcond_reflect.
Proof.
Admitted.

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

(* Rewrites all [ens_state]s present in the goal back to an [ens]. *)
  (* TODO [rew_state_to_hprop in H] *)
Ltac rew_state_to_hprop := 
  unfold ens_pure, ens_heap, ens_ret;
  rewrite ?ens_state_vunit_is_ens_state_void;
  rewrite ?ens_state_void_is_ens_void;
  unfold ens_state, hprop_of_hpred;
  (* clean up the postconditions *)
  rewrite <- ?hempty_eq_hpure_true;
  autorewrite with rew_heap;
  (*rewrite <- hempty_eq_hpure_true;*)
  (*repeat (rewrite hstar_hempty_r, hstar_hempty_l);*)
  fold hprop_of_hpred.

(* now we can write a rewriting lemma *)

(* this lets us use SLF's heap rewrite lemmas inside an ens *)
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

Lemma norm_split_req_void : forall P h Q f,
  precond_reflect P h Q -> entails (req Q f) (req_state P h f).
Proof.
Admitted.

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

(* Solves a goal of the form [precond_reflect _ _ Q]. This is most useful when
   the pure and heap states are evars, allowing to automatically derive the arguments to norm_split_ens_void. *)
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

Ltac frewrite_ens_to_ens_state_one :=
  setoid_rewrite norm_split_ens at 1;
  try match goal with
  | [ |- postcond_reflect _ _ _ _ ] => 
      eapply postc_refl_val;
      [ fsolve_post_value | fsolve_prec_reflect ]
  end;
  autorewrite with rew_simpl_pure.

(* A hack to force Coq to only rewrite the right-hand side of an entailment. *)
Definition entailsR a b := entails b a.

Lemma entailsR_is_entails : forall a b, entailsR a b = entails b a.
Proof. reflexivity. Qed.

(* Hide the existing Proper instance for entails, since that lets Coq rewrite the
  left-hand side of an entailsR *)
Typeclasses Opaque entailsR.

Instance Proper_entails_entailsR :
  Proper (flip entails ====> eq ====> impl) entailsR.
Proof.
Admitted.

Instance Proper_bientails_entailsR :
  Proper (bientails ====> eq ====> iff) entailsR.
Proof.
Admitted.

Ltac with_entailsR_base tac :=
  rewrite <- entailsR_is_entails;
  tac;
  rewrite entailsR_is_entails.

Tactic Notation "with_entailsR" tactic(tac) := with_entailsR_base ltac:(tac).

Ltac rew_hprop_to_state :=
  (with_entailsR (repeat frewrite_ens_to_ens_state_one));
  (repeat frewrite_ens_to_ens_state_one).

Lemma norm_seq_ens_ret_ens_pure : 
  forall P v, entails (ens_ret v ;; ens_pure P) (ens_pure P ;; ens_ret v).
Proof.
Admitted.

Lemma norm_seq_ens_ret_ens_heap :
  forall H v, entails (ens_ret v ;; ens_heap H) (ens_heap H ;; ens_ret v).
Proof.
Admitted.

Lemma norm_seq_ens_ret_combine :
  forall v, entails (ens_ret v ;; ens_ret v) (ens_ret v).
Proof.
Admitted.

Lemma norm_seq_seq_ens_ret_ens_pure : 
  forall P v fk, entails (ens_ret v ;; ens_pure P ;; fk) (ens_pure P ;; ens_ret v ;; fk).
Proof.
Admitted.

Lemma norm_seq_seq_ens_ret_ens_heap :
  forall H v fk, entails (ens_ret v ;; ens_heap H ;; fk) (ens_heap H ;; ens_ret v ;; fk).
Proof.
Admitted.

Lemma norm_seq_seq_ens_ret_combine :
  forall v fk, entails (ens_ret v ;; ens_ret v ;; fk) (ens_ret v ;; fk).
Proof.
Admitted.

Hint Rewrite
  norm_seq_ens_ret_ens_pure
  norm_seq_ens_ret_ens_heap
  norm_seq_ens_ret_combine
  norm_seq_seq_ens_ret_ens_pure
  norm_seq_seq_ens_ret_ens_heap
  norm_seq_seq_ens_ret_combine
  : rew_reorder_ens.


Class Into (A : Type) (B : Type)  := {
  into : A -> B
}.

Instance Into_val_val : Into val val := {
  into := id
}.

Instance Into_loc_val : Into loc val := {
  into := vloc
}.

Instance Into_int_val : Into int val := {
  into := vint
}.

(* It may be useful to work with bound values with other types than [val].
  This implements support for [bind]ing like this, as long as there is some injection
   of the type as [val]s. *)
Definition bind_t {A : Type} `{iv : Into A val} f (fk : A -> flow) :=
  bind f (fun v => ∃' v_typed, ens_pure (v = (into v_typed)) ;; fk v_typed).

Notation "'let\'' x '=' f1 'in' f2" :=
  (bind_t f1 (fun x => f2))
  (at level 38, x binder, right associativity, only printing) : flow_scope.

#[global]
Instance Proper_bind_t_entails_l : 
  forall A I,
  Proper (entails ====> (Morphisms.pointwise_relation _ entails) ====> entails) (@bind_t A I).
Proof.
Admitted.

#[global]
Instance Proper_bind_t_bientails_l : 
  forall A I,
  Proper (bientails ====> (Morphisms.pointwise_relation _ bientails) ====> bientails) (@bind_t A I).
Proof.
Admitted.

