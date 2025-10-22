(* Proofs for simple entailments. These are meant to closely mirror
   Heifer's proofs of the same, as a test to see how to automatically generate them *)

(* The main strategy is to have Heifer's proof log only output
   high-level tactics; it is up to the Coq side to perform
   the same low-level rewrites and transformations that Heifer does. *)

From ShiftReset Require Import Logic Automation Entl Norm Propriety.
From ShiftReset Require ExamplesEnt.
Local Open Scope string_scope.

Definition vplus (a b:val) : val :=
  match a, b with
  | vint a, vint b => vint (a + b)
  | _, _ => vunit
  end.

(* deep embedding of Heifer's [state]. maybe this gives our tactics
   more fine-grained control over shuffling around the ens clauses? *)

Inductive hpred :=
  | hsplit (lhs : hpred) (rhs : hpred)
  | hpts_to (p : loc) (v : val)
  | hemp.

Open Scope list_scope.
Fixpoint hprop_of_hpred pred :=
  match pred with
  | hsplit lhs rhs => (hprop_of_hpred lhs) \* (hprop_of_hpred rhs)
  | hpts_to p v => p ~~> v
  | hemp => \[]
  end.

Fixpoint conjuncts_of_hpred hp :=
  match hp with
  | hpts_to p v => cons (p, v) nil
  | hsplit r1 r2 => conjuncts_of_hpred r1 ++ conjuncts_of_hpred r2
  | hemp => nil
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

(* GET ME OUT OF SETOID HELL PLEASE *)
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

Lemma ens_duplicate_pure_heap : forall P H,
  entails (ens (fun r => \[P r] \* H)) (ens (fun r => \[P r]) ;; ens (fun r => \[P r] \* H)).
Proof.
  unfold entails.
Admitted.

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

(* Rewrites all [ens Q] present in the goal such that [postcond_representable Q] to an [ens_state].

  - break up conjunct hprops
  - add to heap or pure state, respectively
*)

(* what i want:
   - for every (ens ?Q) in the goal entailment,
    create a [forall (free vars in Q), postcond_representable ?Q] goal, and solve it via some auto tactic
   - then use it to rewrite the ens to an ens_state  *)

(* alternatively we can do this purely via rewrite rules but i'd rather do it in 
  a structured way *)
Ltac rew_ens_hprop_to_state :=
  idtac "TODO".

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

(* start by mapping over Heifer's normalization rules to Coq *)

(* these apply to both sides, do we need to write these in terms of bientails? *)
(* but if we do, how will coq know to only apply them in one direction,
   in both the left and right-hand sides? *)

Check norm_bind_val.

Corollary norms_bind_t_val : forall A I fk v, entails (@bind_t A I (ens_state True hemp (into v)) fk) (fk v).
Proof.
Admitted.

(* we have norm_bind_trivial but only for shiftfree specs *)
Check norm_bind_trivial_sf.

Corollary norms_bind_t_trivial : forall A I f1,
  entails (@bind_t A I f1 (fun res => ens_state True hemp (into res))) f1.
Proof.
Admitted.

Check norm_bind_disj.
 
Corollary norm_bind_t_disj : forall A I f1 f2 fk,
  entails (@bind_t A I (disj f1 f2) fk)
  (disj (bind_t f1 fk) (bind_t f1 fk)).
Proof.
Admitted.

(* this rule is norm_seq_disj_r, specialized for ens *)
Theorem norm_seq_ens_disj : forall Q f1 f2,
  entails (ens Q ;; (disj f1 f2)) (disj (ens Q ;; f1) (ens Q ;; f2)).
Proof.
  intros. apply norm_seq_disj_r. shiftfree.
Qed.

Corollary norms_seq_ens_disj : forall p h v f1 f2,
  entails (ens_state p h v ;; (disj f1 f2))
  (disj (ens_state p h v ;; f1) (ens_state p h v ;; f2)).
Proof.
Admitted.

Check norm_bind_req.

Corollary norm_bind_t_req : forall A I P h f fk,
  entails
  (@bind_t A I (req_state P h f) fk)
  (req_state P h (bind_t f fk)).
Proof.
Admitted.

(* we have norm_bind_ex, but only in one direction *)
Check norm_bind_ex_l.

Corollary norm_bind_t_ex_l : forall A I AEx (f : AEx -> flow) (fk : A -> flow),
  entails (@bind_t A I (∃' b, f b) fk) (∃' b, (bind_t (f b) fk)).
Proof.
Admitted.

(* we also have norm_bind_all, but only in one direction *)
Check norm_bind_all_l.

Corollary norm_bind_t_all_l : forall A I AEx (f : AEx -> flow) (fk : A -> flow),
  entails (@bind_t A I (∀' b, f b) fk) (∀' b, (bind_t (f b) fk)).
Proof.
Admitted.

(* norm_bind_assoc_sf specialized for ens *)
(* there is also norm_bind_assoc_sf_equiv, which is a bientailment *)
Theorem norm_bind_assoc_ens : forall Q f1 f2,
  entails (bind (bind (ens Q) f1) f2) (bind (ens Q) (fun y => (bind (f1 y) f2))).
Proof.
  intros. apply norm_bind_assoc_sf. shiftfree.
Qed.

Corollary norms_bind_t_assoc_ens : forall A1 I1 A2 I2 P h v f1 f2,
  entails (@bind_t A1 I1 (@bind_t A2 I2 (ens_state P h v) f1) f2)
    (bind_t (ens_state P h v) (fun y => (bind_t (f1 y) f2))).
Proof.
Admitted.

Theorem norm_seq_val : forall v f,
  entails (ens (fun res => \[res = v]) ;; f) f.
Proof.
  intros. apply norm_seq_pure_l.
Qed.

Corollary norms_seq_val : forall v P h f,
  entails (ens_state P h v ;; f) f.
Proof.
Admitted.

Theorem norm_seq_ens_ex : forall A Q (f : A -> flow),
  entails (ens Q ;; fex (fun x => f x)) (fex (fun x => ens Q ;; f x)).
Proof.
  intros. apply norm_seq_ex_r. shiftfree.
Qed.

Corollary norms_seq_ens_ex : forall A P h v (f : A -> flow),
  entails (ens_state P h v ;; fex f) (fex (fun x => ens_state P h v  ;; f x)).
Proof.
Admitted.

Theorem norm_seq_ens_all : forall A Q (f : A -> flow),
  entails (ens Q ;; fall (fun x => f x)) (fall (fun x => ens Q ;; f x)).
Proof.
  intros. apply norm_seq_all_r. shiftfree.
Qed.

Corollary norms_seq_ens_all : forall A P h v (f : A -> flow),
  entails (ens_state P h v ;; fall f) (fall (fun x => ens_state P h v  ;; f x)).
Proof.
Admitted.

(* a with-trailing versoin of norm_seq_ens_all *)
Theorem norm_seq_ens_seq_all : forall A Q (f : A -> flow) fk,
  entails 
  (ens Q ;; (∀' x, f x) ;; fk)
  (∀' x, (ens Q ;; f x ;; fk)).
Proof.
  intros.
  rewrite norm_seq_assoc_sf. 2: { shiftfree. }
  rewrite norm_seq_all_r. 2: { shiftfree. }
  fintros b.
  apply entl_seq_all_l. exists b.
  rewrite <- norm_seq_assoc_sf. 2: { shiftfree. }
  reflexivity.
Qed.

Theorem norms_seq_ens_seq_all : forall A P h v (f : A -> flow) fk,
  entails (ens_state P h v  ;; fall (fun x => f x) ;; fk) (fall (fun x => ens_state P h v  ;; f x) ;; fk).
Proof.
Admitted.

(* specialization of norm_bind_seq_assoc for ens *)
Theorem norm_bind_seq_ens : forall Q f fk,
  entails (bind (ens Q ;; f) fk) (ens Q ;; bind f fk).
Proof.
  intros.
  rewrite norm_bind_seq_assoc. 2: { shiftfree. }
  reflexivity.
Qed.

Corollary norms_bind_seq_ens : forall A I P h v f fk,
  entails (@bind_t A I (ens_state P h v ;; f) fk) (ens_state P h v ;; bind_t f fk).
Proof.
Admitted.

Check norm_ens_ens_void.

(* we can prove a more general version where P is allowed to 
  contain heap conditions
  but we want to preserve the desired behavior of only lifting pure conditions
   up the chain *)
Theorem norm_ens_heap_ens_pure : forall Q P,
  entails
  (ens_ Q ;; ens_ \[P])
  (ens_ \[P] ;; ens_ Q).
Proof.
  intros.
  (* this is proven, just under a different name *)
  apply norm_seq_ens_ens_pure.
Qed.

Corollary norms_ens_heap_ens_pure : forall h P,
  entails 
  (ens_heap h ;; ens_pure P) (ens_pure P ;; ens_heap h).
Proof.
Admitted.

(* the with-trailing version of norm_ens_heap_ens_pure *)
Theorem norm_seq_ens_heap_ens_pure : forall Q P f,
  entails
  (ens_ Q ;; ens_ \[P] ;; f)
  (ens_ \[P] ;; ens_ Q ;; f).
Proof.
  intros.
  rewrite norm_seq_assoc_sf. 2: { shiftfree. }
  rewrite norm_seq_ens_ens_pure.
  rewrite <- norm_seq_assoc_sf. 2: { shiftfree. }
  reflexivity.
Qed.

Theorem norm_ens_pure_ens_pure : forall P1 P2,
  entails
  (ens_ \[P1] ;; ens_ \[P2])
  (ens_ \[P1 /\ P2]). 
Proof.
  intros.
  rewrite norm_ens_ens_void_combine.
  rewrite hstar_hpure_conj.
  reflexivity.
Qed.

Corollary norms_ens_pure_ens_pure : forall P1 P2,
  entails 
  (ens_pure P1 ;; ens_pure P2) (ens_pure (P1 /\ P2)).
Proof.
Admitted.

(* the with-trailing version of the norm_ens_pure_ens_pure *)
Theorem norm_seq_ens_pure_ens_pure : forall P1 P2 f,
  entails
  (ens_ \[P1] ;; ens_ \[P2] ;; f)
  (ens_ \[P1 /\ P2] ;; f). 
Proof.
  intros.
  rewrite norm_seq_assoc_sf. 2: { shiftfree. }
  rewrite norm_ens_pure_ens_pure.
  reflexivity.
Qed.

Corollary norms_seq_ens_pure_ens_pure : forall P1 P2 f,
  entails 
  (ens_pure P1 ;; ens_pure P2 ;; f) (ens_pure (P1 /\ P2) ;; f).
Proof.
Admitted.

(* we have no way of mentioning "heap-only" ens,
   so we skip norm_ens_heap_ens_heap and norm_seq_ens_heap_ens_heap for now *)

Theorem norms_ens_heap_ens_heap : forall h1 h2,
  entails
  (ens_heap h1 ;; ens_heap h2) (ens_heap (hsplit h1 h2)).
Proof.
Admitted.

Theorem norms_seq_ens_heap_ens_heap : forall h1 h2 f,
  entails
  (ens_heap h1 ;; ens_heap h2 ;; f) (ens_heap (hsplit h1 h2) ;; f).
Proof.
Admitted.

(* we have norm_seq_assoc for shift-free formulas *)
Check norm_seq_assoc_sf.

Theorem norms_seq_ens_emp : forall f,
  entails (ens_pure True ;; f) f.
Proof.
Admitted.

Theorem norms_req_ens_emp : forall f,
  entails (req_state True hemp f) f.
Proof.
Admitted.

(* these rules only apply to the left hand side *)

Theorem norm_seq_all : forall A (f : A -> flow) fk,
  entails ((∀' x, f x) ;; fk) (∀' x, f x ;; fk).
Proof.
  intros.
  fintros x.
  apply entl_seq_all_l.
  exists x.
  reflexivity.
Qed.

Theorem norm_ex_all : forall A (f : A -> flow) fk,
  entails ((∃' x, f x) ;; fk) (∃' x, f x ;; fk).
Proof.
  intros.
  fdestruct x.
  fexists x.
  reflexivity.
Qed.

(* the "base case" of Heifer entailment *)
Lemma ent_ens_empty : entails (ens_pure True) (ens_pure True).
Proof.
  apply entl_ens_single.
  xsimpl; auto.
Qed.

(** TACTICS **)
(* there is also a base case for req \[True], but
   here there is no way to represent a trailing [req] *)

Ltac fempty := apply ent_ens_empty.

Ltac fsolve_pure := auto.

Ltac fsolve_heap := xsimpl.

Ltac fsingle_ens :=
  (* operates on goals of the form 
     entails (ens ?lhs) (ens ?rhs)
     entails_under _ (ens ?lhs) (ens ?rhs)

     has to
     - use biabduction to discharge the heap constraints
     we need to model the addition of the xpure constraints somehow...?
     - use some magic to discharge the pure constraints
     look into: smtcoq, coqhammer, crush from CPDT
   *)
  rewrite ens_state_is_ens; apply entl_ens_single; fsolve_pure.

(* this should maybe be packaged with the hpred? *)
(* maybe hpred should just be an Fmap? *)
Definition distinct_locations : hpred -> Prop.
Proof. Admitted.

(* TODO *)

Definition is_valid_hprop (hp : hprop) := exists (h : heap), hp h.

Lemma is_valid_hprop_star_exists_disj :
  forall H1 H2,
  is_valid_hprop (H1 \* H2) -> (forall h2, H2 h2 -> exists h1, H1 h1 /\ Fmap.disjoint h1 h2).
Proof.
Admitted.

Lemma biab_implies_himpl : forall Ha H1 H2 Hf,
  biab Ha H1 H2 Hf -> Ha \* H1 ==> H2 \* Hf.
Proof.
Admitted.

(* this already suffices for the simple cases,
  but the rule heifer uses is the general one involving biabduction *)
Lemma entl_ens_ens : forall f1 f2 H1 H2,
  H1 ==> H2 -> entails f1 f2 -> entails (ens_ H1 ;; f1) (ens_ H2 ;; f2).
Proof.
  intros * Hhimpl Hentails.
  rewrite Hentails.
  rewrite Hhimpl.
  reflexivity.
Qed.

Lemma entl_ens_req_cancel : forall H1 H2 f,
  entails (ens_ (H1 \* H2) ;; req H1 f) (ens_ H2 ;; f).
Proof.
  unfold entails. intros * Hensreq.
  inverts Hensreq. 2: { no_shift. }
  inverts H8. destr H7. inverts H. inverts H9.
  hinv H0. hinv H. hinv H0. subst.
  Check s_seq.
  apply (@s_seq s3 (h1 \u x2) vunit).
  - constructor. eexists. eexists. intuition. rewrite hstar_hpure_l. intuition.
  - apply (@H12 x1 (h1 \u x2)); intuition.
Qed.

(* fairly certain the [is_valid_hprop] is a technical restriction of the proof
  that can be worked around... *)
Lemma entl_ens_req_create : forall H1 H2 f,
  is_valid_hprop (H1 \* H2) ->
  entails (ens_ H2 ;; f) (ens_ (H1 \* H2) ;; req H1 f).
(* i don't think this is true.. if the heap state already contains H1
   this entailment will not proceed *)
Proof.
  intros * Hvalid. unfold entails. intros * Hens.
  lets Hexists_disj: is_valid_hprop_star_exists_disj H1 H2 Hvalid.
  inverts Hens. 2: { no_shift. }
  inverts H8. destr H7. inverts H. hinv H0. hinv H. subst.
  rewrite union_empty_l in H5. 
  lets Hheap1: Hexists_disj x0 H0.
  destr Hheap1.
  eapply (@s_seq s3 (h1 \u h0 \u x0) vunit).
  - constructor. exists vunit. exists (h0 \u x0). intuition.
    + rewrite hstar_hpure_l. intuition. hintro; intuition.
    (*+ auto. disjoint. Search (Fmap.disjoint _ (_ \u _)).*)
Abort.

Lemma req_req_iff_ens_ens_biab :
  forall Ha H1 H2 Hf f1 f2,
  biab Ha H1 H2 Hf ->
  entails (req Ha f1) (req Hf f2) -> entails (ens_ H1 ;; f1) (ens_ H2 ;; f2).
Proof.
  intros * Hbiab Hreq.
  lets Himpl: biab_implies_himpl Ha H1 H2 Hf Hbiab.
  induction Hbiab.
  - apply entl_ens_ens.
    + apply himpl_refl.
    + rewrite !norm_seq_req_emp in Hreq.
      auto.
  - rewrite !norm_seq_req_emp in Hreq.
    rewrite norm_seq_ens_empty.
    rewrite Hreq.
    rewrite <- (hstar_hempty_r Hf) at 1.
    rewrite (entl_ens_req_cancel Hf \[] f2).
    rewrite norm_seq_ens_empty.
    reflexivity.
  - rewrite norm_req_req in Hreq.
    admit.
  - (* this seems easy enough *) admit.
  - (* see transpose_pts_diff for reference ... *) admit.
Admitted.
    
(* i will ask but i am 99% sure this is unsound.
  consider f1 = f2 = (ens_ (loc ~~> val)). *)
Lemma req_lhs_becomes_ens : forall loc val f1 f2, entails (req (loc ~~> val) f1) f2 -> entails f1 (ens_ (loc ~~> val) ;; f2).
Proof. 
  intros * Hreq.
  unfold entails.
  intros * Hf1.
  unfold entails in Hreq.
  eapply (@s_seq s1 h1 vunit).
  2: {
    apply Hreq.
    constructor.
    intros. 
    hinv H. subst.
    admit.
  }
Abort.

Lemma ens_lhs_becomes_req : forall H f1 f2, entails (ens_ H ;; f1) f2 -> entails f1 (req H f2).
Proof.
  intros * Hens.
  unfold entails.
  intros * Hf1.
  constructor.
  intros.
  (* now we want to use Hens *)
  unfold entails in Hens.
  apply Hens.
  apply (@s_seq s1 h1 vunit).
  - constructor. eexists. eexists. intuition.
    hintro. intuition.
  - auto.
Qed.

(* more general version that directly uses [himpl] instead of the inductively defined [biab] *)
Lemma req_req_iff_ens_ens :
  forall Ha H1 H2 Hf f1 f2,
  Ha \* H1 ==> H2 \* Hf ->
  (entails (req Ha f1) (req Hf f2) -> entails (ens_ H1 ;; f1) (ens_ H2 ;; f2)).
Proof.
  intros * Hbiab.
  - intros Hreq.
    apply (entl_ens_ens _ _ _ _ Hbiab) in Hreq.
    rewrite hstar_comm in Hreq.
    (*rewrite entl_ens_req_cancel in Hreq at 1.*)
    (* intuitively, this should be true because if the entail hypothesis holds,
       any heap pre-state in a heap pre-post pair must contain both Ha and Hf *)
Abort.

(* [entl_req_req] is a corollary of this! *)

(*Lemma entl_match_ens_state :*)
(*  (* suppose biab h1 h2 returns antiframe (ap, ah) and frame (fp, fh): *)*)
(*  forall P1 P2 h1 h2 ah ap fh fp f v,*)
(*  (P1 /\ ap /\ distinct_locations h1 -> P2 /\ fp /\ distinct_locations h2) ->*)
(*  hpred_biab ah h1 h2 fh ap ->*)
(*  entails (req_state True ah f) (req_state True fh f) ->*)
(*  entails (ens_state P1 h1 v ;; f) (ens_state P2 h2 v ;; f).*)
(*Proof. Admitted.*)

Ltac fsolve_biabduction := idtac "TODO".

Lemma entl_state_ens_ens : forall P1 h1 v1 P2 h2 v2 f1 f2,
  (\[P1] \* hprop_of_hpred h1 ==> \[P2] \* hprop_of_hpred h2) ->
  v1 = v2 ->
  entails f1 f2 ->
  entails (ens_state P1 h1 v1 ;; f1) (ens_state P2 h2 v2 ;; f2).
Proof.
  intros * Hhimpl Hval Hent.
  subst.
  rew_state_to_hprop.
  rewrite Hent.
  rewrite <- norm_ens_ens_void_l.
  with_entailsR (rewrite <- norm_ens_ens_void_l).
  rewrite <- norm_seq_assoc_sf by shiftfree.
  with_entailsR (rewrite <- norm_seq_assoc_sf by shiftfree).
  apply entl_ens_ens.
  - auto.
  - reflexivity.
Qed.

Ltac fmatch_ens :=
  (* operates on goals of the form
     entails (ens ?lhs ;; ?lnext) (ens ?rhs ;; ?rnext)

     - uses biabduction to eliminate matching locations in lhs/rhs
     - checks resulting pure condition
     - turns goal into
     entails (req (antiframe) lnext) (req (frame) rnext)
   *)
  apply entl_state_ens_ens; [unfold hprop_of_hpred; fsolve_heap; try fsolve_pure | fsolve_pure | ].

(* TODO: use Ltac2? *)

(* split all ensures clauses up to 
  - one representing the result value
   - one representing pure constraints
   - one representing heap constraints *)

Check norm_rearrange_ens. 

(* Splitting a single ens_state into ens_pure ens_heap and ret *)
Lemma norms_split_ens : forall P h v, bientails (ens_state P h v) (ens_state P hemp vunit ;; ens_state True h vunit ;; ens_state True hemp v).
Proof. Admitted.

Lemma norms_remove_empty_void : forall f, bientails (ens_state True hemp vunit ;; f) f.
Proof. Admitted.

Lemma norms_remove_empty_ret : forall P h, bientails (ens_state P h vunit ;; ens_state True hemp vunit) (ens_state P h vunit).
Proof. Admitted.

Ltac fsplit_ens :=
  setoid_rewrite norms_split_ens;
  repeat (setoid_rewrite norms_remove_empty_void); repeat (setoid_rewrite norms_remove_empty_ret).

Ltac fapply_one_norm_rule :=
  rewrite norms_bind_t_trivial.

(* before normalizing, heifer first splits all ens into pure and
   heap components. *)
Ltac fnormalize :=
  fsplit_ens;
  repeat fapply_one_norm_rule.

Ltac freduce_shrs :=
  idtac "TODO".

Ltac fsimpl :=
repeat (freduce_shrs; fnormalize).

(*** NO GUARANTEE EVERYTHING FROM THIS POINT COMPILES *)

(* IDEA: ens_t, similar to [bind_t] that allows for the [res] to be any type
  we can convert to val *)

(* [fexists] corresponds to the "exists on the right" step
  need to decide whether to use entails/entails_under,
   as this decides whether or not [fexists]/[fexists_old] will be used... *)


(* this Opaque declaration is needed, otherwise
   [frewrite_ens_to_ens_state_one] will attempt to rewrite an existing [ens_state] *)
(* for more fine-grained control over this we may want to look into SSReflect's [lock] *)
Opaque ens_state.

(* this can be instantly discharged *)
Example test10 : entails
  (ens (fun r => \[r = 0]))
  (ens (fun r => \[r = 0])).
Proof.
  rew_hprop_to_state.
  fsingle_ens.
Qed.

(* bind normalization *)
Example test6 : entails
  (bind_t (ens (fun r => \[r = 0])) (fun j => ens (fun r => \[r = j])))
  (ens (fun r => \[r = 0])).
Proof.
  rew_hprop_to_state.

  fsimpl.
  fsingle_ens.
Qed.

#[global]
Instance The_exact_Proper_instance_the_test4_proof_needs_to_work_as_intended : forall A,
  Proper (respectful (flip (Morphisms.pointwise_relation A entails)) (flip eq))
  (@fex A).
Proof.
Admitted.

#[global]
Instance It_might_need_this_one_too : forall A,
  Proper (respectful (flip (Morphisms.pointwise_relation A eq)) (flip eq))
  (@fex A).
Proof.
Admitted.

#[global]
Instance And_this_one_I_guess:
  Proper (respectful eq (respectful entails eq)) seq.
Proof.
Admitted.

#[global]
Instance Me_when_the_setoid_rewrite_failed_UNDEFINED_EVARS:
  Proper (respectful (flip eq) (respectful (flip entails) (flip eq))) seq.
Proof.
Admitted.

(* existential handling *)
Example test9 : entails
  (bind_t (ens (fun r => \[r = 0])) (fun j => ens (fun r => \[r = j])))
  (∃' r, ens (fun res => \[res = r])).
Proof.
  rew_hprop_to_state.
  fexists 0.
  fsimpl.
  fsingle_ens.
Qed.

(* basic heap manipulation *)
(*
  note the use of separating conjunction instead of /\ (though in Heifer this is purely cosmetic)

  also note the [vloc] constructor appearing whenever we need to treat a location
  as a pure value

  so we'll need to be able to tell if something's a reference during
  theorem translation; use the type annotations for this?

  also this detail will need to change if ever a shallow embedding of flow return
  types are used*)
Example test4 : entails
  (∃' v56, bind_t (ens (fun res => v56 ~~> 0 \* \[res = vloc v56])) (fun i => ens (fun res => \[res = vloc i])))
  (∃' i, ens (fun res => \[res = vloc i] \* i ~~> 0)).
Proof.
  rew_hprop_to_state.
  fsimpl.
  fdestruct v.
  fexists v.
  fsimpl.
  fmatch_ens.
  fsingle_ens.
Qed.


 (* this should also split the ens r. Q \* \[P r] 
     into the heap and pure parts. what rule does that?

     do we need to implement [split_ens_aux] as a tactic? *)
  (*fsimpl.*)
  (*fdestruct v.*)
  (*fexists v.*)
  (*fsimpl.*)
  (*fmatch_ens.*)
  (*fsingle_ens.*)

(* heap dereference *)
(* note the use of an existential to match the location (which needs to have type [loc])
  with the bound value (which needs to have type [val])

  maybe we can uniformly apply this to all types...
   again, this may change depending on the embedding of types
   and we won't always have "all types"

   this forms a nontrivial difference between coq and heifer specs...
   the tactics need to transparently adjust for this
   *)
Example test5 : entails
  (∃' v72, bind (ens (fun res => \[res = vloc v72] \* v72 ~~> 0))
  (fun ival =>
  ∃' i, ens_ \[ival = vloc i] ;; ∀' v73, req (i ~~> v73) (ens (fun res => \[res = v73] \* i ~~> v73))))
  (∃' i, ens (fun res => \[res = vloc i] \* i ~~> 0)).
Proof.
  fsimpl.
  (* this should also bring out v73 to the toplevel,
     but this fails because of the vloc existential... 
      the vloc existential can also be lifted to the toplevel...?*)
  fdestruct v72.
  fsimpl.
  rewrite norm_bind_ex_l.
  (* THIS SHOULD WORK *)
  Fail fbiabduction.
  (*fexists v72.*)
  (*fsimpl.*)
  (*fmatch_ens.*)
  (*fsingle_ens.*)
Abort.

(* writing to the heap *)
Example test61 : entails
  (bind (∃' v88, ens (fun res => \[res = vloc v88] \* v88 ~~> 0))
  (fun i_val =>
    ∃' i, ens_ \[i_val = vloc i] ;;
    bind (bind (∀' v89, req (i ~~> v89) (ens (fun res => \[res = v89] \* i ~~> v89)))
    (fun v85 => ens (fun res => \[res = vplus v85 1])))
    (fun v86 => 
      (∀' v90, req (i ~~> v90) (ens_ (i ~~> v86))) ;;
      ∀' v91, req (i ~~> v91) (ens (fun res => \[res = v91] \* i ~~> v91)))))
  (∃' i, ens (fun res => \[res = 1] \* i ~~> 1)).
Proof.
  (* let me work out the other simplifications first *)
Admitted.













