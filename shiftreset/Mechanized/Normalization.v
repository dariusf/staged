
(* Porting over normalization rules.
   Some are largely unchanged from Norm; aside from the use of bind_t instead of bind. *)
From ShiftReset Require Import Logic Automation Entl Norm Propriety Norm.
From ShiftReset.Mechanized Require Import State.

(* TODO apply these on more than one side? *)

Check norm_bind_val.

Corollary norms_bind_t_val : forall A I fk v, entails (@bind_t A I (ens_state True hemp (into v)) fk) (fk v).
Proof.
  intros.
  unfold bind_t.
  rew_state_to_hprop.
  rewrite norm_bind_val.
  fdestruct v_typed.
  rewrite ens_vunit_is_ens_void.
  rewrite hstar_hempty_r.
  fentailment.
  intros H.
  apply into_inj in H.
  subst.
  reflexivity.
Qed.

Corollary norms_bind_t_val2 : forall fk (v : val), entails (bind_t (ens_state True hemp v) fk) (fk v).
Proof.
  apply norms_bind_t_val.
Qed.

(* we have norm_bind_trivial but only for shiftfree specs *)
Check norm_bind_trivial_sf.


#[global]
Instance ShiftFree_fex : forall A (f : A -> flow),
  (forall v, ShiftFree (f v)) -> ShiftFree (fex f).
Proof.
Admitted.

#[global]
Instance Proper_pointwise_entails_fall : forall A,
  Proper (Morphisms.pointwise_relation A entails ====> entails)
  (@fall A).
Proof.
Admitted.

#[global]
Instance Proper_pointwise_bientails_fall : forall A,
  Proper (Morphisms.pointwise_relation A bientails ====> bientails)
  (@fall A).
Proof.
Admitted.

#[global]
Instance ShiftFree_fall : forall A (f : A -> flow),
  (forall v, ShiftFree (f v)) -> ShiftFree (fall f).
Proof.
Admitted.

#[global]
Instance Proper_bind_pointwise_entails_bind :
  forall A I H f,
  ShiftFree f ->
  Proper ((Morphisms.pointwise_relation _ entails) ====> entails) (@bind_t A I (req H f)).
Proof.
Admitted.

#[global]
Instance Proper_req_state :
  forall P H,
  Proper (entails ====> entails) (req_state P H).
Proof.
Admitted.

#[global]
Instance Proper_req_locked_state :
  forall P H,
  Proper (entails ====> entails) ((locked _ req_state) P H).
Proof.
Admitted.

(*Lemma norm_bind_ex_r : forall A f (fkk : A -> val -> flow),*)
(*  entails (bind f (fun x => fex (fun v => fkk v x)))*)
(*    (fex (fun v => (bind f (fun x => fkk v x)))).*)
(*Proof.*)
(*Admitted.*)

Corollary norms_bind_t_trivial : forall A I f1,
  shift_free f1 -> entails (@bind_t A I f1 (fun res => ens_state True hemp (into res))) f1.
Proof.
Admitted.

Check norm_bind_disj.
 
Corollary norm_bind_t_disj : forall A I f1 f2 fk,
  entails (@bind_t A I (disj f1 f2) fk)
  (disj (bind_t f1 fk) (bind_t f2 fk)).
Proof.
  intros. unfold bind_t. rewrite norm_bind_disj.
  apply entl_disj_l.
  - apply entl_disj_r_l. reflexivity.
  - apply entl_disj_r_r. reflexivity.
Qed.

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
  intros. rew_state_to_hprop.
  apply norm_seq_disj_r.
  shiftfree.
Qed.

Check norm_bind_req.

Corollary norm_bind_t_req : forall A I P h f fk,
  entails
  (@bind_t A I (req_state P h f) fk)
  (req_state P h (bind_t f fk)).
Proof.
  intros. rew_state_to_hprop. unfold bind_t.
  rewrite norm_bind_req.
  reflexivity.
Qed.

(* we have norm_bind_ex, but only in one direction *)
Check norm_bind_ex_l.

Corollary norm_bind_t_ex_l : forall A I AEx (f : AEx -> flow) (fk : A -> flow),
  entails (@bind_t A I (∃' b, f b) fk) (∃' b, (bind_t (f b) fk)).
Proof.
  intros. rew_state_to_hprop. unfold bind_t.
  rewrite norm_bind_ex_l.
  reflexivity.
Qed.

(* we also have norm_bind_all, but only in one direction *)
Check norm_bind_all_l.

Corollary norm_bind_t_all_l : forall A I AEx (f : AEx -> flow) (fk : A -> flow),
  entails (@bind_t A I (∀' b, f b) fk) (∀' b, (bind_t (f b) fk)).
Proof.
  intros. rew_state_to_hprop. unfold bind_t.
  rewrite norm_bind_all_l.
  reflexivity.
Qed.

(* norm_bind_assoc_sf specialized for ens *)
(* there is also norm_bind_assoc_sf_equiv, which is a bientailment *)
Theorem norm_bind_assoc_ens : forall Q f1 f2,
  entails (bind (bind (ens Q) f1) f2) (bind (ens Q) (fun y => (bind (f1 y) f2))).
Proof.
  intros. 
  rewrite norm_bind_assoc_sf.
  - reflexivity.
  - shiftfree.
Qed.

Corollary norms_bind_t_assoc_ens : forall A1 I1 A2 I2 P h v f1 f2,
  entails (@bind_t A1 I1 (@bind_t A2 I2 (ens_state P h v) f1) f2)
    (bind_t (ens_state P h v) (fun y => (bind_t (f1 y) f2))).
Proof.
  intros. rew_state_to_hprop. unfold bind_t.
  rewrite norm_bind_assoc_ens.
  setoid_rewrite norm_bind_ex_l.
  setoid_rewrite norm_reassoc_ens_void.
  reflexivity.
Qed.

Theorem norm_seq_val : forall v f,
  entails (ens (fun res => \[res = v]) ;; f) f.
Proof.
  intros. apply norm_seq_pure_l.
Qed.

Corollary norms_seq_val : forall v f,
  entails (ens_state True hemp v ;; f) f.
Proof.
  intros. rew_state_to_hprop. apply norm_seq_val.
Qed.

Theorem norm_seq_ens_ex : forall A Q (f : A -> flow),
  entails (ens Q ;; fex (fun x => f x)) (fex (fun x => ens Q ;; f x)).
Proof.
  intros. apply norm_seq_ex_r. shiftfree.
Qed.

Corollary norms_seq_ens_ex : forall A P h v (f : A -> flow),
  entails (ens_state P h v ;; fex f) (fex (fun x => ens_state P h v  ;; f x)).
Proof.
  intros. rew_state_to_hprop. rewrite norm_seq_ens_ex. reflexivity.
Qed.

Theorem norm_seq_ens_all : forall A Q (f : A -> flow),
  entails (ens Q ;; fall (fun x => f x)) (fall (fun x => ens Q ;; f x)).
Proof.
  intros. apply norm_seq_all_r. shiftfree.
Qed.

Corollary norms_seq_ens_all : forall A P h v (f : A -> flow),
  entails (ens_state P h v ;; fall f) (fall (fun x => ens_state P h v  ;; f x)).
Proof.
  intros. rew_state_to_hprop. rewrite norm_seq_ens_all. reflexivity.
Qed.

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
  entails (ens_state P h v  ;; fall (fun x => f x) ;; fk) (fall (fun x => ens_state P h v  ;; f x ;; fk)).
Proof.
  intros. rew_state_to_hprop. rewrite norm_seq_ens_seq_all.
  reflexivity.
Qed.

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
  intros. unfold bind_t. rew_state_to_hprop. rewrite norm_bind_seq_ens.
  reflexivity.
Qed.

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
  intros. rew_state_to_hprop. apply norm_ens_heap_ens_pure.
Qed.

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

(* COQ-ONLY NORMALIZATION RULE *)
Theorem norms_seq_assoc_req : forall P H f1 f2,
  bientails (req_state P H f1 ;; f2) (req_state P H (f1 ;; f2)).
Proof.
Admitted.

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

