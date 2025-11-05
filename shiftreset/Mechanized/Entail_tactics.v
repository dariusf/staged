
From ShiftReset Require Import Logic Automation Entl Norm Propriety.
From ShiftReset.Mechanized Require Import State Normalization.

(** TACTICS **)

(* the "base case" of Heifer entailment *)
Lemma ent_ens_empty : entails (ens_pure True) (ens_pure True).
Proof.
  apply entl_ens_single.
  xsimpl; auto.
Qed.
(* there is also a base case for req \[True], but
   here there is no way to represent a trailing [req] *)

Ltac fempty :=
  match goal with
  | [ |- entails (req_state True hemp empty) (req_state True hemp empty) ] => reflexivity
  | [ |- entails (ens_state True hemp vunit) (ens_state True hemp vunit) ] => reflexivity
  end.

Ltac fsolve_pure := auto.

Ltac fsolve_heap := xsimpl.

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
  intros * Hbiab.
  induction Hbiab; xsimpl; intuition.
Qed.

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
(* this version is probably provable; the version with a non-empty antiframe
  is probably unsound as it implies [req_lhs_becomes_ens] *)
Lemma req_implies_ens_ens :
  forall H1 H2 Hf f1 f2,
  H1 ==> H2 \* Hf ->
  (entails f1 (req Hf f2) -> entails (ens_ H1 ;; f1) (ens_ H2 ;; f2)).
Proof.
  intros * Hbiab.
  intros Hreq.
  rewrite Hreq.
  rewrite Hbiab.
  rewrite hstar_comm.
  rewrite entl_ens_req_cancel.
  reflexivity.
Qed.

(* TODO is the converse true? *)

Lemma entl_state_ens_ens_f : forall P1 h1 v1 P2 h2 v2 f1 f2,
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

Lemma entl_state_req_req_f : forall P1 h1 P2 h2 f1 f2,
  (\[P2] \* hprop_of_hpred h2) ==> (\[P1] \* hprop_of_hpred h1) ->
  entails f1 f2 ->
  entails (req_state P1 h1 f1) (req_state P2 h2 f2).
Proof.
  intros * Hhimpl Hent.
  rew_state_to_hprop.
  rewrite Hent.
  rewrite Hhimpl.
  reflexivity.
Qed.

Lemma entl_state_ens_ens : forall P1 P2 hp1 hp2 v1 v2,
  (* Heifer's rule here is a full biabduction, but I'm pretty sure it's incorrect... *)
  (\[P1] \* hprop_of_hpred hp1)  ==> \[P2] \* (hprop_of_hpred hp2)
  -> v1 = v2
  (* Technically, this subgoal is not needed, but this is what Heifer reduces the ens-ens entailment to... *)
  -> entails (req_state True hemp empty) (req_state True hemp empty)
  -> entails (ens_state P1 hp1 v1) (ens_state P2 hp2 v2).
Proof.
  intros * Hhimpl Hsubst Hreq.
  subst.
  rew_state_to_hprop.
  rewrite <- norm_ens_ens_void_l.
  with_entailsR (rewrite <- norm_ens_ens_void_l).
  apply entl_ens_ens.
  - exact Hhimpl.
  - reflexivity. 
Qed.

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
  match goal with
  |  [ |- entails (ens_state _ _ _) (ens_state _ _ _) ] =>
    apply entl_state_ens_ens; [unfold hprop_of_hpred; fsolve_heap; try fsolve_pure | fsolve_pure | ]
  end.


Ltac fmatch_ens :=
  (* operates on goals of the form
     entails (ens ?lhs ;; ?lnext) (ens ?rhs ;; ?rnext)

     - uses biabduction to eliminate matching locations in lhs/rhs
     - checks resulting pure condition
     - turns goal into
     entails (req (antiframe) lnext) (req (frame) rnext)
   *)
  match goal with
  | [ |- entails ((ens_state _ _ _) ;; _) ((ens_state _ _ _) ;; _)] =>
    apply entl_state_ens_ens_f; [unfold hprop_of_hpred; fsolve_heap; try fsolve_pure | fsolve_pure | ]
  | [ |- entails (req_state _ _ _) (req_state _ _ _) ] =>
    apply entl_state_req_req_f; [unfold hprop_of_hpred; fsolve_heap; try fsolve_pure | ]
  end.

(* TODO: use Ltac2? *)

(* split all ensures clauses up to 
  - one representing the result value
   - one representing pure constraints
   - one representing heap constraints *)

Check norm_rearrange_ens. 

(* Splitting a single ens_state into ens_pure ens_heap and ret *)
Lemma norms_split_ens : forall P h v, bientails (ens_state P h v) (ens_state P hemp vunit ;; ens_state True h vunit ;; ens_state True hemp v).
Proof. Admitted.

Corollary norms_split_ens_locked : 
  forall P h v, bientails (ens_state P h v)
  ((locked _ ens_state) P hemp vunit ;;
   (locked _ ens_state) True h vunit ;;
   (locked _ ens_state) True hemp v).
Proof.
  rewrite <- (lock _ _).
  apply norms_split_ens.
Qed.

Lemma norms_remove_empty_void : forall f, bientails (ens_state True hemp vunit ;; f) f.
Proof. Admitted.

Lemma norms_remove_empty_ret : forall P h, bientails (ens_state P h vunit ;; ens_state True hemp vunit) (ens_state P h vunit).
Proof. Admitted.

Ltac fsplit_ens :=
  repeat (setoid_rewrite norms_split_ens_locked at 1);
  rewrite <- (lock _ _);
  repeat (setoid_rewrite norms_remove_empty_void at 1);
  repeat (setoid_rewrite norms_remove_empty_ret at 1).

Ltac fapply_one_norm_rule :=
  first [
    setoid_rewrite norms_bind_t_trivial at 1; [ | rew_state_to_hprop; shiftfree ] |
    setoid_rewrite norm_bind_t_ex_l at 1 |
    setoid_rewrite norm_bind_t_all_l at 1 |
    setoid_rewrite norms_bind_seq_ens at 1 |
    setoid_rewrite norms_bind_t_val at 1 |
    setoid_rewrite norm_bind_t_req at 1 |
    setoid_rewrite norms_bind_t_assoc_ens at 1 |
    setoid_rewrite norms_bind_seq_ens at 1 |
    setoid_rewrite norms_seq_ens_all at 1 |
    setoid_rewrite norms_bind_t_val at 1 |
    setoid_rewrite norms_bind_t_val2 at 1 |
    setoid_rewrite norms_seq_ens_all at 1 |
    setoid_rewrite norms_seq_ens_seq_all at 1 |
    setoid_rewrite norm_seq_all at 1 |
    setoid_rewrite norms_ens_heap_ens_heap at 1 |
    setoid_rewrite norms_seq_ens_heap_ens_heap at 1 |
    setoid_rewrite norms_ens_pure_ens_pure at 1 |
    setoid_rewrite norms_seq_ens_pure_ens_pure at 1 |
    setoid_rewrite norms_seq_ens_ex at 1 |
    setoid_rewrite <- norm_seq_assoc_sf at 1; [ | rew_state_to_hprop; shiftfree ] |
    setoid_rewrite norms_seq_assoc_req
  ].

(* before normalizing, heifer first splits all ens into pure and
   heap components. *)
Ltac fnormalize :=
  fsplit_ens;
  repeat fapply_one_norm_rule.

Ltac freduce_shrs :=
  idtac "shift/reset TODO".

Ltac fsimpl :=
  repeat (fsimpl_heap; freduce_shrs; fnormalize).

Ltac fbiab_state := 
  rew_state_to_hprop;
  (* fbiabduction, but only on the first ens-req pair *)
  rewrite norm_ens_req_transpose at 1; [ | applys b_pts_single ];
  rewrite norm_req_pure_l; [ | reflexivity ];
  rewrite norm_seq_ens_empty;
  rew_hprop_to_state.

Ltac finst_lhs_all c :=
  apply entl_all_l; exists c.

Ltac finst_and_biab c :=
  finst_lhs_all c; fbiab_state.

(*** NO GUARANTEE EVERYTHING FROM THIS POINT COMPILES *)

(* IDEA: ens_t, similar to [bind_t] that allows for the [res] to be any type
  we can convert to val *)

