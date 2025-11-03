
From ShiftReset Require Import Logic Entl Automation Norm Propriety.
From ShiftReset Require ExamplesEnt.

From ShiftReset.Mechanized Require Import State Normalization Entail_tactics.

(* Try not to use evars for return values, some of the rewrite rules look for vunit return values
   and this may trigger undesired unification. *)

#[global]
Instance RewritableBinder_anything : forall f, RewritableBinder f.
Proof.
Admitted.

Definition vplus (a b:val) : val :=
  match a, b with
  | vint a, vint b => vint (a + b)
  | _, _ => vunit
  end.

(* this can be instantly discharged *)
Example test10 : entails
  (ens (fun r => \[r = 0]))
  (ens (fun r => \[r = 0])).
Proof.
  rew_hprop_to_state.
  fsingle_ens.
Qed.


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

Example test5 : entails
  (bind_t (∃' v72, ens (fun res => \[res = into v72] \* v72 ~~> 0))
  (fun i =>
  bind_t (∀' v73, req (i ~~> v73) (ens (fun res => \[res = into v73] \* i ~~> v73)))
    (fun v70 => ens (fun res => \[res = vplus v70 (vint 1)]))))
  (∃' i, (ens (fun res => \[res = 1] \* i ~~> 0))).
Proof.
  rew_hprop_to_state.
  fsimpl.
  fdestruct v72.
  finst_and_biab 0.
  fexists v72.
  fmatch_ens.
  fsingle_ens.
Qed.

(* writing to the heap *)
Example test61 : entails
  (bind_t (∃' v88, ens (fun res => \[res = into v88] \* v88 ~~> 0)) (fun i =>
  (bind_t (
    (bind_t (∀' v89, req (i ~~> v89) (ens (fun res => \[res = v89] \* i ~~> v89))) (fun v85 =>
    ens (fun res => \[res = vplus v85 1])))
  ) (fun v86 =>
  (∀' v90, req (i ~~> v90) (ens_ (i ~~> v86))) ;;
  ∀' v91, req (i ~~> v91) (ens (fun res => \[res = v91] \* i ~~> v91))
  ))))
  (∃' i, ens (fun res => \[res = 1] \* i ~~> 1)).
Proof.
  rew_hprop_to_state.
  fsimpl.
  fdestruct v88.
  finst_and_biab 0.
  finst_and_biab 0.
  finst_and_biab (vplus 0 1).
  fexists v88.
  fmatch_ens.
  fsingle_ens.
Qed.

