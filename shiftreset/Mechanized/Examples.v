
From ShiftReset Require Import Logic Entl Automation Norm Propriety.
From ShiftReset Require ExamplesEnt.

From ShiftReset.Mechanized Require Import State Normalization Entail_tactics.

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
Instance Proper_entails_req_state :
  Proper (eq ====> eq ====> entails ====> entails) req_state.
Proof.
Admitted.

#[global]
Instance Proper_bientails_req_state :
  Proper (eq ====> eq ====> entails ====> entails) req_state.
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

Ltac rew_state_to_hprop := 
  unfold ens_pure, ens_heap, ens_ret;
  rewrite ?ens_state_vunit_is_ens_state_void;
  rewrite ?ens_state_void_is_ens_void;
  unfold ens_state, req_state, hprop_of_hpred;
  (* clean up the postconditions *)
  rewrite ?ens_vunit_is_ens_void;
  rewrite <- ?hempty_eq_hpure_true;
  autorewrite with rew_heap;
  (*rewrite <- hempty_eq_hpure_true;*)
  (*repeat (rewrite hstar_hempty_r, hstar_hempty_l);*)
  fold hprop_of_hpred.

Example test5 : entails
  (*(∃' v72, bind (ens (fun res => \[res = vloc v72] \* v72 ~~> 0))*)
  (*(fun ival =>*)
  (*∃' i, ens_ \[ival = vloc i] ;; ∀' v73, req (i ~~> v73) (ens (fun res => \[res = v73] \* i ~~> v73))))*)
  (*(∃' i, ens (fun res => \[res = vloc i] \* i ~~> 0)).*)
  (bind_t (∃' v72, ens (fun res => \[res = into v72] \* v72 ~~> 0))
  (fun i =>
  bind_t (∀' v73, req (i ~~> v73) (ens (fun res => \[res = into v73] \* i ~~> v73)))
    (fun v70 => ens (fun res => \[res = vplus v70 (vint 1)]))))
  (∃' i, (ens (fun res => \[res = 1] \* i ~~> 0))).
Proof.
  rew_hprop_to_state.
  fsimpl.
  fdestruct v72.
  feinst_and_biab.
  rew_hprop_to_state.
  fexists v72.
  fmatch_ens.
  fsingle_ens.
Qed.

(*
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
*)
