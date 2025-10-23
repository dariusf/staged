
From ShiftReset Require Import Logic Automation Entl Norm Propriety.
From ShiftReset Require ExamplesEnt.
From ShiftReset.Mechanized Require Import State Normalization Entail_tactics.
Local Open Scope string_scope.

Definition vplus (a b:val) : val :=
  match a, b with
  | vint a, vint b => vint (a + b)
  | _, _ => vunit
  end.


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
(*
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
 *)
