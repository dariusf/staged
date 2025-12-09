From IxFree Require Import Nat Lib.
From CtxEquivIxFree Require Import lang_shift_reset.
Import Inc.

(** top level Proper instances (using ctx_equiv/ctx_approx) *)

Instance Proper_ctx_equiv {V} :
  Proper
    (@ctx_equiv V ==> @ctx_equiv V ==> iff)
    (@ctx_equiv V).
Proof.
  unfold flip, Proper, respectful, iff.
  intros a b Hab c d Hcd.
  split.
  - intros Hac.
    transitivity a. symmetry. exact Hab.
    transitivity c. exact Hac. exact Hcd.
  - intros Hbd.
    transitivity b. exact Hab.
    transitivity d. exact Hbd.
    symmetry. exact Hcd.
Qed.

Instance Proper_ctx_approx {V} : Proper
  (@ctx_approx V --> @ctx_approx V ==> impl)
  (@ctx_approx V).
Proof.
  unfold flip, Proper, respectful, impl.
  intros a b Hba c d Hcd Hac.
  transitivity a. exact Hba.
  transitivity c. exact Hac. exact Hcd.
Qed.

Instance Proper_e_rel_o_app {V} :
  Proper (@e_rel_o V ==> @e_rel_o V ==> @e_rel_o V) e_app.
Proof.
  unfold Proper, e_rel_o, respectful.
  intros a b Hab c d Hcd n.
  by apply compat_app.
Qed.

Instance Proper_e_rel_o_lambda {V} :
  Proper (@e_rel_o (inc V) ==> @e_rel_o V) e_lambda.
Proof.
  unfold Proper, e_rel_o, respectful, e_lambda.
  intros a b Hab n.
  apply compat_val.
  by apply compat_lambda.
Qed.

Instance Proper_e_rel_o_shift {V} :
  Proper (@e_rel_o (inc V) ==> @e_rel_o V) e_shift.
Proof.
  unfold Proper, e_rel_o, respectful.
  intros a b Hab n.
  by apply compat_shift.
Qed.

Instance Proper_e_rel_o_reset {V} :
  Proper (@e_rel_o V ==> @e_rel_o V) e_reset.
Proof.
  unfold Proper, e_rel_o, respectful.
  intros a b Hab n.
  by apply compat_reset.
Qed.
