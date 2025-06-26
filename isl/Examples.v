
(* From ISL Require Import Logic Automation Entl. *)
(* From ISL Require ExamplesEnt. *)
From ISL Require Import Basics Norm.
Local Open Scope string_scope.

(*
Lemma entl_elim_bind: forall P fk f1 (f:var) u H,
  (forall r, P r -> entails (defun f u;; ens_ H;; rs (fk r)) f1) ->
    entails (defun f u;; ens_ H;; rs (bind (ens (fun r => \[P r])) fk)) f1.
Proof. *)