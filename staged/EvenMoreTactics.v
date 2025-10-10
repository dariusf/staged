
From Staged Require Export ExtraTactics.
From SLF Require Import LibTactics.

(* For when the goal can be dispatched by brute force.
  jauto handles these but will not leave unsolved goals. *)
Ltac zap :=
  lazymatch goal with
  | H: exists _, _ |- _ => destr H; zap
  | H: _ /\ _ |- _ => destr H; zap
  | H: _ <-> _ |- _ => destruct H; zap
  | |- _ /\ _ => splits; zap
  | |- exists _, _ => eexists; zap
  | _ => jauto
  end.
