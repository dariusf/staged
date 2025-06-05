
From ShiftReset Require Import Logic Entl.

Ltac funfold_hyp H env f :=
  rewrites (>> entails_under_unk env f) in H; [ unfold env; resolve_fn_in_env | ].

Ltac funfold_ env f :=
  rewrites (>> entails_under_unk env f); [ unfold env; resolve_fn_in_env | ].

Tactic Notation "funfold" constr(env) constr(f) := funfold_ env f.
Tactic Notation "funfold" constr(env) constr(f) "in" constr(H) := funfold_hyp H env f.

(* TODO maybe this should be the interface, for working with sequents especially *)
Ltac funfold1 f :=
  lazymatch goal with
  | |- entails_under (?env ?a ?b) _ _ =>
    rewrite (@entails_under_unk (env a b) f); [ | try unfold env; resolve_fn_in_env ]; simpl
  | |- entails_under (?env ?a) _ _ =>
    rewrite (@entails_under_unk (env a) f); [ | try unfold env; resolve_fn_in_env ]; simpl
  | |- entails_under ?env _ _ =>
    rewrite (@entails_under_unk env f); [ | try unfold env; resolve_fn_in_env ]; simpl

  | |- gentails_under (?env ?a ?b) _ _ _ =>
    rewrite (@entails_under_unk (env a b) f); [ | try unfold env; resolve_fn_in_env ]; simpl
  | |- gentails_under (?env ?a) _ _ _ =>
    rewrite (@entails_under_unk (env a) f); [ | try unfold env; resolve_fn_in_env ]; simpl
  | |- gentails_under ?env _ _ _ =>
    rewrite (@entails_under_unk env f); [ | try unfold env; resolve_fn_in_env ]; simpl
  end.

(* introduce variables *)
Ltac fintro x :=
  lazymatch goal with
  (* base cases *)
  | |- entails_under _ (∃ _, _) _ =>
    (* let x := fresh y in *)
    simple apply ent_ex_l; intros x
  | |- entails_under _ _ (∀ _, _) =>
    (* let x := fresh y in *)
    simple apply ent_all_r; intros x

  (* ex under an ens *)
  (* a problem with the automation is quantifiers going into the continuation *)
  (* | |- entails_under _ (ens_ _;; ∃ _, _) _ =>
    rewrite norm_seq_ex; fintro x
  | |- entails_under _ (ens_ _;; ∃ _, _;; _) _ =>
    rewrite norm_seq_ex; fintro x *)

  (* SL exists *)
  | |- entails_under _ (ens_ (\exists _, _)) _ =>
    rewrite norm_seq_ens_sl_ex; fintro x
  | |- entails_under _ (ens_ (\exists _, _);; _) _ =>
    rewrite norm_seq_ens_sl_ex; fintro x
  end.


(* instantiate an existential or specialize a forall *)
Ltac finst a :=
  lazymatch goal with
  | |- entails_under _ (rs (∀ _, _)) _ =>
    rewrite norm_rs_all; finst a
  | |- entails_under _ (req _ (∀ _, _)) _ =>
    rewrite norm_req_all; finst a
  | |- entails_under _ (_;; ∀ _, _) _ =>
    rewrite norm_seq_all_r; shiftfree; finst a
  (* | |- entails_under _ ((∃ _, _);; _) _ =>
    rewrite norm_seq_ex_l; fintro a
  | |- entails_under _ (_;; ∃ _, _) _ =>
    rewrite norm_seq_ex_r; fintro a *)

  | |- entails_under _ ((∀ _, _);; _) _ =>
    apply ent_seq_all_l; exists a

  | |- entails_under _ (∀ _, _) _ =>
    apply ent_all_l; exists a
  | |- entails_under _ _ (∃ _, _) =>
    apply ent_ex_r; exists a
  | |- entails_under _ _ ((∃ _, _);; _) =>
    apply ent_seq_ex_r; try exists a
  end.

(** Move assumptions to the Coq context.
  This is the rough eqiuvalent of xpull from SLF.
  While we're comparing, xchange is replaced with rewriting and the use of lemmas around the covariance of [ens_]. *)
(* Ltac fassume_ H :=
  lazymatch goal with
  | |- entails_under _ (ens_ \[_]) _ =>
    apply ent_ens_void_l; intros H
  | |- entails_under _ (ens_ \[_];; _) _ =>
    apply ent_seq_ens_void_pure_l; intros H
  | |- entails_under _ (ens (fun _ => \[_]);; _) _ =>
    apply ent_seq_ens_pure_l; intros H
  | |- entails_under _ _ (req \[_] _) =>
    apply ent_req_r; apply ent_seq_ens_void_pure_l; intros H
  end.

Ltac fassume_req :=
  lazymatch goal with
  | |- entails_under _ _ (req _ _) =>
    apply ent_req_r
  end.

Tactic Notation "fassume" simple_intropattern(p) := fassume_ p.
Tactic Notation "fassume" := fassume_req. *)

(* some technical lemmas for rearranging ens *)
Lemma norm_rearrange_ens : forall H P (P1:val->Prop),
  entails (ens (fun r => H \* \[P /\ P1 r]))
  (ens_ \[P];; ens_ H;; ens (fun r => \[P1 r])).
Proof.
  unfold entails. intros.
  inverts H0.
  heaps.
  applys s_seq.
  { applys s_ens. heaps. }
  applys s_seq.
  { applys s_ens. heaps. }
  { applys s_ens. heaps. }
Qed.

Lemma norm_ens_pure_conj1: forall P P1,
  entails (ens (fun r : val => \[P r /\ P1]))
    (seq (ens_ \[P1]) (ens (fun r : val => \[P r]))).
Proof.
  unfold entails. intros.
  inverts H.
  heaps.
  applys s_seq.
  applys s_ens. heaps.
  applys s_ens. heaps.
Qed.

(* automation-friendly specializations of a more general lemma
  to move only some constructs *)
Lemma norm_float_ens_void : forall H f2,
  entails (rs (ens_ H;; f2)) (ens_ H;; rs f2).
Proof.
  intros. applys* red_rs_float1.
Qed.

Lemma norm_reassoc_ens_void : forall H f2 fk,
  entails (bind (ens_ H;; f2) fk) (ens_ H;; bind f2 fk).
Proof.
  intros. applys* norm_bind_seq_assoc.
Qed.

Ltac fbiabduction :=
  rewrite norm_ens_req_transpose; [ | applys b_pts_single ];
  rewrite norm_req_pure_l; [ | reflexivity ];
  rewrite norm_seq_ens_empty.

Ltac freduction :=
  rewrite red_init;
  repeat rewrite red_extend;
  rewrite red_rs_sh_elim.



Create HintDb staged_norm_old.
Global Hint Rewrite

  (* move universal quantifiers on the left outwards *)
  norm_rs_all norm_req_all norm_seq_all_r

  (* associate things out of binds *)
  norm_bind_req norm_bind_seq_assoc norm_bind_disj

  (* move quantifiers out *)
  norm_bind_all_l norm_bind_ex_l
  norm_seq_ex_r
  norm_rs_seq_ex_r
  norm_ens_pure_ex
  (* norm_bind_all_r norm_bind_ex_r *)
  norm_rs_all norm_seq_all_r
  norm_rs_ex

  (* normalise pure assumptions *)
  norm_ens_pure_conj
  norm_ens_void_hstar_pure_l
  norm_ens_void_hstar_pure_r

  (* associate things out of resets *)
  norm_rs_req norm_rs_disj red_rs_float1

  (* eliminate trivial resets and binds *)
  norm_rs_ens norm_bind_val

  (* trivial rewrites *)
  norm_seq_empty_l

using shiftfree : staged_norm_old.
Ltac fsimpl_old := autorewrite with staged_norm_old.

(** Automation

  The set of tactics shows the general strategy/decomposiiton of proof steps.

  - [fsimpl]: simplify. This is in charge of implicitly establishing a normal form for the left side of a sequent, which is [(defun f u;)* (ens_ H;)? f]. Simplification generally involves: applying easy simplifying rewrites, moving assumptions as far back as possible (to facilitate lifting into metalogic), moving an ens to the beginning to serve as the "spatial context"/"symbolic execution state", moving shift-free things out of resets, moving defun to the beginning. Will not move quantiifers, leaving open the possibility of handling them via heuristics based on position.
  - [funfold2]: unfold anonymous functions or discard a defun
  - [fspecialize], [fdestruct], [fexists], [fintros]: these are unfortunately-named, but deal with quantifiers on both sides of entailments
  - [freduction], [fbiabduction]: for specific scenarios, where there is a shift inside a reset, or an ens followed by req
  - [fentailment]: bridges to metalogic
  - [fleft], [fright]: for disjunction

*)

Create HintDb staged_forall_r.
Global Hint Rewrite
  red_init
using shiftfree : staged_forall_r.
Ltac fintros_rew := autorewrite with staged_forall_r.
Ltac fintros x :=
  fintros_rew;
  first [
    simple apply ent_all_r |
    simple apply entl_all_r
  ]; intros x.

Create HintDb staged_exists_r.
Global Hint Rewrite
  red_init
using shiftfree : staged_exists_r.
Ltac fexists_rew := autorewrite with staged_exists_r.
Ltac fexists a := fexists_rew;
  first [
    simple apply entl_ex_r |
    simple apply entl_seq_ex_r
  ]; exists a.

Ltac fexists_old a := fexists_rew;
  first [
    simple apply ent_ex_r |
    simple apply ent_seq_ex_r
  ]; exists a.

Create HintDb staged_exists_l.
Global Hint Rewrite
  norm_bind_ex_l
  norm_seq_ex_r
  norm_rs_seq_ex_r
  norm_ens_pure_ex
  norm_rs_ex
  norm_seq_ens_sl_ex
  norm_seq_ens_sl_ex
  norm_seq_ex_l
  norm_seq_defun_ex
using shiftfree : staged_exists_l.
Ltac fdestruct_rew := autorewrite with staged_exists_l.
Ltac fdestruct a := fdestruct_rew;
  first [
    simple apply entl_ex_l |
    simple apply entl_seq_ex_l
  ]; intros a.

Ltac fdestruct_old a := fdestruct_rew;
  first [
    simple apply ent_ex_l |
    simple apply ent_seq_ex_l
  ]; intros a.

Create HintDb staged_forall_l.
Global Hint Rewrite
  norm_bind_all_l
  norm_rs_all
  norm_seq_all_r
  norm_rs_all
  norm_req_all
  norm_seq_all_r
  norm_seq_defun_all
using shiftfree : staged_forall_l.
Ltac fspecialize_rew := autorewrite with staged_forall_l.
Ltac fspecialize x := fspecialize_rew;
  first [
    simple apply entl_all_l |
    simple apply ent_all_l |
    simple apply ent_seq_all_l
  ]; exists x.

Lemma norm_bind_defun_out: forall (f:var) u fk f2,
  entails (bind (defun f u;; f2) fk) (defun f u;; bind f2 fk).
Proof.
  intros. applys* norm_bind_seq_assoc.
Qed.

Lemma norm_seq_defun_ens_void_out: forall (f:var) u f2 H,
  entails (ens_ H;; defun f u;; f2) (defun f u;; ens_ H;; f2).
Proof.
  unfold entails. intros.
  inverts* H0.
  inverts H8.
  inverts* H9.
  inverts* H8.
  applys* s_seq.
  applys* s_defun.
  applys* s_seq.
  applys* s_ens.
Qed.


Create HintDb staged_defun_out.
Global Hint Rewrite
  norm_bind_defun_out
  norm_rs_seq_defun_out
  norm_seq_defun_ens_void_out
using shiftfree : staged_defun_out.
Ltac move_defun_out := autorewrite with staged_defun_out.



Create HintDb staged_defun_in.
Global Hint Rewrite
  (* push defun towards a discard *)
  norm_seq_defun_rs
  norm_seq_defun_bind_l
  norm_seq_defun_ens_void
  norm_seq_defun_req
  norm_seq_defun_skip_ens_void
  (* don't move quantifiers *)
  (* norm_seq_defun_all *)
  (* norm_seq_defun_ex *)

  (* move out of bind/rs *)
  norm_bind_seq_defun_ens
  norm_bind_rs_seq_defun_ens

using shiftfree : staged_defun_in.
Ltac funfold2 :=
  autorewrite with staged_defun_in;
  first [
    (* unfold defun when possible *)
    rewrite norm_seq_defun_unk; move_defun_out |
    (* cancel defun and discard *)
    first [
      rewrite norm_seq_defun_discard | (* TODO get rid of these *)
      rewrite norm_defun_discard_id |
      rewrite norm_seq_defun_discard1 |
      rewrite norm_defun_discard_id1
    ]; jauto
  ].

(** keep in sync with [staged_defun_in] *)
Ltac move_one_defun_in f :=
  repeat first [
    rewrite (@norm_seq_defun_rs f) |
    rewrite (@norm_seq_defun_bind_l f) |
    rewrite (@norm_seq_defun_ens_void f) |
    rewrite (@norm_seq_defun_req f) |
    rewrite (@norm_seq_defun_skip_ens_void f) |
    rewrite (@norm_bind_seq_defun_ens f) |
    rewrite (@norm_bind_rs_seq_defun_ens f)
  ].


Ltac funfold3 f :=
  move_one_defun_in f;
  first [
    (* unfold defun when possible *)
    rewrite norm_seq_defun_unk; move_defun_out |
    (* cancel defun and discard *)
    first [
      rewrite norm_seq_defun_discard1 |
      rewrite norm_defun_discard_id1
    ]; jauto
  ].


(* obligations involving shifting around separation logic and req/ens.
  the general strategy is to join ens, then split them into:

  - pure (to be lifted to metalogic)
  - stateful
  - results
*)
Create HintDb staged_sl_ens.
Global Hint Rewrite
  norm_ens_pure_conj1
  norm_ens_pure_conj
  norm_rearrange_ens
  (* norm_ens_ens_void_l *)
  norm_ens_void_hstar_pure_l
  norm_ens_void_hstar_pure_r
using shiftfree : staged_sl_ens.


(* simplification/normalization, optimized for interactive use.
  for example, this splits ens so we can move the pure parts out. *)
Create HintDb staged_norm.
Global Hint Rewrite

  (* associate things out of binds *)
  norm_reassoc_ens_void
  norm_bind_req
  norm_bind_disj

  (* associate things out of resets *)
  norm_rs_req
  norm_rs_disj
  norm_float_ens_void

  (* trivial simplifications *)
  norm_rs_ens
  norm_bind_val
  norm_seq_empty_l

using shiftfree : staged_norm.
Ltac fsimpl := autorewrite with staged_norm staged_sl_ens.



(* simplifications performed prior to using entailment rules.
  this optimises for closing out goals, so will e.g. join ens. *)
(* Create HintDb staged_ens_join.
Global Hint Rewrite
  norm_ens_ens_void_l
using shiftfree : staged_ens_join. *)

(* apply an entailment rule, which bridges to the metalogic *)
Ltac fentailment :=
  first [
    apply entl_seq_ens_pure_l |
    apply entl_seq_defun_ens_pure_l |

    apply entl_seq_ens_void_pure_l |
    apply entl_seq_defun_ens_void_pure_l |

    apply entl_ens_single |

    apply entl_req_req |
    apply entl_defun_req_req |
    (* apply entl_defun2_req_req | *)

    apply entl_req_l |
    apply entl_defun_req_l |

    (* this is ordered last *)
    apply entl_req_r
  ].


Ltac fentailment_old :=
  first [
    apply ent_seq_ens_pure_l |
    apply ent_seq_defun_ens_pure_l |

    apply ent_seq_ens_void_pure_l |
    apply ent_seq_defun_ens_void_pure_l |

    apply ent_ens_single |

    apply ent_req_req |
    apply ent_defun_req_req |
    (* apply ent_defun2_req_req | *)

    apply ent_req_l |
    apply ent_defun_req_l |

    (* this is ordered last *)
    apply ent_req_r
  ].

Ltac fleft := first [ apply entl_seq_disj_r_l | apply entl_disj_r_l ].
Ltac fright := first [ apply entl_seq_disj_r_r | apply entl_disj_r_r ].

Ltac fleft_old := first [ apply ent_seq_disj_r_l | apply ent_disj_r_l ].
Ltac fright_old := first [ apply ent_seq_disj_r_r | apply ent_disj_r_r ].