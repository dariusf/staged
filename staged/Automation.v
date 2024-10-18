
From Staged Require Import Logic.

Ltac funfold_hyp H env f :=
  rewrites (>> norm_unk env f) in H; [ unfold env; resolve_fn_in_env | ].

Ltac funfold_ env f :=
  rewrites (>> norm_unk env f); [ unfold env; resolve_fn_in_env | ].

Global Hint Rewrite norm_seq_ens_empty norm_exists norm_forall norm_reassoc : norm_db.

Ltac norm :=
  autorewrite with norm_db.

Tactic Notation "funfold" constr(env) constr(f) := funfold_ env f.
Tactic Notation "funfold" constr(env) constr(f) "in" constr(H) := funfold_hyp H env f.

Ltac ent_step :=
  match goal with

  (* assume things on the left side *)
  | |- entails_under _ (disj _ _) _ =>
    simple apply ent_disj_l
  | |- entails_under _ (fex (fun y => _)) _ =>
    let x := fresh y in
    simple apply ent_ex_l; intros x
  | |- entails_under _ (fex (fun _ => _);; _) _ =>
    rewrite ent_seq_ex_reassoc
  | |- entails_under _ (ens_ \[_];; _) _ =>
    let H := fresh "H" in
    simple apply ent_seq_ens_l; intros H; destr H

  (* if there is an IH, try to use it *)
  | IH: context[entails_under ?env (unk _ _ _) _] |-
    context[unk ?f _ _] =>

    (* if it fails, try to resolve it from the environment *)
    first [
      (* TODO unfortunately this immediately tries the IH. we need to delay it until we've unfolded at least once *)
        rewrite IH; [ | subst; auto ]
      (* | rewrite (@norm_unk env); [ | unfold env; resolve_fn_in_env ]; simpl *)
      (* | funfold env f *)
    ]

  (* if there is no IH, try to resolve from the environment *)
  | |- entails_under ?env (unk ?f _ _) _ =>
    (* rewrite (@norm_unk env); [ | unfold env; resolve_fn_in_env ]; simpl *)
    funfold env f; simpl

  (* try to work on the right side *)
  | |- entails_under _ _ (fex (fun _ => _)) =>
    simple apply ent_ex_r; eexists
  | |- entails_under _ (ens_ \[_]) (ens_ \[_]) =>
    simple apply ent_ens_single_pure; subst; intuition
  | |- entails_under _ (ens_ _) (ens_ _) =>
    simple apply ent_ens_single; xsimpl; subst; intuition

  (* if all else fails, try basic tactics to hopefully get other steps to apply *)
  | H: _ /\ _ |- _ =>
    destruct H
  | _: ?v = ?w |- _ =>
    first [subst v | subst w]

  (* after we've tried everything, try to solve *)
  | |- _ = _ =>
    solve [simpl; simple apply eq_refl]
    (* https://coq.inria.fr/doc/master/refman/proofs/writing-proofs/proof-mode.html#coq:flag.Solve-Unification-Constraints *)
    (* solve [solve_constraints; reflexivity] *)

  (* always have a no-match so we can repeat this *)
  | |- ?g => idtac "no match"; idtac g; fail
  end.

  Ltac solve_entailment :=
    repeat ent_step.