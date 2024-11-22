
From ShiftReset Require Import Logic.

Ltac funfold_hyp H env f :=
  rewrites (>> ent_unk env f) in H; [ unfold env; resolve_fn_in_env | ].

Ltac funfold_ env f :=
  rewrites (>> ent_unk env f); [ unfold env; resolve_fn_in_env | ].

Tactic Notation "funfold" constr(env) constr(f) := funfold_ env f.
Tactic Notation "funfold" constr(env) constr(f) "in" constr(H) := funfold_hyp H env f.

(* TODO maybe this should be the interface, for working with sequents especially *)
Ltac funfold1 f :=
  lazymatch goal with
  | |- entails_under (?env ?a ?b) _ _ =>
    rewrite (@ent_unk (env a b) f); [ | unfold env; resolve_fn_in_env ]
  | |- entails_under (?env ?a) _ _ =>
    rewrite (@ent_unk (env a) f); [ | unfold env; resolve_fn_in_env ]
  | |- entails_under ?env _ _ =>
    rewrite (@ent_unk env f); [ | unfold env; resolve_fn_in_env ]
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
    rewrite norm_seq_ex_reassoc_ctx; fintro x
  | |- entails_under _ (ens_ _;; ∃ _, _;; _) _ =>
    rewrite norm_seq_ex_reassoc_ctx; fintro x *)

  (* SL exists *)
  | |- entails_under _ (ens_ (\exists _, _)) _ =>
    rewrite ent_seq_ens_sl_ex; fintro x
  | |- entails_under _ (ens_ (\exists _, _);; _) _ =>
    rewrite ent_seq_ens_sl_ex; fintro x
  end.

(* instantiate an existential or specialize a forall *)
Ltac finst a :=
  lazymatch goal with
  (* | |- entails_under _ (ens_ _;; ∀ _, _) _ =>
    rewrite norm_seq_all_reassoc_ctx; finst a
  | |- entails_under _ (ens_ _;; ∀ _, _;; _) _ =>
    rewrite norm_seq_all_reassoc_ctx; finst a *)

  | |- entails_under _ ((∀ _, _);; _) _ =>
    apply ent_seq_all_l; exists a

  | |- entails_under _ (∀ _, _) _ =>
    apply ent_all_l; exists a
  | |- entails_under _ _ (∃ _, _) =>
    apply ent_ex_r; exists a
  end.

(** Move assumptions to the Coq context.
  This is the rough eqiuvalent of xpull from SLF.
  While we're comparing, xchange is replaced with rewriting and the use of lemmas around the covariance of [ens_]. *)
Ltac fassume_ H :=
  lazymatch goal with
  | |- entails_under _ (ens_ \[_]) _ =>
    apply ent_ens_l; intros H
  | |- entails_under _ (ens_ \[_];; _) _ =>
    apply ent_seq_ens_l; intros H
  | |- entails_under _ _ (req \[_] _) =>
    apply ent_req_r; apply ent_seq_ens_l; intros H
  end.

Ltac fassume_req :=
  lazymatch goal with
  | |- entails_under _ _ (req _ _) =>
    apply ent_req_r
  end.

Tactic Notation "fassume" simple_intropattern(p) := fassume_ p.
Tactic Notation "fassume" := fassume_req.
