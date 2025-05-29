
(* From ShiftReset Require Import Logic Automation. *)
From ShiftReset Require Import Logic Automation.
Local Open Scope string_scope.

Lemma norm_seq_defun_skip_ens_void: forall (f:var) u H f1,
  entails (defun f u;; ens_ H;; f1) (ens_ H;; defun f u;; f1).
Proof.
  unfold entails. intros.
  inverts* H0.
  inverts H8.
  inverts* H9.
  inverts H7.
  heaps.
  applys* s_seq. applys* s_ens. heaps.
  applys* s_seq. applys* s_defun.
Qed.

Lemma norm_seq_defun_all: forall (f:var) u (A:Type) (P:A->flow),
  entails (defun f u;; ∀ x, P x) (∀ x, defun f u;; P x).
Proof.
  unfold entails. intros.
  inverts* H.
  inverts H7.
  inverts H8 as H8.
  applys s_fall. intros b.
  specializes H8 b.
  applys* s_seq. applys* s_defun.
Qed.

Lemma norm_rs_ens: forall Q,
  bientails (rs (ens Q)) (ens Q).
Proof.
  applys red_rs_ens.
Qed.

Lemma norm_seq_defun_ex: forall (f:var) u (A:Type) (P:A->flow),
  entails (defun f u;; ∃ x, P x) (∃ x, defun f u;; P x).
Proof.
  unfold entails. intros.
  inverts* H.
  inverts H7.
  inverts H8 as H8.
  applys s_fex. destruct H8 as (b&H8).
  exists b.
  applys* s_seq. applys* s_defun.
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

Coercion vint : Z >-> val.
Coercion vbool : bool >-> val.

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

(* Automation

  The set of tactics shows the general strategy/decomposiiton of proof steps.

  - fsimpl: simplify, but do not move quantifiers. Simplification generally involves: applying easy simplifying rewrites, moving assumptions as far back as possible (to facilitate lifting into metalogic), moving an ens to the beginning to serve as the "spatial context"/"symbolic execution state", moving shift-free things out of resets, moving defun forward to unfold functions and cancel it with discard
  - fspecialize, fdestruct, fexists, fintros: these are unfortunately-named, but deal with quantifiers on both sides of entailments
  - freduction, fbiabduction: for specific scenarios, where there is a shift inside a reset, or an ens followed by req
  - fentailment: bridges to metalogic
  - fleft, fright: for disjunction

*)

Create HintDb staged_forall_r.
Global Hint Rewrite
  red_init
using shiftfree : staged_forall_r.
Ltac fintros_rew := autorewrite with staged_forall_r.
Ltac fintros x := fintros_rew; simple apply ent_all_r; intros x.

Create HintDb staged_exists_r.
Global Hint Rewrite
  red_init
using shiftfree : staged_exists_r.
Ltac fexists_rew := autorewrite with staged_exists_r.
Ltac fexists a := fexists_rew;
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
Ltac fdestruct := fdestruct_rew;
  first [
    simple apply ent_ex_l
  ]; intros.

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
    simple apply ent_all_l |
    simple apply ent_seq_all_l
  ]; exists x.

Create HintDb staged_norm.
Global Hint Rewrite

  (* associate things out of binds *)
  (* norm_bind_seq_assoc *)
  norm_reassoc_ens_void
  norm_bind_req
  norm_bind_disj

  (* normalise pure assumptions *)
  norm_ens_pure_conj
  norm_ens_void_hstar_pure_l
  norm_ens_void_hstar_pure_r

  (* associate things out of resets *)
  norm_rs_req
  norm_rs_disj
  norm_float_ens_void

  (* trivial simplifications *)
  norm_rs_ens
  norm_bind_val
  norm_seq_empty_l

  (* DEFUN *)

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

  (* unfold defun when possible *)
  norm_seq_defun_unk

  (* cancel defun and discard *)
  norm_seq_defun_discard
  norm_defun_discard_id

  using shiftfree : staged_norm.
Ltac fsimpl := autorewrite with staged_norm.

(* Create HintDb staged_norm_defun.
Global Hint Rewrite
  using shiftfree : staged_norm_defun.
Ltac fdefun := autorewrite with staged_norm_defun. *)

(* this is split into two tactics because we want to
  pull things out of resets in general, but move defuns
  in, towards discards. so we pull everything out, then
  move defuns in, so that's the state the user sees.
  as defuns swap over things, this makes progress. *)
(* Ltac fsimpl :=
  fsimpl_rew. *)
  (* repeat (fsimpl_rew; fdefun). *)

(* apply an entailment rule, which bridges to the metalogic *)
Ltac fentailment := first [
  apply ent_seq_ens_pure_l |
  apply ent_seq_ens_void_pure_l |
  apply ent_ens_single |
  apply ent_req_req |
  apply ent_req_l
].

Ltac fleft := first [ apply ent_seq_disj_r_l | apply ent_disj_r_l ].
Ltac fright := first [ apply ent_seq_disj_r_r | apply ent_disj_r_l ].

Module Multi.

(* < sh k. let a = k true in let b = k false in a && b > *)
Definition f : ufun := fun _ =>
  rs (
    sh "k" (
      bind (unk "k" true) (fun r1 =>
      bind (unk "k" false) (fun r2 =>
        ens (fun r => \[r = vand r1 r2])
      )))).

Definition flip_env :=
  Fmap.single "k" (fun v : val => rs (ens (fun r => \[r = v]))).

Theorem flip_reduction: forall n v1,
  gentails_under flip_env n (f v1) (ens (fun r => \[r = false])).
Proof.
  intros. unfold f.
  rewrite red_init.
  rewrite red_rs_sh_elim.

  (* rewrite entails_under_seq_defun_idem.
  2: { unfold flip_env. apply Fmap.indom_single. }
  2: { unfold flip_env. resolve_fn_in_env. } *)

  applys gent_seq_defun_idem.
  { unfold flip_env. apply Fmap.indom_single. }
  { unfold flip_env. resolve_fn_in_env. }

  funfold1 "k".
  fsimpl.
  funfold1 "k".
  lazymatch goal with
  | |- gentails_under ?e _ _ _ => remember e as env
  end.
  fsimpl.
  reflexivity.
Qed.

Definition flip1 : ufun := fun _ =>
  rs (
    sh "k" (
      bind (unk "k" true) (fun r1 =>
      bind (unk "k" false) (fun r2 =>
        discard "k";; ens (fun r => \[r = vand r1 r2])
      )))).

Theorem flip_reduction1: forall v1,
  entails_under empty_env (flip1 v1) (ens (fun r => \[r = false])).
Proof.
  intros. unfold flip1.
  freduction.
  fsimpl.
  reflexivity.
Qed.

(* this shows how [flip_reduction1] works *)
Theorem flip_reduction2: forall v1,
  entails_under empty_env (flip1 v1) (ens (fun r => \[r = false])).
Proof.
  intros. unfold flip1.
  freduction.
  rewrite norm_seq_defun_rs.
  rewrite norm_seq_defun_bind_l.
  rewrite norm_seq_defun_unk.
  rewrite norm_seq_defun_rs.
  rewrite norm_bind_rs_seq_defun_ens.
  rewrite norm_rs_ens.
  rewrite norm_bind_val.

  rewrite norm_seq_defun_bind_l.
  rewrite norm_seq_defun_unk.
  rewrite norm_seq_defun_rs.
  rewrite norm_bind_rs_seq_defun_ens.
  rewrite norm_rs_ens.
  rewrite norm_bind_val.

  rewrite norm_seq_defun_discard.
  - rewrite norm_rs_ens.
    reflexivity.
  - unfold empty_env. solve_not_indom.
Qed.

End Multi.

Module Toss.

(* let toss () =
  shift k.
    x := !x+1;
    let r1 = k true in
    x := !x+1;
    let r2 = k false in
    r1 + r2
*)
Definition toss : ufun := fun _ =>
  sh "k" (∀ x a,
    bind (req (x~~>vint a) (ens_ (x~~>(a+1));; unk "k" true)) (fun r1 =>
      ∀ b, bind (req (x~~>vint b) (ens_ (x~~>(b+1));; unk "k" false)) (fun r2 =>
        ens (fun r3 => \[r3 = vadd r1 r2])))).

Definition toss_env :=
  Fmap.update
    (Fmap.single "toss" toss)
    "k" (fun v : val => rs (bind (ens (fun r => \[r = v]))
    (fun v => ens (fun r1 => \[If v = true then r1 = 1 else r1 = 0])))).

(* let flipi () = < let v = toss () in if v then 1 else 0 > *)
Definition flipi : flow :=
  rs (
    bind (unk "toss" vunit) (fun v =>
    ens (fun r1 => \[If v = true then r1 = 1 else r1 = 0]))
  ).

Definition flipi_spec : flow :=
  ∀ x a, req (x~~>vint a) (ens (fun r => x~~>(a+2) \* \[r=1])).

Theorem flipi_summary :
  entails_under toss_env flipi flipi_spec.
Proof.
  intros.
  unfold flipi, flipi_spec.

  funfold1 "toss". unfold toss.
  rewrite red_init.
  rewrite red_extend.
  rewrite red_rs_sh_elim.

  apply ent_seq_defun_idem.
  { unfold toss_env. apply Fmap.indom_union_l. apply Fmap.indom_single. }
  { unfold toss_env. resolve_fn_in_env. }

  fintro x. finst x.
  fintro a. finst a.
  funfold1 "k".

  fsimpl.
  apply ent_req_req. xsimpl.

  (* fix printing due to overly-long env *)
  lazymatch goal with
  | |- entails_under ?e _ _ => remember e as env
  end.

  case_if.
  fsimpl_old.
  finst (a + 1).

  (* somehow automate this... *)
  subst.
  funfold1 "k".
  lazymatch goal with
  | |- entails_under ?e _ _ => remember e as env
  end.

  fsimpl_old.
  case_if.

  (* lazymatch goal with
  | |- entails_under ?env _ _ =>
    pose proof (@entails_under_unk env k (vbool false))
    (* [ | resolve_fn_in_env ]; simpl *)
  end.
  specializes H. resolve_fn_in_env. simpl in H. *)

  fbiabduction.

  fsimpl.

  rewrite norm_ens_ens_void_l.
  apply ent_ens_single.
  xsimpl.
  - intros. f_equal. math.
  - intros. subst. f_equal.
Qed.


Definition toss1 : ufun := fun _ =>
  sh "k" (∀ x a,
    bind (req (x~~>vint a) (ens_ (x~~>(a+1));; unk "k" true)) (fun r1 =>
      ∀ b, bind (req (x~~>vint b) (ens_ (x~~>(b+1));; unk "k" false)) (fun r2 =>
        discard "k";;
        ens (fun r3 => \[r3 = vadd r1 r2])))).

Definition toss_env1 := Fmap.single "toss" toss1.

(* let flipi () = < let v = toss () in if v then 0 else 0 > *)
Definition flipi1 : flow :=
  rs (
    bind (unk "toss" vunit) (fun v =>
    ens (fun r1 => \[If v = true then r1 = 1 else r1 = 0]))
  ).

Theorem flipi_summary1 :
  entails_under toss_env1 flipi1 flipi_spec.
Proof.
  unfold flipi1, flipi_spec.
  funfold1 "toss". unfold toss1.
  freduction.
  fsimpl. fintros x. fspecialize x.
  fsimpl. fintros a. fspecialize a.
  fsimpl. fentailment. xsimpl.
  case_if.
  fsimpl. fspecialize (a+1).
  fsimpl. fbiabduction.
  case_if.
  fsimpl. 2: { unfold toss_env1. solve_not_indom. }
  rewrite norm_ens_ens_void_l.
  fentailment.
  xsimpl.
  - intros. f_equal. math.
  - intros. simpl in H. rewrite H. f_equal.
Qed.

(*

let toss_n n =
  if n = 0 then
    true
  else
    let r1 = toss () in
    let r2 = toss_n (n - 1) in
    r1 && r2

*)
Definition toss_n : ufun := fun (n:val) =>
  (* req \[vgt n (vint 0)] *)
    (disj
      (ens (fun r => \[r = true /\ veq n 0]))
      (ens_ \[vgt n 0];;
        bind (toss vunit) (fun r1 =>
        bind (unk "toss_n" (vsub n 1)) (fun r2 =>
        ens (fun r => \[r = vand r1 r2]))))).

Definition toss_n_env :=
  let d :=
(fun v : val => ∀ n acc, rs (bind (bind (bind (ens (fun r : val => \[r = v])) (fun r1 : val => bind (unk "toss_n" (vsub n 1)) (fun r2 : val => ens (fun r : val => \[r = vand r1 r2])))) (fun r2 : val => ens (fun r : val => \[r = vand acc r2]))) (fun v0 : val => ens (fun r : val => \[If v0 = true then r = 1 else r = 0]))))
  in
  Fmap.update (Fmap.single "toss_n" toss_n) "k" d.

Definition main n : flow :=
  rs (
    bind (unk "toss_n" (vint n)) (fun v =>
    ens (fun r => \[If v = true then r = 1 else r = 0]))).

Definition main_spec_weaker n : flow :=
  ∀ x a,
    req (x~~>vint a \* \[vgt (vint n) 0])
      (∃ b, ens (fun r => x~~>b \* \[vge b (vadd a n) /\ r = 1])).

(* Lemma lemma_weaker : forall acc x n,
  entails
    (rs (bind (unk "toss_n" (vint n)) (fun v =>
      ens (fun r1 =>
        \[If vand acc v = true then r1 = vint 1 else r1 = vint 0]))))
    (∀ a, req (x~~>vint a \* \[n > 0])
      (∃ b, ens (fun r => x~~>vint b \*
        \[b > a+n /\ (If acc = true then r = 1 else r = 0)]))).
        (* \[b > a+n /\ (acc = true /\ r = 1 \/ acc = false /\ r = 0)]))). *)
Proof.
  (* induction_wf IH: (downto 0) n. *)
(* Admitted. *)
Abort. *)


(* Lemma lemma_weaker2_under : forall (n:int) (acc:bool),
  entails_under toss_n_env n acc

    (rs (bind
      (bind (unk "toss_n" n) (fun r2 =>
        ens (fun r => \[r = vand acc r2])))
      (fun v => ens (fun r => \[If v = true then r = 1 else r = 0]))))

    (∀ x a, req (x~~>vint a \* \[n >= 0])
      (∃ b, ens (fun r => x~~>vint b \*
        (* \[b > a+n /\ (r=1 \/ r=0)]))). *)
        \[b > a+n /\ (If acc = true then r = 1 else r = 0)]))).
        (* \[b > a+n /\ (acc = true /\ r = 1 \/ acc = false /\ r = 0)]))). *)
Proof.
Admitted. *)

Lemma ent_seq_defun_idem_weaker : forall s x u1 u2 f1 f2,
  Fmap.indom s x ->
  Fmap.read s x = u1 ->
  (forall v, entails (u1 v) (u2 v)) ->
  entails_under s f1 f2 ->
  entails_under s (defun x u2;; f1) f2.
Proof.
  unfold entails_under. intros.
  inverts* H3.
  inverts H11.
  applys H2.

Admitted.


Example ex_weaken_env : forall s x u1 u2 f1 f2,
  s = Fmap.single "x" u1 ->
  x = "x" ->
  u1 = (fun _ => ens (fun r => \[r = 1])) ->
  u2 = (fun _ => ens (fun r => \[r = 1 \/ r = 2])) ->
  f1 = unk "x" vunit ->
  f2 = ens (fun r => \[r = 1]) ->

  Fmap.indom s x ->
  Fmap.read s x = u1 ->
  (forall v, entails (u1 v) (u2 v)) ->
  entails_under s f1 f2 ->
  entails_under s (defun x u2;; f1) f2.
Proof.
  introv H5 H6 H7 H8 H9 H10.
  introv H1 H2 H3 H4.
  applys ent_seq_defun_idem_weaker H1 H2 H3 H4.
Qed.

Lemma norm_bind_trivial: forall f1,
  entails (bind f1 (fun r2 => ens (fun r1 => \[r1 = r2]))) f1.
Proof.
  intros.
  applys norm_bind_trivial_sf.
  admit.
Admitted.

#[global]
Instance Proper_bind_entails_r f1 :
  Proper (Morphisms.pointwise_relation val entails ====> entails)
    (@bind f1).
Proof.
  intros. applys Proper_bind_entails_sf.
  admit.
Admitted.

#[global]
Instance Proper_seq_entails_r f1 :
  Proper (entails ====> entails)
    (@seq f1).
Proof.
  intros. applys Proper_seq_entails_sf.
  admit.
Admitted.

Lemma norm_bind_assoc: forall f fk fk1,
  entails (bind (bind f fk) fk1)
    (bind f (fun r => bind (fk r) fk1)).
Proof.
  intros.
  applys norm_bind_assoc_sf.
  admit.
Admitted.

Lemma norm_seq_assoc: forall f1 f2 f3,
  bientails (f1;; f2;; f3) ((f1;; f2);; f3).
Proof.
  intros.
  applys norm_seq_assoc_sf.
  admit.
Admitted.

Lemma lemma_weaker2_attempt : forall (n:int) (acc:bool),
  entails_under toss_n_env

    (rs (bind
      (bind (unk "toss_n" n) (fun r2 =>
        ens (fun r => \[r = vand acc r2])))
      (fun v => ens (fun r => \[If v = true then r = 1 else r = 0]))))

    (∀ x a, req (x~~>vint a \* \[n >= 0])
      (∃ b, ens (fun r => x~~>vint b \*
        \[b >= a+n /\ (If acc = true then r = 1 else r = 0)]))).
Proof.
  intros n. induction_wf IH: (downto 0) n. intros.

  funfold1 "toss_n". unfold toss_n.
  fsimpl_old.
  applys ent_disj_l.
  {
    fintro x. fintro a.

    (* base case. no shifts here *)
    assert (forall (P:val->Prop) P1,
      entails (ens (fun r => \[P r /\ P1]))
        (ens_ \[P1];; ens (fun r => \[P r]))).
    { introv H. inverts H. applys s_seq; applys s_ens; heaps. }
    rewrite H.
    clear H.

    fsimpl_old.
    fsimpl_old.
    fentailment. unfold veq, virel. intros.

    applys ent_req_r.
    fsimpl_old.
    rewrite <- norm_seq_assoc; shiftfree.
    fentailment. intros.
    finst a.
    rewrite norm_ens_ens_void_l.
    fentailment. xsimpl. intros. split. rewrite H. math.
    destruct acc.
    - case_if.
      { case_if. assumption. }
      { specializes C. constructor. false. }
    - case_if.
      { specializes C. constructor. false. }
      { case_if. assumption. }
  }
  {
    (* recursive case *)
    fsimpl_old.
    fentailment. unfold vgt. simpl. intro.
    unfold toss.
    rewrite red_init.
    rewrite red_extend.
    rewrite red_extend.
    rewrite red_extend.
    rewrite red_rs_sh_elim.

    (* applys ent_seq_defun_idem. *)
    applys ent_seq_defun_idem_weaker.
    {
      unfold toss_n_env. unfold update.
      applys Fmap.indom_union_l.
      applys Fmap.indom_single.
    }
    { reflexivity. }
    {
      intros.
      unfold toss_n_env. unfold update.
      rewrite Fmap.read_union_l.
      2: { applys Fmap.indom_single. }
      rewrite Fmap.read_single.
      unfold entails.
      intros.
      inverts H0. specializes H7 n.
      inverts H7. specializes H6 acc.
      assumption.
    }

    fintro x. fintro a.
    finst x. finst a.

    funfold1 "k".

    fsimpl_old.
    finst n.
    fsimpl_old. finst acc.

    rewrite norm_req_req.
    fentailment. xsimpl.
    applys ent_req_r. fentailment. intros.
    simpl.

    pose proof IH as IH1.
    specializes IH (n-1).
    forward IH. unfold virel in H. unfold downto. math.
    specializes IH acc.
    fsimpl_old.
    simpl.
    rewrite norm_bind_trivial.
    rewrite IH.
    clear IH.

    fsimpl_old. finst x.
    fsimpl_old. finst (a+1).
    fsimpl_old.

    rewrite norm_req_req.

    rewrite norm_ens_req_transpose. 2: { applys b_pts_single. }
    rewrite norm_req_pure_l. 2: { reflexivity. }
    rewrite norm_seq_ens_empty.

    applys ent_req_l. math.
    fintro a1.
    rewrite norm_ens_hstar_pure_r.
    fsimpl_old.

    rewrite norm_ens_void_pure_swap.
    fentailment. intros.
    fsimpl_old.

    rewrite norm_bind_all_r.
    fsimpl_old. finst a1.

    lets: norm_bind_req (x~~>a1).
    setoid_rewrite H2.
    clear H2.

    rewrite norm_bind_ens_req. 2: { shiftfree. }
    fsimpl_old.

    rewrite norm_ens_req_transpose. 2: { applys b_pts_single. }
    rewrite norm_req_pure_l. 2: { reflexivity. }
    rewrite norm_seq_ens_empty.

    setoid_rewrite norm_bind_seq_assoc. 2: { shiftfree. }

    rewrite norm_bind_seq_past_pure_sf. 2: { shiftfree. }
    fsimpl_old.

    (* we are missing a proper instance for unfolding on the right side of a bind *)
    lazymatch goal with
    | |- entails_under ?env _ _ =>
      pose proof (@entails_under_unk env "k" (vbool false))
    end.
    specializes H2. unfold toss_n_env. resolve_fn_in_env. simpl in H2.
    Fail rewrite H2.
    Fail setoid_rewrite H2.
    clear H2.

    (* workaround: eliminate the bind before we unfold *)
    applys ent_seq_ens_rs_bind_ens_pure_l. intros.

    funfold1 "k".
    fsimpl_old. finst n.
    fsimpl_old. finst false.

    rewrite norm_bind_val.

    specializes IH1 (n-1).
    forward IH1. unfold virel in H. unfold downto. math.
    specializes IH1 false.
    simpl in IH1.

    (* try to get the goal to match the IH *)
    simpl.
    rewrite norm_bind_seq_def.
    rewrite norm_bind_seq_def.
    rewrite <- norm_seq_assoc.

    lets H3: norm_seq_ignore_res_l false (ens (fun r => \[r = false])).
    rewrite H3.
    clear H3.

    rewrite IH1. clear IH1.

    fsimpl_old. finst x.
    fsimpl_old. finst (a1 + 1).
    fsimpl_old.
    rewrite norm_req_req.

    rewrite norm_ens_req_transpose. 2: { applys b_pts_single. }
    rewrite norm_req_pure_l. 2: { reflexivity. }
    rewrite norm_seq_ens_empty.

    fentailment. math.
    fintro a2.

    rewrite norm_rearrange_ens.
    fsimpl_old.
    fentailment. intros.
    finst a2.

    case_if. { false C. constructor. }
    fsimpl_old.
    rewrite norm_ens_ens_void_l.
    fentailment.
    xsimpl.
    intros.
    split.
    math.
    case_if; subst; simpl.

    - f_equal.

    - rewrite Z.add_0_r.
      reflexivity.
  }
Qed.

(*
  This statement differs from the proved lemma above in two ways:

  1. using entails instead of entails_under, which is justified because the proof of main also uses toss_n_env. This sidesteps the need for framing away the additions to the environment in main proof due to dynamic functions.

  2. not including extra existential f due to defun, which is not observable if the name is fresh.
*)
Definition lemma_weaker2 := forall (n:int) (acc:bool),
  entails

    (rs (bind
      (bind (unk "toss_n" n) (fun r2 =>
        ens (fun r => \[r = vand acc r2])))
      (fun v => ens (fun r => \[If v = true then r = 1 else r = 0]))))

    (∀ x a, req (x~~>vint a \* \[n >= 0])
      (∃ b, ens (fun r => x~~>vint b \*
        \[b > a+n /\ (If acc = true then r = 1 else r = 0)]))).

Theorem main_summary : forall n, exists f,
  lemma_weaker2 ->
  entails_under toss_n_env (main n) (f;; main_spec_weaker n).
Proof.
  unfold main_spec_weaker, main. intros n.

  exists (∃ k, disj empty (defun k (fun v =>
    rs (bind (bind (ens (fun r => \[r = v])) (fun r1 => bind (unk "toss_n" (viop (fun x y => x - y) n 1)) (fun r2 => ens (fun r => \[r = vand r1 r2])))) (fun v0 => ens (fun r => \[If v0 = true then r = 1 else r = 0])))))).

  intros lemma_weaker.

  funfold1 "toss_n".
  unfold toss_n.
  fsimpl_old.
  applys ent_disj_l.
  {
    (* the defun isn't used *)
    finst "k". { intros. shiftfree. } fleft.
    lazymatch goal with
    | |- entails_under _ _ (empty;; ?f) =>
      rewrite (norm_seq_empty_l f)
    end.

    (* base case *)
    rewrite <- hstar_pure_post_pure.
    rewrite <- norm_ens_ens_void_l.
    fsimpl_old.
    case_if. clear C.
    fentailment. simpl. intros.
    fintro x.
    fintro a.
    apply ent_req_r.
    finst a.
    rewrite norm_ens_ens_void_l.
    fentailment. xsimpl. simpl. math.
  }
  { fsimpl_old.
    fentailment. simpl. intros.

    unfold toss.
    rewrite red_init.
    rewrite red_extend.
    rewrite red_extend.
    rewrite red_rs_sh_elim.

    (* fintro k. *)
    finst "k". { shiftfree. }
    (* recursive case; use the defun *)
    fright. applys ent_seq_defun_both.

    fintro x. finst x.
    fintro a. finst a.

    funfold1 "k".
    lazymatch goal with
    | |- entails_under ?e _ _ => remember e as env
    end.

    fsimpl_old.
    fentailment. xsimpl.

    unfolds in lemma_weaker.
    rewrite lemma_weaker.
    fold lemma_weaker2 in lemma_weaker.

    (* framing lemma *)
    (* subst.
    lets: ent_env_frame lemma_weaker2_under.
    admit.
    rewrite H0.
    lazymatch goal with
    | |- entails_under ?e _ _ => remember e as env
    end.
    clear H0. *)

    fsimpl_old. finst x.
    fsimpl_old. finst (a+1).
    fsimpl_old.
    rewrite norm_req_req.

    rewrite norm_ens_req_transpose. 2: { apply b_pts_single. }
    rewrite norm_req_pure_l. 2: { reflexivity. }
    rewrite norm_seq_ens_empty.

    fentailment. math.
    fsimpl_old. fintro b.
    rewrite norm_rearrange_ens.
    fsimpl_old.

    apply ent_seq_ens_void_pure_l. intros.

    case_if. 2: { false* C. }

    fsimpl_old. finst b.

    subst.
    funfold1 "k".
    lazymatch goal with
    | |- entails_under ?e _ _ => remember e as env
    end.

    fsimpl_old.

    rewrite norm_ens_req_transpose. 2: { apply b_pts_single. }
    rewrite norm_req_pure_l. 2: { reflexivity. }
    rewrite norm_seq_ens_empty.

    unfolds in lemma_weaker.
    rewrite lemma_weaker.
    fold lemma_weaker2 in lemma_weaker.

    fsimpl_old. finst x.
    fsimpl_old. finst (b+1).
    fsimpl_old.
    rewrite norm_req_req.

    rewrite norm_ens_req_transpose. 2: { apply b_pts_single. }
    rewrite norm_req_pure_l. 2: { reflexivity. }
    rewrite norm_seq_ens_empty.

    fentailment. math.
    fintro b1.

    rewrite norm_rearrange_ens.

    fsimpl_old.
    fentailment. intros.
    case_if.
    fsimpl_old.

    rewrite norm_ens_ens_void_l.
    finst b1.
    fentailment. { xsimpl. intros. simpl. split. math. rewrite H2; f_equal. }
  }
Qed.

(* proof attempt with tactics *)

Definition toss_n_env1 :=
  Fmap.single "toss_n" toss_n.

(* norm_ens_pure_conj  *)
(* Lemma *)
(* Close Scope flow_scope. *)
(* Unset Printing Notations. Set Printing Coercions. Set Printing Parentheses. *)
(* Check norm_ens_pure_conj. *)

Theorem main_summary1 : forall n,
  lemma_weaker2 ->
  entails_under toss_n_env1 (main n) (main_spec_weaker n).
Proof.
  intros n lemma. unfold main, main_spec_weaker.
  funfold1 "toss_n". unfold toss_n.
  fsimpl.
  applys ent_disj_l.
  {
    rewrite norm_ens_pure_conj1.
    fsimpl. fentailment. simpl. intros.
    case_if.
    fintros x. fintros a.
    fassume.
    fexists a.
    rewrite norm_ens_ens_void_l.
    fentailment. xsimpl. intros. splits*. math.
  }
  {
    fsimpl.
    fentailment. simpl. intros.
    unfold toss.
    freduction.
    fsimpl.

    fintros x. fspecialize x.
    fintros a. fspecialize a.

    fsimpl.
    rewrite norm_req_req.
    fentailment. xsimpl.
    fassume. fentailment. intros.
    fexists (a+1).

    (* fsimpl. *)

    unfolds in lemma.
    (* TODO now rewriting is blocked because of defun being left inside *)

    rewrite lemma.
    fold lemma_weaker2 in lemma.

    fsimpl. finst x.
    fsimpl. finst (a+1).
    fsimpl.
    rewrite norm_req_req.

    fbiabduction.
    fentailment. math.
    fintro b.
    fsimpl.
    rewrite norm_rearrange_ens.
    fsimpl.
    fentailment. intros.
    case_if. 2: { false C. constructor. }
    fsimpl.
    finst b.
    fsimpl.

    fsimpl_rew.

    unfolds in lemma.
    rewrite lemma.
    fold lemma_weaker2 in lemma.


    fsimpl.

    (* fintro x0. *)

    admit.
  }


(* Qed. *)
Abort.

(* undone proof for stronger lemma *)

Definition main_spec : flow :=
  ∀ x a n,
    req (x~~>vint a \* \[n > 0])
      (ens (fun r => x~~>(a + Z.pow 2 (n+1) - 2) \* \[r = 1])).

Lemma lemma : forall acc x n,
  entails
    (rs (bind (unk "toss" (vint n)) (fun v =>
      ens (fun r1 =>
        \[vand acc v = true /\ r1 = vint 1 \/ vand acc v = false /\ r1 = vint 0]))))
    (∃ a, req (x~~>vint a \* \[n > 0]) (ens (fun r => x~~>vint (a + Z.pow 2 (n+1) - 2) \* \[acc = true /\ r = 1 \/ acc = false /\ r = 0]))).
Proof.
Abort.

(* Theorem main_summary : forall n,
  entails_under toss_env (main n) main_spec.
Proof.
Abort. *)

End Toss.
