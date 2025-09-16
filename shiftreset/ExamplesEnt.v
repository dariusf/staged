
(* examples based on entails_under and with explicit environments
  of functions, which doesn't scale to inductive proofs *)

From ShiftReset Require Import Logic Automation Entl.
Local Open Scope string_scope.

Module Multi.

(* < sh k. let a = k true in let b = k false in a && b > *)
Definition flip : ufun := fun _ =>
  rs (
    sh "k" (
      bind (unk "k" true) (fun r1 =>
      bind (unk "k" false) (fun r2 =>
        discard "k";;
        ens (fun r => \[r = vand r1 r2])
      )))).

Definition flip_env :=
  Fmap.single "k" (fun v : val => rs (ens (fun r => \[r = v]))).

Theorem flip_reduction: forall n v1,
  gentails n (flip v1) (ens (fun r => \[r = false])).
Proof.
  intros. unfold flip.
  rewrite red_init.
  rewrite red_rs_sh_elim.

  (* rewrite entails_under_seq_defun_idem.
  2: { unfold flip_env. apply Fmap.indom_single. }
  2: { unfold flip_env. resolve_fn_in_env. } *)
(*
  applys gent_seq_defun_idem.
  { unfold flip_env. apply Fmap.indom_single. }
  { unfold flip_env. resolve_fn_in_env. }
*)
  move_one_defun_in "k".
  rewrite norm_seq_defun_unk.
  move_defun_out.
  rewrite norm_rs_ens.
  rewrite norm_bind_val.
  move_one_defun_in "k".
  rewrite norm_seq_defun_unk.
  move_defun_out.
  rewrite norm_rs_ens.
  rewrite norm_bind_val.
  rewrite red_normal.
  rewrite norm_seq_defun_discard1.
  reflexivity.
  shiftfree.
Qed.

End Multi.

Module Axioms.

(* Justified by [gnorm_bind_trivial] *)
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

(* Justified by [gnorm_bind_assoc] *)
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

End Axioms.

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

(* let toss_n n =
  if n = 0 then
    true
  else
    let r1 = toss () in
    let r2 = toss_n (n - 1) in
    r1 && r2 *)
Definition toss_n : ufun := fun (n:val) =>
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

(* an unsound lemma that we can't prove anyway *)
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

Lemma ent_seq_ens_rs_bind_ens_pure_l: forall s P fk f H,
  (forall r, P r -> entails_under s (ens_ H;; rs (fk r)) f) ->
  entails_under s (ens_ H;; rs (bind (ens (fun r => \[P r])) fk)) f.
Proof.
  unfold entails_under. intros.
  inverts* H1.
  inverts H10.
  - inverts* H2.
    inverts H11.
    heaps.
    applys H0 H1.
    applys* s_seq.
    applys* s_rs_sh.
  - inverts H7.
    inverts H10.
    heaps.
    applys H0 H1.
    applys* s_seq.
    applys* s_rs_val.
Qed.

Import Axioms.

Lemma lemma_weaker_ind : forall (n:int) (acc:bool),
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
    fentailment_old. unfold veq, virel. intros.

    applys ent_req_r.
    fsimpl_old.
    rewrite <- norm_seq_assoc; shiftfree.
    fentailment_old. intros.
    finst a.
    rewrite norm_ens_ens_void_l.
    fentailment_old. xsimpl. intros. split. rewrite H. math.
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
    fentailment_old. unfold vgt. simpl. intro.
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
    fentailment_old. xsimpl.
    applys ent_req_r. fentailment_old. intros.
    simpl.

    pose proof IH as IH1.
    specializes IH (n-1).
    forward IH. unfold virel in H. unfold downto. math.
    specializes IH acc.
    fsimpl_old.
    simpl.
    rewrite norm_bind_trivial.
    (* rewrite (ens_. *)

    (* assert (entails (ens_ (x~~>(a+1))) (defun "a" (fun v => empty);; ens_ (x~~>(a+1)))) as ?. admit.
    rewrite H1.
    rewrite <- norm_seq_assoc. *)

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
    fentailment_old. intros.
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

    fentailment_old. math.
    fintro a2.

    rewrite norm_rearrange_ens.
    fsimpl_old.
    fentailment_old. intros.
    finst a2.

    case_if. { false C. constructor. }
    fsimpl_old.
    rewrite norm_ens_ens_void_l.
    fentailment_old.
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

End Toss.

Module Main.

Definition main n : flow :=
  rs (
    bind (unk "toss_n" (vint n)) (fun v =>
    ens (fun r => \[If v = true then r = 1 else r = 0]))).

Definition main_spec_weaker n : flow :=
  ∀ x a,
    req (x~~>vint a \* \[vgt (vint n) 0])
      (∃ b, ens (fun r => x~~>b \* \[vge b (vadd a n) /\ r = 1])).

Import Toss.

(*
  This statement differs from the proved lemma above in two ways:

  1. using entails instead of entails_under, which is justified because the proof of main also uses toss_n_env. This sidesteps the need for framing away the additions to the environment in main proof due to dynamic functions.

  2. not including extra existential f due to defun, which is not observable if the name is fresh.
*)
Definition lemma_weaker := forall (n:int) (acc:bool),
  entails

    (rs (bind
      (bind (unk "toss_n" n) (fun r2 =>
        ens (fun r => \[r = vand acc r2])))
      (fun v => ens (fun r => \[If v = true then r = 1 else r = 0]))))

    (∀ x a, req (x~~>vint a \* \[n >= 0])
      (∃ b, ens (fun r => x~~>vint b \*
        \[b > a+n /\ (If acc = true then r = 1 else r = 0)]))).

Theorem main_summary : forall n, exists f,
  lemma_weaker ->
  entails_under toss_n_env (main n) (f;; main_spec_weaker n).
Proof.
  unfold main_spec_weaker, main. intros n.

  exists (∃ k, disj empty (defun k (fun v =>
    rs (bind (bind (ens (fun r => \[r = v])) (fun r1 => bind (unk "toss_n" (viop (fun x y => x - y) n 1)) (fun r2 => ens (fun r => \[r = vand r1 r2])))) (fun v0 => ens (fun r => \[If v0 = true then r = 1 else r = 0])))))).

  intros lem.

  funfold1 "toss_n".
  unfold toss_n.
  fsimpl_old.
  applys ent_disj_l.
  {
    (* the defun isn't used *)
    finst "k". { intros. shiftfree. } fleft_old.
    lazymatch goal with
    | |- entails_under _ _ (empty;; ?f) =>
      rewrite (norm_seq_empty_l f)
    end.

    (* base case *)
    rewrite <- hstar_pure_post_pure.
    rewrite <- norm_ens_ens_void_l.
    fsimpl_old.
    case_if. clear C.
    fentailment_old. simpl. intros.
    fintro x.
    fintro a.
    apply ent_req_r.
    finst a.
    rewrite norm_ens_ens_void_l.
    fentailment_old. xsimpl. simpl. math.
  }
  { fsimpl_old.
    fentailment_old. simpl. intros.

    unfold toss.
    rewrite red_init.
    rewrite red_extend.
    rewrite red_extend.
    rewrite red_rs_sh_elim.

    (* fintro k. *)
    finst "k". { shiftfree. }
    (* recursive case; use the defun *)
    fright_old. applys ent_seq_defun_both.

    fintro x. finst x.
    fintro a. finst a.

    funfold1 "k".
    lazymatch goal with
    | |- entails_under ?e _ _ => remember e as env
    end.

    fsimpl_old.
    fentailment_old. xsimpl.

    unfolds in lem.
    rewrite lem.
    fold lemma_weaker in lem.

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

    fentailment_old. math.
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

    unfolds in lem.
    rewrite lem.
    fold lemma_weaker in lem.

    fsimpl_old. finst x.
    fsimpl_old. finst (b+1).
    fsimpl_old.
    rewrite norm_req_req.

    rewrite norm_ens_req_transpose. 2: { apply b_pts_single. }
    rewrite norm_req_pure_l. 2: { reflexivity. }
    rewrite norm_seq_ens_empty.

    fentailment_old. math.
    fintro b1.

    rewrite norm_rearrange_ens.

    fsimpl_old.
    fentailment_old. intros.
    case_if.
    fsimpl_old.

    rewrite norm_ens_ens_void_l.
    finst b1.
    fentailment_old. { xsimpl. intros. simpl. split. math. rewrite H2; f_equal. }
  }
Qed.

End Main.
