
From ShiftReset Require Import Logic Automation Entl GEntl.
From ShiftReset Require ExamplesEnt.
Local Open Scope string_scope.

Module Multi.

(* < sh k. let a = k true in let b = k false in a && b > *)
Definition flip1 : ufun := fun _ =>
  rs (
    sh "k" (
      bind (unk "k" true) (fun r1 =>
      bind (unk "k" false) (fun r2 =>
        discard "k";; ens (fun r => \[r = vand r1 r2])
      )))).

Theorem flip_reduction1: forall v1,
  entails (flip1 v1) (ens (fun r => \[r = false])).
Proof.
  intros. unfold flip1.
  freduction.
  funfold2. fsimpl.
  funfold2. fsimpl.
  funfold2. fsimpl.
  reflexivity.
Qed.

(* this shows how [flip_reduction1] works *)
Theorem flip_reduction2: forall v1,
  entails (flip1 v1) (ens (fun r => \[r = false])).
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

  rewrite norm_seq_defun_discard1.
  rewrite norm_rs_ens.
  reflexivity.
Qed.

End Multi.

Module Times.

Definition vmul (v1 v2 : val) : val :=
  match v1, v2 with
  | _, vint 1 => v1
  | vint 1, _ => v2
  | vint i1, vint i2 => vint (i1 * i2)
  | _, _ => vunit
  end.

(* Definition vmul (v1 v2 : val) : option val :=
  match v1, v2 with
  | _, vint 1 => Some v1
  | vint 1, _ => Some v2
  | vint i1, vint i2 => Some (vint (i1 * i2))
  | _, _ => None
  end. *)

Definition aux : ufun := fun (xs:val) =>
  (disj
    (ens (fun r => \[xs = vlist nil /\ r = 1]))
    (disj
      (∃ ys, ens_ \[xs = vlist (vint 0::ys)];;
        sh "k" (discard "k";; ens (fun r => \[r = 0])))
      (∃ x ys, ens_ \[xs = vlist (x::ys)];;
        bind (unk "aux" (vlist ys)) (fun z =>
          ens (fun r => \[r = vmul x z]))))).

Definition times : ufun := fun (xs:val) =>
  rs (aux xs).

Fixpoint all {A:Type} P (xs:list A) : Prop :=
  match xs with
  | nil => True
  | x::ys => P x /\ all P ys
  end.

Definition is_vint (v:val) : Prop :=
  exists i, v = vint i.

Definition is_vint_vlist (v:val) : Prop :=
  exists xs, v = vlist xs /\ all is_vint xs.

Fixpoint times_pure (xs:list val) : val :=
  match xs with
  | nil => vint 1
  | x::nil => x
  | 0::_ => vint 0
  | x::ys => vmul x (times_pure ys)
  end.

(* Fixpoint times_pure (xs:list int) : int :=
  match xs with
  | nil => 1
  | x::nil => x
  | 0::_ => 0
  | x::ys => x * times_pure ys
  end. *)

Lemma vmul_one: forall x,
  vmul x 1 = x.
Proof.
  intros x.
  destruct x; try reflexivity.
  simpl. destruct z; try reflexivity.
  destruct p; reflexivity.
Qed.

Lemma times_singleton: forall x,
  times_pure (x :: nil) = x.
Proof.
  intros x.
  destruct x; try reflexivity.
  simpl. destruct z; try reflexivity.
Qed.

(* These simple properties are admitted, pending a better encoding
  of mul for values *)
Lemma vmul_assoc: forall x y z,
  (* is_vint x ->
  is_vint y ->
  is_vint z -> *)
  vmul x (vmul y z) = vmul (vmul x y) z.
Proof.
  intros x y z.
  (* destruct x; destruct y; destruct z; auto. *)
Admitted.

Lemma times_any_zero : forall x ys,
  vint 0 = times_pure (x :: vint 0 :: ys).
Proof.
Admitted.

Lemma times_first_two : forall a b c,
  times_pure (a :: b :: c) = times_pure (vmul a b :: c).
Proof.
Admitted.

(* Import ExamplesEnt.Axioms. *)

Lemma lemma : forall xs x n,
  (forall a, gentails n (unk "aux" a) (aux a)) ->
  gentails n
    (rs (bind (aux (vlist xs)) (fun z => ens (fun r => \[r = vmul x z]))))
    (ens (fun r => \[r = times_pure (x :: xs)])).
Proof.
  intros xs.
  induction_wf IH: list_sub xs.
  introv Haux.
  destruct xs.
  {
    unfold aux.
    fsimpl.
    applys gentl_disj_l.
    (* get rid of spurious cases *)
    2: {
      fsimpl.
      applys gentl_disj_l.
      { fdestruct ys.
        fsimpl.
        fentailment. intros. false H. }
      { fdestruct x0. fdestruct ys.
        fsimpl.
        fentailment. intros. false H. } }
    fsimpl.
    fentailment. intros.
    fentailment. xsimpl. intros. subst r.
    rewrite times_singleton.
    rewrite vmul_one.
    reflexivity.
  }
  {
    unfold aux.
    fsimpl.
    applys gentl_disj_l. { fsimpl. fentailment. intros. false H. }
    fsimpl.
    applys gentl_disj_l.
    { fdestruct ys.
      fsimpl. fentailment. intros. injects H.
      freduction.
      funfold2.
      fsimpl.
      fentailment. xsimpl. intros. subst.
      simpl.
      applys times_any_zero. }
    { fdestruct x0. fdestruct ys.
      fsimpl. fentailment. intros. injects H.

      specializes Haux (vlist ys).

      rewrite Haux.

      rewrite norm_bind_assoc.
      setoid_rewrite norm_bind_val.

      specializes IH ys.
      specializes IH (vmul x x0) Haux.
      rewrite times_first_two.
      (* more pain *)
      applys_eq IH.
      f_equal. f_equal.
      applys fun_ext_dep. intros.
      f_equal.
      applys fun_ext_dep. intros.
      rewrite vmul_assoc.
      reflexivity. }
  }
Qed.

Import ExamplesEnt.Axioms.

Lemma lemma : forall xs x,
  (forall a, entails (unk "aux" a) (aux a)) ->
  entails
    (rs (bind (aux (vlist xs)) (fun z => ens (fun r => \[r = vmul x z]))))
    (ens (fun r => \[r = times_pure (x :: xs)])).
Proof.
  intros xs.
  induction_wf IH: list_sub xs.
  introv Haux.
  destruct xs.
  {
    unfold aux.
    fsimpl.
    applys entl_disj_l.
    (* get rid of spurious cases *)
    2: {
      fsimpl.
      applys entl_disj_l.
      { fdestruct ys.
        fsimpl.
        fentailment. intros. false H. }
      { fdestruct x0. fdestruct ys.
        fsimpl.
        fentailment. intros. false H. } }
    fsimpl.
    fentailment. intros.
    fentailment. xsimpl. intros. subst r.
    rewrite times_singleton.
    rewrite vmul_one.
    reflexivity.
  }
  {
    unfold aux.
    fsimpl.
    applys entl_disj_l. { fsimpl. fentailment. intros. false H. }
    fsimpl.
    applys entl_disj_l.
    { fdestruct ys.
      fsimpl. fentailment. intros. injects H.
      freduction.
      funfold2.
      fsimpl.
      fentailment. xsimpl. intros. subst.
      simpl.
      applys times_any_zero. }
    { fdestruct x0. fdestruct ys.
      fsimpl. fentailment. intros. injects H.
      rewrite Haux.

      rewrite norm_bind_assoc.
      setoid_rewrite norm_bind_val.

      specializes IH ys.
      specializes IH (vmul x x0) Haux.
      rewrite times_first_two.
      (* more pain *)
      applys_eq IH.
      f_equal. f_equal.
      applys fun_ext_dep. intros.
      f_equal.
      applys fun_ext_dep. intros.
      rewrite vmul_assoc.
      reflexivity. }
  }
Qed.

Theorem times_spec : forall xs,
  (forall a, entails (unk "aux" a) (aux a)) ->
  entails
    (times (vlist xs))
    (ens (fun r => \[r = times_pure xs])).
Proof.
  intros xs.
  unfold times.
  intros Haux.
  unfold aux.
  fsimpl.
  applys entl_disj_l.
  { fsimpl.
    fentailment. intros. injects H.
    fentailment. xsimpl. auto. }
  fsimpl.
  applys entl_disj_l.
  { fdestruct ys.
    fsimpl.
    fentailment. intros. injects H.
    freduction.
    funfold2.
    fsimpl.
    fentailment. xsimpl. intros. subst. simpl. destruct ys; reflexivity. }
  {
    fdestruct x. fdestruct ys.
    fsimpl.
    fentailment. intros. injects H.
    fsimpl.
    rewrite Haux.
    apply* lemma.
  }
Qed.

End Times.

Module Toss.

(* let toss () =
  shift k.
    x := !x+1;
    let r1 = k true in
    x := !x+1;
    let r2 = k false in
    r1 + r2
*)
Definition toss1 : ufun := fun _ =>
  sh "k" (∀ x a,
    bind (req (x~~>vint a) (ens_ (x~~>(a+1));; unk "k" true)) (fun r1 =>
      ∀ b, bind (req (x~~>vint b) (ens_ (x~~>(b+1));; unk "k" false)) (fun r2 =>
        discard "k";;
        ens (fun r3 => \[r3 = vadd r1 r2])))).

(* let flipi () = < let v = toss () in if v then 0 else 0 > *)
Definition flipi1 : flow :=
  rs (
    bind (unk "toss" vunit) (fun v =>
    ens (fun r1 => \[If v = true then r1 = 1 else r1 = 0]))
  ).

Theorem flipi_summary2 :
  (forall a, entails (unk "toss" a) (toss1 a)) ->
  entails flipi1 ExamplesEnt.Toss.flipi_spec.
Proof.
  intros Htoss.
  unfold flipi1, ExamplesEnt.Toss.flipi_spec.
  rewrite Htoss. unfold toss1.
  freduction.
  fintros x. fspecialize x.
  fintros a. fspecialize a.
  fsimpl. fentailment. xsimpl.
  funfold2. fsimpl.
  case_if.
  fsimpl. fspecialize (a+1).
  fsimpl. fbiabduction.
  funfold2. fsimpl.
  case_if.
  fsimpl.
  funfold3 "k".
  fsimpl.
  rewrite norm_ens_ens_void_l.
  fentailment.
  xsimpl.
  - intros. f_equal. math.
  - intros. simpl in H. rewrite H. f_equal.
Qed.

(* let toss_n n =
  if n = 0 then
    true
  else
    let r1 = toss () in
    let r2 = toss_n (n - 1) in
    r1 && r2 *)
Definition toss_n1 : ufun := fun (n:val) =>
  (disj
    (ens (fun r => \[r = true /\ veq n 0]))
    (ens_ \[vgt n 0];;
      bind (toss1 vunit) (fun r1 =>
      bind (unk "toss_n" (vsub n 1)) (fun r2 =>
      ens (fun r => \[r = vand r1 r2]))))).

Lemma entl_elim_bind: forall P fk f1 (f:var) u H,
  (forall r, P r -> entails (defun f u;; ens_ H;; rs (fk r)) f1) ->
    entails (defun f u;; ens_ H;; rs (bind (ens (fun r => \[P r])) fk)) f1.
Proof.
  unfold entails. intros.
  inverts* H1.
  inverts H9.
  inverts* H10.
  inverts H9.
  inverts H11.
  - inverts* H2.
    inverts H12. heaps.
    applys H0 H1.
    applys* s_seq.
    applys* s_defun.
    applys* s_seq.
    applys s_ens. heaps.
    applys* s_rs_sh.
  - inverts* H9.
    inverts H11. heaps.
    applys H0 H1.
    applys* s_seq.
    applys* s_defun.
    applys* s_seq.
    applys s_ens. heaps.
    applys* s_rs_val.
Qed.

Import ExamplesEnt.Axioms.

Lemma lemma_weaker : forall (n:int) (acc:bool),
  (forall a, entails (unk "toss_n" a) (toss_n1 a)) ->
  entails
    (rs (bind
      (bind (unk "toss_n" n) (fun r2 =>
        ens (fun r => \[r = vand acc r2])))
      (fun v => ens (fun r => \[If v = true then r = 1 else r = 0]))))

    (∀ x a, req (x~~>vint a \* \[n >= 0])
      (∃ b, ens (fun r => x~~>vint b \*
        \[b >= a+n /\ (If acc = true then r = 1 else r = 0)]))).
Proof.
  intros n. induction_wf IH: (downto 0) n. introv Htoss_n.
  rewrite Htoss_n. unfold toss_n1.
  fsimpl.
  applys entl_disj_l.
  { (* base case *)
    fsimpl. fentailment. simpl. intros ->.
    fintros x. fintros a.
    destruct acc.
    - case_if.
      case_if. 2: { false C0. constructor. }
      fentailment.
      rewrite norm_ens_ens_void_l.
      fexists a.
      fentailment. xsimpl. intros. splits*. math.
    - case_if.
      case_if. { false C0. constructor. }
      fentailment.
      rewrite norm_ens_ens_void_l.
      fexists a.
      fentailment. xsimpl. intros. splits*. math. }
  { (* recursive case *)
    fsimpl.
    fentailment. unfold vgt. simpl. intro.
    unfold toss1.
    freduction.
    fintros x. fintros a.
    fspecialize x. fspecialize a.
    fsimpl.
    rewrite norm_req_req.
    fentailment. xsimpl.
    fentailment. fentailment. intros.
    funfold2.
    fsimpl.
    simpl.
    pose proof IH as IH1.
    specializes IH (n-1).
    forward IH. unfold virel in H. unfold downto. math.
    specializes IH acc Htoss_n.
    simpl in IH.
    rewrite norm_bind_trivial.

    rewrite IH. clear IH.

    fsimpl. fspecialize x.
    fsimpl. fspecialize (a+1).
    fsimpl.

    rewrite norm_req_req.
    fbiabduction.
    fentailment. math.
    fdestruct a1.
    rewrite norm_ens_hstar_pure_r.
    fsimpl.
    rewrite norm_ens_void_pure_swap.
    fentailment. intros.
    rewrite* norm_bind_all_r.
    fspecialize a1.
    lets H2: norm_bind_req (x~~>a1).
    setoid_rewrite H2.
    clear H2.
    rewrite norm_bind_ens_req.
    fsimpl.
    fbiabduction.
    setoid_rewrite norm_bind_seq_assoc. 2: { shiftfree. }
    rewrite norm_bind_seq_past_pure_sf. 2: { shiftfree. }
    fsimpl.
    applys entl_elim_bind. intros.
    funfold3 "k".
    fsimpl.
    simpl.
    case_if.

    { case_if in H2. 2: { false C0. constructor. }

      specializes IH1 (n-1).
      forward IH1. unfold virel in H. unfold downto. math.
      specializes IH1 false Htoss_n.
      simpl in IH1.

      rewrite norm_bind_trivial.
      rewrite IH1. clear IH1.

      (* everything below this point is duplicated *)
      fspecialize x.
      fspecialize (a1 + 1).
      fsimpl.
      rewrite norm_req_req.
      fbiabduction.
      fentailment. math.
      fdestruct b. fexists b.
      fsimpl. fentailment. intros.
      case_if. fsimpl.
      funfold2. fsimpl.
      rewrite norm_ens_ens_void_l.
      fentailment. xsimpl. intros.
      split. math. subst. simpl. f_equal. }

    { case_if in H2. { false C0. constructor. }

      specializes IH1 (n-1).
      forward IH1. unfold virel in H. unfold downto. math.
      specializes IH1 false Htoss_n.
      simpl in IH1.

      (* try to get the goal to match the IH *)
      rewrite norm_bind_seq_def.
      rewrite norm_bind_seq_def.
      rewrite <- norm_seq_assoc.

      lets H3: norm_seq_ignore_res_l false (ens (fun r => \[r = false])).
      rewrite H3.
      clear H3.

      rewrite IH1. clear IH1.

      (* everything below this point is duplicated *)
      fspecialize x.
      fspecialize (a1 + 1).
      fsimpl.
      rewrite norm_req_req.
      fbiabduction.
      fentailment. math.
      fdestruct b. fexists b.
      fsimpl. fentailment. intros.
      case_if. fsimpl.
      funfold2. fsimpl.
      rewrite norm_ens_ens_void_l.
      fentailment. xsimpl. intros.
      split. math. subst. simpl. f_equal.
    }
  }
Qed.

End Toss.

Module Main.

Import Toss.

Definition main n : flow :=
  rs (
    bind (unk "toss_n" (vint n)) (fun v =>
    ens (fun r => \[If v = true then r = 1 else r = 0]))).

Theorem main_summary1 : forall n,
  (forall a, entails (unk "toss_n" a) (toss_n1 a)) ->
  entails (main n) (ExamplesEnt.Main.main_spec_weaker n).
Proof.
  intros n. introv Htoss_n. unfold main, ExamplesEnt.Main.main_spec_weaker.
  rewrite Htoss_n. unfold toss_n1.
  fsimpl.
  applys entl_disj_l.

  { fsimpl. fentailment. simpl. intros.
    case_if.
    fintros x. fintros a.
    fentailment.
    fexists a.
    rewrite norm_ens_ens_void_l.
    fentailment. xsimpl. intros. splits*. math. }

  { fsimpl.
    fentailment. simpl. intros.
    unfold toss1.
    freduction.
    fintros x. fspecialize x.
    fintros a. fspecialize a.
    fsimpl. rewrite norm_req_req. fentailment. xsimpl.
    fentailment.
    fentailment. intros.

    funfold2.
    fsimpl.

    rewrite* lemma_weaker.

    fspecialize x.
    fspecialize (a+1).
    fsimpl.
    rewrite norm_req_req.
    fbiabduction.
    fentailment. math.
    fdestruct b.
    fsimpl.

    fentailment. intros.
    case_if. 2: { false C. constructor. }
    fsimpl.

    fspecialize b.
    fsimpl.
    fbiabduction.
    funfold2.
    fsimpl.

    rewrite* lemma_weaker.

    fspecialize x.
    fspecialize (b+1).
    rewrite norm_req_req.
    fsimpl.
    fbiabduction.
    fentailment. math.

    fdestruct b1.
    fexists b1.
    fsimpl.
    fentailment. intros.
    case_if.
    fsimpl.
    funfold2.
    fsimpl.
    rewrite norm_ens_ens_void_l.
    fentailment. xsimpl. simpl. intros. splits*. math.
  }
Qed.

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

End Main.
