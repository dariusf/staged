
(* From ShiftReset Require Import Logic Automation. *)
From ShiftReset Require Import LogicBind AutomationBind.
Local Open Scope string_scope.

Lemma norm_ens_pure_conj: forall (P:val->Prop) (P1:Prop),
  entails
    (ens (fun r => \[P1 /\ P r]))
    (ens_ \[P1];; ens (fun r => \[P r])).
Proof.
  unfold entails. intros.
  inverts H.
  heaps.
  applys s_seq.
  applys s_ens_. heaps.
  applys s_ens. heaps.
Qed.

(* TODO this also would benefit from generalised entailment *)
Lemma norm_bind_trivial: forall f1,
  shift_free f1 ->
  entails
    (bind f1 (fun r2 => ens (fun r1 => \[r1 = r2])))
    f1.
Proof.
  unfold entails. introv Hsf H.
  inverts H.
  { inverts H8. heaps. }
  { false Hsf H6. }
Qed.

Lemma norm_ens_void_hstar_pure_l: forall P H,
  entails
    (ens_ (\[P] \* H))
    (ens_ \[P];; ens_ H).
Proof.
  unfold entails. intros.
  inverts H0.
  applys s_seq.
  - applys s_ens_. heaps.
  - applys s_ens. heaps.
Qed.

Lemma norm_ens_void_hstar_pure_r: forall P H,
  entails
    (ens_ (H \* \[P]))
    (ens_ \[P];; ens_ H).
Proof.
  unfold entails. intros.
  inverts H0.
  applys s_seq.
  - applys s_ens_. heaps.
  - applys s_ens. heaps.
Qed.

Lemma norm_ens_pure_ex: forall (A:Type) (P:A->val->Prop),
  entails
    (ens (fun r => \[exists b, P b r]))
    (∃ b, ens (fun r => \[P b r])).
Proof.
  unfold entails. intros.
  inverts H.
  heaps.
  applys s_fex. exists b.
  applys s_ens.
  heaps.
Qed.

Definition viop f a b :=
  match a, b with
  | vint a1, vint b1 => f a1 b1
  | _, _ => vunit
  end.

Definition vbop f a b :=
  match a, b with
  | vbool a1, vbool b1 => f a1 b1
  | _, _ => vunit
  end.

Definition virel f a b :=
  match a, b with
  | vint a1, vint b1 => f a1 b1
  | _, _ => False
  end.

Definition vgt a b := virel (fun x y => x > y) a b.
Definition vlt a b := virel (fun x y => x < y) a b.
Definition vge a b := virel (fun x y => x >= y) a b.
Definition vle a b := virel (fun x y => x <= y) a b.
Definition veq a b := virel (fun x y => x = y) a b.
Definition vneq a b := virel (fun x y => x <> y) a b.
Definition vsub a b := viop (fun x y => vint (x - y)) a b.

(* Definition vand a b := vbop (fun x y => vbool (x && y)) a b. *)

Definition vand (a b:val) :=
  match a, b with
  | vbool true, _ => b
  | vbool false, _ => vbool false
  | _, vbool false => vbool false
  | _, vbool true => a
  | _, _ => vunit
  end.

Coercion vint : Z >-> val.
Coercion vbool : bool >-> val.

Create HintDb staged_norm.
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
  red_rs_ens norm_bind_val
  (* trivial rewrites *)
  norm_seq_empty
  using shiftfree : staged_norm.

Ltac fsimpl := autorewrite with staged_norm.

(* Create HintDb staged_closing.

Global Hint Resolve
  ent_seq_ens_void_l

  : staged_closing.

Ltac fstep := eauto with staged_closing. *)

(* applies an uncontroversial reasoning step,
  which one would always want to apply *)
Ltac fstep := first [
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

Definition f_env :=
  Fmap.single "k" (fun v : val => rs (ens (fun r => \[r = v]))).

Lemma f_reduction: forall v1,
  entails_under f_env (f v1) (ens (fun r => \[r = false])).
Proof.
  intros.
  unfold f.
  rewrite red_init.
  rewrite red_rs_sh_elim.

  (* rewrite entails_under_seq_defun_idem.
  2: { unfold f_env. apply Fmap.indom_single. }
  2: { unfold f_env. resolve_fn_in_env. } *)

  apply ent_seq_defun_idem.
  { unfold f_env. apply Fmap.indom_single. }
  { unfold f_env. resolve_fn_in_env. }

  funfold1 "k".
  fsimpl.
  funfold1 "k".
  lazymatch goal with
  | |- entails_under ?e _ _ => remember e as env
  end.
  fsimpl.
  applys entails_under_refl.
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

(* let foo () = < let v = toss () in if v then 0 else 0 > *)
Definition foo : flow :=
  rs (
    bind (unk "toss" vunit) (fun v =>
    ens (fun r1 => \[If v = true then r1 = 1 else r1 = 0]))
  ).

Definition foo_spec : flow :=
  ∀ x a, req (x~~>vint a) (ens (fun r => x~~>(a+2) \* \[r=1])).

Theorem foo_summary :
  entails_under toss_env foo foo_spec.
Proof.
  intros.
  unfold foo, foo_spec.

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
  fsimpl.
  finst (a + 1).

  (* somehow automate this... *)
  subst.
  funfold1 "k".
  lazymatch goal with
  | |- entails_under ?e _ _ => remember e as env
  end.

  fsimpl.
  case_if.

  (* lazymatch goal with
  | |- entails_under ?env _ _ =>
    pose proof (@entails_under_unk env k (vbool false))
    (* [ | resolve_fn_in_env ]; simpl *)
  end.
  specializes H. resolve_fn_in_env. simpl in H. *)

  rewrite norm_ens_req_transpose. 2: { applys b_pts_single. }
  rewrite norm_req_pure_l. 2: { reflexivity. }
  rewrite norm_seq_ens_empty.

  fsimpl.

  rewrite norm_ens_ens_void_l.
  apply ent_ens_single.
  xsimpl.
  - intros. f_equal. math.
  - intros. subst. f_equal.
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

Lemma lemma_weaker : forall acc x n,
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
Abort.


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

Lemma ent_env_weaken: forall x u u1 s1 s2 f1 f2,
  Fmap.indom s1 x ->
  Fmap.indom s2 x ->
  Fmap.read s1 x = u ->
  Fmap.read s2 x = u1 ->
  (forall v, entails (u v) (u1 v)) ->
  entails_under s1 f1 f2 ->
  entails_under s2 f1 f2.
Proof.
  unfold entails_under. intros.
  forwards: H2. applys_eq H3. f_equal.
(* Abort. *)
Admitted.

(* Lemma entails_under_seq_defun_idem_weaker : forall s x uf f1,
  Fmap.indom s x ->
  (forall v, entails ((Fmap.read s x) v) (uf v)) ->
  entails_under s (defun x uf;; f1) f1.
Proof.
  unfold entails_under. intros.
  applys ent_env_weaken.

  inverts H1. 2: { vacuous. }
  inverts H9.

  (* lets: update_idem H H0.
  rewrite H1 in H10.
  assumption. *)
Abort. *)


(* For applying *)
Lemma ent_seq_defun_idem_weaker : forall s x uf f1 f2,
  Fmap.indom s x ->
  (forall v, entails (Fmap.read s x v) (uf v)) ->
  entails_under s f1 f2 ->
  entails_under s (defun x uf;; f1) f2.
Proof.
  intros.
  rewrite* entails_under_seq_defun_idem.
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
  fsimpl.
  applys ent_disj_l.
  {
    fintro x. fintro a.

    (* base case *)
    assert (forall (P:val->Prop) P1,
      entails (ens (fun r => \[P r /\ P1]))
        (ens_ \[P1];; ens (fun r => \[P r]))).
    { introv H. inverts H. applys s_seq; applys s_ens; heaps. }
    rewrite H.
    clear H.

    fsimpl.
    fsimpl.
    fstep. unfold veq, virel. intros.

    applys ent_req_r.
    fsimpl.
    rewrite <- norm_seq_assoc; shiftfree.
    fstep. intros.
    finst a.
    rewrite norm_ens_ens_void_l.
    fstep. xsimpl. intros. split. rewrite H. math.
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
    fsimpl.
    fstep. unfold vgt. simpl. intro.
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

    fsimpl.
    finst n.
    fsimpl. finst acc.

    rewrite norm_req_req.
    fstep. xsimpl.
    applys ent_req_r. fstep. intros.
    simpl.

    pose proof IH as IH1.
    specializes IH (n-1).
    forward IH. unfold virel in H. unfold downto. math.
    specializes IH acc.
    fsimpl.
    simpl.
    rewrite norm_bind_trivial.
    2: admit.
    (* generalised entailment *)
    rewrite IH.
    clear IH.
    (* clear IH. *)

    fsimpl. finst x.
    fsimpl. finst (a+1).
    fsimpl.


    rewrite norm_req_req.

    rewrite norm_ens_req_transpose. 2: { applys b_pts_single. }
    rewrite norm_req_pure_l. 2: { reflexivity. }
    rewrite norm_seq_ens_empty.

    applys ent_req_l. math.
    fintro a1.
    assert (forall H (P:val->Prop),
      entails (ens (fun r => H \* \[P r])) (ens_ H;; ens (fun r => \[P r]))) as ?. admit.
    rewrite H1.
    clear H1.
    fsimpl.

    assert (forall H P f,
      entails (ens_ H;; ens_ \[P];; f)
        (ens_ \[P];; ens_ H;; f)) as ?. admit.

    rewrite H1.
    clear H1.
    fstep. intros.
    fsimpl.

    assert (forall (A:Type) f1 (f2:A->val->flow),
      entails
        (bind f1 (fun r => ∀ x, f2 x r))
        (∀ x, bind f1 (fun r => f2 x r))) as ?. admit.

    rewrite H2.
    clear H2.
    fsimpl. finst a1.

    lets: norm_bind_req (x~~>a1).
    setoid_rewrite H2.
    clear H2.

    assert (forall f f2 H,
      shift_free f ->
      entails (bind f (fun r => req H (f2 r)))
      (req H (bind f f2))) as ?. admit.
    rewrite H2. 2: { shiftfree. }
    clear H2.
    fsimpl.

    rewrite norm_ens_req_transpose. 2: { applys b_pts_single. }
    rewrite norm_req_pure_l. 2: { reflexivity. }
    rewrite norm_seq_ens_empty.

    setoid_rewrite norm_bind_seq_assoc. 2: { shiftfree. }

    assert (forall f1 f2 P,
      entails (bind (ens (fun r => \[P r])) (fun r => f1;; f2 r))
      (f1;; (bind (ens (fun r => \[P r])) f2))) as ?. admit.
    rewrite H2.
    clear H2.
    fsimpl.

    lazymatch goal with
    | |- entails_under ?env _ _ =>
      pose proof (@entails_under_unk env "k" (vbool false))
      (* [ | resolve_fn_in_env ]; simpl *)
    end.
    specializes H2. unfold toss_n_env. resolve_fn_in_env. simpl in H2.
    Fail rewrite H2.
    Fail setoid_rewrite H2.
    clear H2.

    (* assert (forall H, entails (ens H) empty) as ?. admit. *)
    (* assert ("k" = "a") as ?. admit. *)
    (* rewrite H2. *)

    (* assert (forall k v s, entails_under s (unk k v) empty) as ?. admit. *)
    (* setoid_rewrite H2. *)

    (* we have to do this because setoid rewrite doesn't work for some reason *)
    destruct acc.
    {
      case_if. 2: { false C. constructor. }
      fsimpl.
      funfold1 "k".
      fsimpl. finst n.
      fsimpl. finst false.

      specializes IH1 (n-1).
      forward IH1. unfold virel in H. unfold downto. math.
      specializes IH1 false.
      rewrite norm_bind_val.
      simpl in IH1.

      unfold vsub. simpl.
      fsimpl.

      assert (forall f1 f2, entails (bind f1 (fun _ => f2)) (f1;; f2)) as ?. admit.
      rewrite H2.
      rewrite H2.

      rewrite <- norm_seq_assoc. 2: admit.
      assert (forall f, entails
        (ens (fun r => \[r = false]);; f)
        f
      ) as ?. admit.

      specializes H3 (ens (fun r => \[r = false])).

      assert (ShiftFree (unk "toss_n" (n - 1))) as ?. admit.
      rewrite H3.

      rewrite IH1.

      fsimpl. finst x.
      fsimpl. finst (a1 + 1).
      fsimpl.
      rewrite norm_req_req.

      rewrite norm_ens_req_transpose. 2: { applys b_pts_single. }
      rewrite norm_req_pure_l. 2: { reflexivity. }
      rewrite norm_seq_ens_empty.

      fstep. math.
      fintro a2.
      case_if.

      (* rewrite norm_ens_void_hstar_pure_r. *)
      assert (forall H P P1, entails
        (ens (fun r => H \* \[P /\ P1 r]))
        (ens_ \[P];; ens_ H;; ens (fun r => \[P1 r]))
      ) as ?. admit.

      rewrite H5.
      fsimpl.
      fstep. intros.
      finst a2.
      rewrite norm_ens_ens_void_l.
      fstep.
      xsimpl.
      intros.
      split. math.
      Fail math.
      rewrite H7.
      Fail math. (* ????? *)
      rewrite Z.add_0_r.
      reflexivity.
    }
    {

      (* TODO this branch is entirely copy-pasted from the previous one, figure out a way to not do this... *)

      case_if. { false C. constructor. }
      fsimpl.
      funfold1 "k".

      fsimpl. finst n.
      fsimpl. finst false.

      specializes IH1 (n-1).
      forward IH1. unfold virel in H. unfold downto. math.
      specializes IH1 false.
      rewrite norm_bind_val.
      simpl in IH1.

      unfold vsub. simpl.
      fsimpl.

      assert (forall f1 f2, entails (bind f1 (fun _ => f2)) (f1;; f2)) as ?. admit.
      rewrite H2.
      rewrite H2.

      rewrite <- norm_seq_assoc. 2: admit.
      assert (forall f, entails
        (ens (fun r => \[r = false]);; f)
        f
      ) as ?. admit.

      specializes H3 (ens (fun r => \[r = false])).

      assert (ShiftFree (unk "toss_n" (n - 1))) as ?. admit.
      rewrite H3.

      rewrite IH1.

      fsimpl. finst x.
      fsimpl. finst (a1 + 1).
      fsimpl.
      rewrite norm_req_req.

      rewrite norm_ens_req_transpose. 2: { applys b_pts_single. }
      rewrite norm_req_pure_l. 2: { reflexivity. }
      rewrite norm_seq_ens_empty.

      fstep. math.
      fintro a2.
      case_if.

      (* rewrite norm_ens_void_hstar_pure_r. *)
      assert (forall H P P1, entails
        (ens (fun r => H \* \[P /\ P1 r]))
        (ens_ \[P];; ens_ H;; ens (fun r => \[P1 r]))
      ) as ?. admit.

      rewrite H5.
      fsimpl.
      fstep. intros.
      finst a2.
      rewrite norm_ens_ens_void_l.
      fstep.
      xsimpl.
      intros.
      split. math.
      Fail math.
      rewrite H7.
      Fail math. (* ????? *)
      rewrite Z.add_0_r.
      reflexivity.

    }

(* Abort. *)
Admitted.


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

Lemma rearrange_ens : forall H P (P1:val->Prop),
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
  fsimpl.
  applys ent_disj_l.
  {
    (* the defun isn't used *)
    finst "k". { intros. shiftfree. } fleft.
    lazymatch goal with
    | |- entails_under _ _ (empty;; ?f) =>
      rewrite (norm_seq_empty f)
    end.

    (* base case *)
    rewrite <- hstar_pure_post_pure.
    rewrite <- norm_ens_ens_void_l.
    fsimpl.
    case_if. clear C.
    fstep. simpl. intros.
    fintro x.
    fintro a.
    apply ent_req_r.
    finst a.
    rewrite norm_ens_ens_void_l.
    fstep. xsimpl. simpl. math.
  }
  { fsimpl.
    fstep. simpl. intros.

    unfold toss.
    rewrite red_init.
    rewrite red_extend.
    rewrite red_extend.
    rewrite red_rs_sh_elim.

    fintro k. finst k. { shiftfree. }
    (* recursive case; use the defun *)
    fright. applys ent_seq_defun_both.

    fintro x. finst x.
    fintro a. finst a.

    funfold1 k.
    lazymatch goal with
    | |- entails_under ?e _ _ => remember e as env
    end.

    fsimpl.
    fstep. xsimpl.

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

    fsimpl. finst x.
    fsimpl. finst (a+1).
    fsimpl.
    rewrite norm_req_req.

    rewrite norm_ens_req_transpose. 2: { apply b_pts_single. }
    rewrite norm_req_pure_l. 2: { reflexivity. }
    rewrite norm_seq_ens_empty.

    fstep. math.
    fsimpl. fintro b.
    rewrite rearrange_ens.
    fsimpl.

    apply ent_seq_ens_void_pure_l. intros.

    case_if. 2: { false* C. }

    fsimpl. finst b.

    subst.
    funfold1 k.
    lazymatch goal with
    | |- entails_under ?e _ _ => remember e as env
    end.

    fsimpl.

    rewrite norm_ens_req_transpose. 2: { apply b_pts_single. }
    rewrite norm_req_pure_l. 2: { reflexivity. }
    rewrite norm_seq_ens_empty.
    
    unfolds in lemma_weaker.
    rewrite lemma_weaker.
    fold lemma_weaker2 in lemma_weaker.

    fsimpl. finst x.
    fsimpl. finst (b+1).
    fsimpl.
    rewrite norm_req_req.

    rewrite norm_ens_req_transpose. 2: { apply b_pts_single. }
    rewrite norm_req_pure_l. 2: { reflexivity. }
    rewrite norm_seq_ens_empty.

    fstep. math.
    fintro b1.

    rewrite rearrange_ens.

    fsimpl.
    fstep. intros.
    case_if.
    fsimpl.

    rewrite norm_ens_ens_void_l.
    finst b1.
    fstep. { xsimpl. intros. simpl. split. math. rewrite H2; f_equal. }
  }
Qed.

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
