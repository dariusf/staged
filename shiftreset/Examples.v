
(* From ShiftReset Require Import Logic Automation. *)
From ShiftReset Require Import LogicBind AutomationBind.
Local Open Scope string_scope.

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
Definition vand a b := vbop (fun x y => vbool (x && y)) a b.

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
  (* norm_bind_all_r norm_bind_ex_r *)
  norm_rs_all norm_seq_all_r
  norm_rs_ex

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
    sh (fun k =>
      bind (unk k true) (fun r1 =>
      bind (unk k false) (fun r2 =>
        ens (fun r => \[r = vand r1 r2])
      )))).

Lemma f_reduction: forall v1, exists f1,
  entails_under empty_env (f v1) (f1;; ens (fun r => \[r = false])).
Proof.
  intros.
  exists (∃ k, defun k (fun v : val => rs (ens (fun r => \[r = v])))).
  unfold f.
  rewrite red_init.
  rewrite red_rs_sh_elim.
  fintro k. finst k. { intros. shiftfree. }
  apply ent_seq_defun_both.
  funfold1 k.
  fsimpl.
  funfold1 k.
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
  sh (fun k => ∀ x a,
    bind (req (x~~>vint a) (ens_ (x~~>(a+1));; unk k true)) (fun r1 =>
      ∀ b, bind (req (x~~>vint b) (ens_ (x~~>(b+1));; unk k false)) (fun r2 =>
        ens (fun r3 => \[r3 = vadd r1 r2])))).

Definition toss_env := Fmap.update empty_env "toss" toss.

(* let foo () = < let v = toss () in if v then 1 else 0 > *)
Definition foo : flow :=
  rs (
    bind (unk "toss" vunit) (fun v =>
    ens (fun r1 => \[If v = true then r1 = 1 else r1 = 0]))
  ).

Definition foo_spec : flow :=
  ∀ x a, req (x~~>vint a) (ens (fun r => x~~>(a+2) \* \[r=1])).

Theorem foo_summary : exists f,
  entails_under toss_env foo (f;; foo_spec).
Proof.
  intros.
  exists (∃ k,
    defun k (fun v : val => rs (bind (ens (fun r => \[r = v]))
    (fun v => ens (fun r1 => \[If v = true then r1 = 1 else r1 = 0]))))).
  unfold foo, foo_spec.

  funfold1 "toss". unfold toss.
  rewrite red_init.
  rewrite red_extend.
  rewrite red_rs_sh_elim.
  fintro k. finst k. { intros. shiftfree. }

  apply ent_seq_defun_both.
  fintro x. finst x.
  fintro a. finst a.
  funfold1 k.

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
  funfold1 k.
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

Definition toss_n_env := Fmap.update empty_env "toss_n" toss_n.

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


Lemma lemma_weaker2_under : forall (n:int) (acc:bool),
  entails_under toss_n_env

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
Admitted.

Lemma lemma_weaker2_attempt : exists f, forall (n:int) (acc:bool),
  entails_under toss_n_env

    (rs (bind
      (bind (unk "toss_n" n) (fun r2 =>
        ens (fun r => \[r = vand acc r2])))
      (fun v => ens (fun r => \[If v = true then r = 1 else r = 0]))))

    (f;; ∀ x a, req (x~~>vint a \* \[n >= 0])
      (∃ b, ens (fun r => x~~>vint b \*
        (* \[b > a+n /\ (r=1 \/ r=0)]))). *)
        \[b >= a+n /\ (If acc = true then r = 1 else r = 0)]))).
        (* \[b > a+n /\ (acc = true /\ r = 1 \/ acc = false /\ r = 0)]))). *)
Proof.
  exists (disj empty (∃ n acc, ∃ k, defun k (fun v => rs (bind (bind (bind (ens (fun r => \[r = v])) (fun r1 => bind (unk "toss_n" (viop (fun x y : int => x - y) n 1)) (fun r2 => ens (fun r => \[r = vand r1 r2])))) (fun r2 => ens (fun r => \[r = match r2 with | vbool b1 => acc && b1 | _ => vunit end]))) (fun v0 => ens (fun r => \[If v0 = true then r = 1 else r = 0])))))).

  intros n. induction_wf IH: (downto 0) n. intros.

  funfold1 "toss_n". unfold toss_n.
  fsimpl.
  applys ent_disj_l.
  {

    fleft.
    lazymatch goal with
    | |- entails_under _ _ (empty;; ?f) =>
      rewrite (norm_seq_empty f)
    end.

    fintro x. fintro a.

    (* base case *)
    assert (forall (P:val->Prop) P1,
      entails (ens (fun r => \[P r /\ P1]))
        (ens_ \[P1];; ens (fun r => \[P r]))).
    { introv H. inverts H. applys s_seq; applys s_ens; heaps. }
    rewrite H.
    clear H.

    fsimpl.
    fstep. unfold veq. intros.
    applys ent_req_r.
    rewrite norm_ens_ens_void.
    rewrite norm_seq_ens_ens_pure.
    rewrite <- norm_seq_assoc; shiftfree.
    fstep. intros.
    finst a.
    rewrite norm_ens_ens_void_l.
    fstep. xsimpl. intros. split. rewrite H. math.
    destruct acc.
    - case_if.
      { case_if. assumption. simpl in C0. false. }
      { specializes C. constructor. false. }
    - case_if.
      { specializes C. constructor. false. }
      { case_if. assumption. }
  }
  { fright.

    (* recursive case *)
    fsimpl.
    fstep. unfold vgt. intro.
    unfold toss.
    rewrite red_init.
    rewrite red_extend.
    rewrite red_extend.
    rewrite red_extend.
    rewrite red_rs_sh_elim.

    fintro k.
    finst n; shiftfree. finst acc; shiftfree.

    finst k. { intros. shiftfree. }
    applys ent_seq_defun_both.

    lazymatch goal with
    | |- entails_under ?e _ _ => remember e as env
    end.

    fintro x. fintro a.
    finst x. finst a.

    subst.
    funfold1 k.
    lazymatch goal with
    | |- entails_under ?e _ _ => remember e as env
    end.

    fsimpl.

    rewrite norm_req_req.
    fstep. xsimpl.
    applys ent_req_r. fstep. intros.

    fsimpl.

    (* rewrites (>> IH (n-1)). *)
    pose proof IH as IH1.
    specializes IH1 (n-1).

    assert (forall a, vand true a = a) as ?. admit.
    (* rewrite H1. *)
    unfold vand.
    (* destru *)
    (* rewrite norm_bind_assoc. *)
    (* fsimpl. *)
    (* rewrite norm_bind_val. *)
    (* setoid_rewrite norm_bind_val. *)
    (* rewrite IH1. *)

    (* applys rs. *)


  (* lazymatch goal with
  | |- entails_under ?env _ _ =>
    pose proof (@entails_under_unk env k false)
    (* [ | resolve_fn_in_env ]; simpl *)
  end.
  subst env.
  specializes H0.
  resolve_fn_in_env. simpl in H. *)

    admit.
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
