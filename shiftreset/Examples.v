
(* From ShiftReset Require Import Logic Automation. *)
From ShiftReset Require Import LogicBind AutomationBind.
Local Open Scope string_scope.

(* TODO move upstream *)
Lemma norm_bind_disj: forall f1 f2 fk,
  entails (bind (disj f1 f2) fk) (disj (bind f1 fk) (bind f2 fk)).
Proof.
  unfold entails. intros.
  inverts H.
  { inverts H7.
    - applys s_disj_l. applys* s_bind.
    - applys s_disj_r. applys* s_bind. }
  {
    inverts H6.
    - applys s_disj_l. applys* s_bind_sh.
    - applys s_disj_r. applys* s_bind_sh. }
Qed.

(* Lemma norm_rs_ens_void: forall f1 f2 fk,
  entails (rs (ens_ H)) (disj (bind f1 fk) (bind f2 fk)).
Proof.
  unfold entails. intros.
  inverts H.
  { inverts H7.
    - applys s_disj_l. applys* s_bind.
    - applys s_disj_r. applys* s_bind. }
  {
    inverts H6.
    - applys s_disj_l. applys* s_bind_sh.
    - applys s_disj_r. applys* s_bind_sh. }
Qed. *)

Lemma norm_rs_disj: forall f1 f2,
  entails (rs (disj f1 f2)) (disj (rs f1) (rs f2)).
Proof.
  applys red_rs_float2.
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

Notation vgt a b := (virel (fun x y => x > y) a b).
Notation vlt a b := (virel (fun x y => x < y) a b).
Notation vge a b := (virel (fun x y => x >= y) a b).
Notation vle a b := (virel (fun x y => x <= y) a b).
Notation veq a b := (virel (fun x y => x = y) a b).
Notation vneq a b := (virel (fun x y => x <> y) a b).
Notation vsub a b := (viop (fun x y => x - y) a b).
Notation vand a b := (vbop (fun x y => x && y) a b).

Coercion vint : Z >-> val.
Coercion vbool : bool >-> val.

Create HintDb staged_norm.
Global Hint Rewrite
  (* move universal quantifiers on the left outwards *)
  norm_rs_all norm_req_all norm_seq_all_r
  (* associate things out of binds *)
  norm_bind_req norm_bind_seq_assoc norm_bind_disj
  (* associate things out of resets *)
  norm_rs_req norm_rs_disj red_rs_float1
  (* eliminate trivial resets and binds *)
  red_rs_ens norm_bind_val

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
  apply ent_seq_ens_void_l |
  apply ent_ens_single |
  apply ent_req_req
].

Module Multi.

(* < sh k. let a = k true in let b = k false in a + b > *)
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
  apply ent_seq_defun.
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

(* let s() =
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

(* let foo () = < let v = s () in if v then 1 else 0 > *)
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

  apply ent_seq_defun.
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
    pose proof (@ent_unk env k (vbool false))
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
  if n = 1 then
    toss ()
  else
    let r1 = toss () in
    let r2 = toss_n (n - 1) in
    r1 && r2

*)
Definition toss_n : ufun := fun (n:val) =>
  (* req \[vgt n (vint 0)] *)
    (disj
      (ens (fun r => \[r = true /\ veq n 0]))
      (ens_ \[vneq n 0];;
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
      (∃ b, ens (fun r => x~~>b \* \[vgt b (vadd a n) /\ r = 1])).

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
(* Abort. *)
Admitted.


Lemma norm_bind_assoc: forall f fk fk1,
  shift_free f ->
  (forall v, shift_free (fk v)) ->
  entails (bind (bind f fk) fk1)
    (bind f (fun r => bind (fk r) fk1)).
Proof.    
  unfold entails. intros * Hsf Hsfk * H.
  inverts H. 2: { inverts H6. false Hsfk H8. false Hsf H4. }
  inverts H7.
  applys s_bind H6.
  applys* s_bind H9.
Qed.

Theorem main_summary : forall n,
(* exists f, *)
  (* entails_under toss_n_env (main n) (f;; main_spec_weaker n). *)
  entails_under toss_n_env (main n) (main_spec_weaker n).
Proof.
  (* intros n. *)
  unfold main_spec_weaker, main. intros.

  (* unfold toss_n_env. *)

  (* lazymatch goal with
  | |- entails_under ?env _ _ =>
    pose proof (@ent_unk env "toss_n" n)
    (* [ | resolve_fn_in_env ]; simpl *)
  end.
  specializes H. unfold toss_n_env. resolve_fn_in_env. simpl in H.
  rewrite H.
  unfold toss_n. *)

  funfold1 "toss_n". unfold toss_n.
  fsimpl.
  applys ent_disj_l.
  {
    (* base case *)
    rewrite <- hstar_pure_post_pure.
    rewrite <- norm_ens_ens_void_l.
    fsimpl.
    fstep. intros.
    case_if. clear C.
    unfold veq in H.
    fintro x.
    fintro a.
    apply ent_req_r.
    finst a.
    rewrite norm_ens_ens_void_l.
    fstep. xsimpl.
    simpl.
    math.
  }
  {
    pose proof lemma_weaker.
    (* rewrite H. *)

    (* TODO toss and n aren't shift free *)
    (* fsimpl.
    fstep. intros. *)


    unfold toss.
    (* rewrite red_init. *)
    (* rewrite red_extend. *)
    (* rewrite red_extend. *)
    (* rewrite red_rs_sh_elim. *)

    (* TODO defun problem *)
    (* TODO reduce and unfold everything *)
    (* TODO rewrite after unfolding unk *)


    (* (forall f fk fk1,
      entails (bind (bind f fk1) fk)
        (bind f (fun r => bind (fk1 r) fk))
    ) *)
    (* Search (bind (bind _ _) _). *)


    (* START TRYING TO REWRITE WITH THE LEMMA *)

    (* assert 
    (forall f fk fk1,
      entails (bind (bind f fk1) fk)
        (bind f (fun r => bind (fk1 r) fk))
    )
     as ?. admit.
    rewrite H1.

    assert (forall f fk1 fk2,
      entails
        (bind (bind f fk1) fk2)
        (bind f (fun v => bind (fk1 v) fk2))
    ) as ?. admit.

    specializes H2
      (unk "toss_n" (viop (fun x y : int => x - y) n 1))
      (* (ens (fun r0 => \[r0 = vbop (fun x y : bool => x && y) r r2]))
      (ens (fun r0 => \[If v = true then r0 = 1 else r0 = 0])) *)
      . *)

    (* rewrite H2. *)



    admit.
    admit.
    admit.
  }

  (* exists (∃ k, (defun k (fun a =>
    rs (bind (ens (fun r : val => \[r = a]))
      (fun v => ens (fun r => \[If v = true then r = 1 else r = 0])))))). *)

  (* fintro n. finst n. *)
  (* funfold1 "toss". unfold toss.
  rewrite red_init.
  rewrite red_extend.
  rewrite red_rs_sh_elim.
  fintro k.
  finst k. { intros. shiftfree. }
  apply ent_seq_defun.
  lazymatch goal with
  | |- entails_under ?e _ _ => remember e as env
  end.
  fintro x.
  fintro a.
  finst x.
  finst a.

  subst.
  funfold1 k.
  lazymatch goal with
  | |- entails_under ?e _ _ => remember e as env
  end.

  fsimpl; shiftfree.

  (* rewrite norm_bind_req; shiftfree.
  rewrite norm_bind_val.
  rewrite red_rs_ens. *)
  case_if.
  fsimpl.
  (* rewrite norm_bind_seq_assoc; shiftfree.
  rewrite norm_bind_val.

  (* finst does not work contextually *)
  rewrite norm_seq_all_r; shiftfree. *)
  (* rewrite norm_req_all. *)
  finst (a+1).

  subst.
  funfold1 k.
  lazymatch goal with
  | |- entails_under ?e _ _ => remember e as env
  end.

  fsimpl.
  rewrite norm_ens_req_transpose. 2: { apply b_pts_single. }
  rewrite norm_req_pure_l. 2: { reflexivity. }
  rewrite norm_seq_ens_empty.

(* Search (req _ (∀ _, _)). *)
  (* finst b. *)


  case_if.

  fsimpl.
  (* rewrite red_rs_elim. *)
  rewrite norm_req_req.
  apply ent_req_req. xsimpl.
  (* rewrite norm_req_pure_l.
  2: {

  } *)
  Search (req \[_] _).
  (* fassume. *)
  (* applys entails_req.
  2: { xsimpl. }
  2: {

  } *)
  
  Search (entails (ens_ _;; _) (ens_ _ ;; _)).
  Search (entails_under _ (req _ _) (req _ _)). *)
  (* rewrite norm_req_single. *)

  (* 2: { . } shiftfree. *)


  (* rewrite norm_bind_val. *)
  (* rewrite norm_bind_ens. *)

  (* Search (rs (∀ _, _)). *)
  (* finst x. *)
  

(* Close Scope flow_scope. *)
(* Unset Printing Notations. Set Printing Coercions. Set Printing Parentheses. *)
  (* rewrite norm_seq_ex_l. *)
  (* Search (entails_under _ _ ((∃ _, _);; _)). *)
  (* rewrite norm_seq_assoc *)

Abort.

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

Theorem main_summary : forall n,
  entails_under toss_env (main n) main_spec.
Proof.
Abort.

End Toss.
