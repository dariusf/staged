
(* From ShiftReset Require Import Logic Automation. *)
From ShiftReset Require Import LogicBind AutomationBind.
Local Open Scope string_scope.

(* TODO *)
Lemma norm_bind_all_l : forall (A:Type) fk1 fk,
  entails (bind (∀ (x:A), fk1 x) fk) (∀ (x:A), bind (fk1 x) fk).
Proof.
Admitted.

(* Lemma norm_bind_all_r : forall (A:Type) f fk,
  entails (bind f (fun r => ∀ (x:A), fk r)) (∀ (x:A), bind f fk).
Proof.
Admitted. *)

Lemma norm_bind_ex_l : forall (A:Type) fk1 fk,
  entails (bind (∃ (x:A), fk1 x) fk) (∃ (x:A), bind (fk1 x) fk).
Proof.
Admitted.

(* Lemma norm_bind_ex_r : forall (A:Type) f fk,
  entails (bind f (fun r => ∃ (x:A), fk r)) (∃ (x:A), bind f fk).
Proof.
Admitted. *)

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
      (ens_ \[vgt n 0];;
        bind (toss vunit) (fun r1 =>
        bind (unk "toss_n" (vsub n 1)) (fun r2 =>
        ens (fun r => \[r = vand r1 r2]))))).

Definition toss_n_env :=
(* Fmap.update *)
  (Fmap.update empty_env "toss_n" toss_n)
  (* "k"
(fun v => ∀ n, rs (bind (bind (ens (fun r => \[r = v])) (fun r1 => bind (unk "toss_n" (viop (fun x y => x - y) n 1)) (fun r2 => ens (fun r => \[r = vbop (fun x y => x && y) r1 r2])))) (fun v0 => ens (fun r => \[If v0 = true then r = 1 else r = 0])))) *)
.

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


(* acc  *)
Lemma lemma_weaker2 : forall (acc:bool) (n:int),
  entails

    (rs (bind
      (bind (unk "toss_n" n) (fun r2 =>
        ens (fun r => \[r = vbop (fun x y => x && y) acc r2])))
      (fun v => ens (fun r => \[If v = true then r = 1 else r = 0]))))

    (∀ x a, req (x~~>vint a \* \[n >= 0])
      (∃ b, ens (fun r => x~~>vint b \*
        (* \[b > a+n /\ (r=1 \/ r=0)]))). *)
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

Ltac fleft := first [ apply ent_seq_disj_r_l | apply ent_disj_r_l ].
Ltac fright := first [ apply ent_seq_disj_r_r | apply ent_disj_r_l ].

Theorem main_summary : forall n,
exists f,
  entails_under toss_n_env (main n) (f;; main_spec_weaker n).
  (* entails_under toss_n_env (main n) (main_spec_weaker n). *)
Proof.
  (* intros n. *)
  unfold main_spec_weaker, main. intros.

  exists (∃ k, disj empty (defun k (fun v =>
    rs (bind (bind (ens (fun r => \[r = v])) (fun r1 => bind (unk "toss_n" (viop (fun x y => x - y) n 1)) (fun r2 => ens (fun r => \[r = vbop (fun x y : bool => x && y) r1 r2])))) (fun v0 => ens (fun r => \[If v0 = true then r = 1 else r = 0])))))).

  (* unfold toss_n_env. *)

  (* lazymatch goal with
  | |- entails_under ?env _ _ =>
    pose proof (@entails_under_unk env "toss_n" n)
    (* [ | resolve_fn_in_env ]; simpl *)
  end.
  specializes H. unfold toss_n_env.
  
  (* TODO fix the unfolding tactic *)
  (* resolve_fn_in_env. *)
  unfold Fmap.update.
  rewrite Fmap.read_union_r.
  rewrite Fmap.read_union_l.
  apply Fmap.read_single.
  apply Fmap.indom_single.
  solve_trivial_not_indom.

  simpl in H. rewrite H. clear H. *)

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
    fstep. unfold veq. intros.
    fintro x.
    fintro a.
    apply ent_req_r.
    finst a.
    rewrite norm_ens_ens_void_l.
    fstep. xsimpl. math.
  }
  {

    fsimpl.
    fstep. unfold vgt. intros.

    unfold toss.
    rewrite red_init.
    rewrite red_extend.
    rewrite red_extend.
    rewrite red_rs_sh_elim.

    fintro k. finst k. { shiftfree. }
    fright. applys ent_seq_defun_both.


    fintro x. finst x.
    fintro a. finst a.

    funfold1 k.
    lazymatch goal with
    | |- entails_under ?e _ _ => remember e as env
    end.

    fsimpl.
    fstep. xsimpl.

    (* finst x. *)
    (* fintro x1. *)
    (* finst x. *)
    rewrite lemma_weaker2.

    (* rewrite norm_bind_all_l.
    rewrite norm_rs_all.
    rewrite norm_seq_all_r. *)
    fsimpl. finst x.
    fsimpl. finst (a+1).
    fsimpl.
    rewrite norm_req_req.

    (* rewrite norm_ens_req_transpose. 2: {
      (* rewrite *)
      (* Search (_ \* \[]). *)
      (* rewrite <- (hstar_hempty_r (x~~>(a+1))) at 1.
      apply b_pts_match.
      apply b_base_empty. *)
      } *)

    rewrite norm_ens_req_transpose. 2: { apply b_pts_single. }
    rewrite norm_req_pure_l. 2: { reflexivity. }
    rewrite norm_seq_ens_empty.

    (* fsimpl. *)
    (* Search (entails_under _ (req \[_] _) _). *)
    fstep. math.
    fsimpl. fintro b.
    (* fsimpl. *)
    (* rewrite <- norm_ens_ens_void. *)
    (* Search (ens). *)

assert (forall H P (P1:val->Prop),
  entails (ens (fun r => H \* \[P /\ P1 r]))
  (ens_ \[P];; ens_ H;; ens (fun r => \[P1 r]))).
  admit.
  rewrite H0.
  clear H0.

  fsimpl.
  assert (forall H P, entails (ens_ H;; ens_ \[P]) (ens_ \[P];; ens_ H)) as ?. admit.
  (* rewrite norm_seq_assoc; shiftfree.
  rewrite H0.
  rewrite <- norm_seq_assoc; shiftfree. *)
  clear H0.

  assert ( forall s P f1 f2,
    (P -> entails_under s f1 f2) ->
    entails_under s (ens_ \[P];; f1) f2
  ) as ?. admit.

  apply H0. intros.
  clear H0.

  case_if. 2: { false* C. }

  (* fsimpl. *)
  (* rewrite norm_bind_disj_val. *)
  fsimpl.

  assert (forall f1 f2 f3,
    entails (f1;; disj f2 f3)
    (disj (f1;; f2) (f1;; f3))
  ) as ?. admit.
  (* rewrite H0. *)
  clear H0.

  (* apply ent_seq_disj_l. *)

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

    
    rewrite lemma_weaker2.
    fsimpl. finst x.
    fsimpl. finst (b+1).
    fsimpl.
    rewrite norm_req_req.

    rewrite norm_ens_req_transpose. 2: { apply b_pts_single. }
    rewrite norm_req_pure_l. 2: { reflexivity. }
    rewrite norm_seq_ens_empty.

    fstep. math.
    fintro b1.

(* this occurs twice *)
assert (forall H P (P1:val->Prop),
  entails (ens (fun r => H \* \[P /\ P1 r]))
  (ens_ \[P];; ens_ H;; ens (fun r => \[P1 r]))).
  admit.
  rewrite H0.
  clear H0.

  fsimpl.
  fstep. intros.
  case_if.
  fsimpl.

  (* Search (ens_ _;; ens _). *)
  rewrite norm_ens_ens_void_l.
  finst b1.
  fstep.
  xsimpl.
  intros.
  split.
  math.
  rewrite H2; f_equal.

  

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

Theorem main_summary : forall n,
  entails_under toss_env (main n) main_spec.
Proof.
Abort.

End Toss.
