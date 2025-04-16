
(* From ShiftReset Require Import Logic Automation. *)
From ShiftReset Require Import LogicBind AutomationBind.
Local Open Scope string_scope.

Module Multi.

(* < sh k. let a = k true in let b = k false in a + b > *)
Definition f : ufun := fun _ =>
  rs (
    sh (fun k =>
      bind (unk k (vbool true)) (fun r1 =>
      bind (unk k (vbool false)) (fun r2 =>
        ens (fun r => \[r = vand r1 r2])
      )))).

Lemma f_reduction: forall v1, exists f1,
  entails_under empty_env (f v1) (f1;; ens (fun r => \[r = vbool false])).
Proof.
  intros.
  exists (∃ k, defun k (fun v : val => rs (ens (fun r => \[r = v])))).
  unfold f.
  rewrite red_init.
  rewrite red_rs_sh_elim.
  fintro k.
  finst k. { intros. shiftfree. }
  apply ent_seq_defun.
  funfold1 k.
  rewrites (>> red_rs_elim (ens (fun r => \[r = vbool true]))). { shiftfree. }
  rewrite norm_bind_val.
  funfold1 k.
  (* TODO bad printing *)
  rewrites (>> red_rs_elim (ens (fun r => \[r = vbool false]))). { shiftfree. }
  rewrite norm_bind_val.
  rewrite red_rs_elim. 2: { shiftfree. }
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
    bind (req (x~~>vint a) (ens_ (x~~>vint (a+1));; unk k (vbool true))) (fun r1 =>
      ∀ b, bind (req (x~~>vint b) (ens_ (x~~>vint (b+1));; unk k (vbool false))) (fun r2 =>
        ens (fun r3 => \[r3 = vadd r1 r2])))).

Definition toss_env := Fmap.update empty_env "toss" toss.

(* let foo () = < let v = s () in if v then 1 else 0 > *)
Definition foo : flow :=
  rs (
    bind (unk "toss" vunit) (fun v =>
    ens (fun r1 => \[If v = (vbool true) then r1 = vint 1 else r1 = vint 0]))
  ).

Definition foo_spec : flow :=
  ∀ x a, req (x~~>vint a) (ens (fun r => x~~>vint(a+2) \* \[r=vint 1])).

Theorem foo_summary : exists f,
  entails_under toss_env foo (f;; foo_spec).
Proof.
  intros.
  exists (∃ k,
    defun k (fun v : val => rs (bind (ens (fun r => \[r = v]))
    (fun v => ens (fun r1 => \[If v = (vbool true) then r1 = vint 1 else r1 = vint 0]))))).
  unfold foo, foo_spec.

  funfold1 "toss". unfold toss.
  rewrite red_init.
  rewrite red_extend.
  rewrite red_rs_sh_elim.
  fintro k.
  finst k. { intros. shiftfree. }

  apply ent_seq_defun.
  fintro x. rewrite norm_rs_all. finst x.
  fintro a. rewrite norm_rs_all. finst a.
  funfold1 k.

  rewrite norm_bind_req. 2: { shiftfree. }
  rewrite norm_rs_req.
  apply ent_req_req. xsimpl.

  (* fix printing due to overly-long env *)
  lazymatch goal with
  | |- entails_under ?e _ _ => remember e as env
  end.
  rewrite norm_bind_seq_assoc; shiftfree.

  rewrite norm_bind_val.
  lazymatch goal with
  | |- context[rs (ens ?H)] =>
    rewrites (>> red_rs_elim (ens H))
  end; shiftfree.

  case_if.
  rewrite norm_bind_val.

  rewrite norm_seq_all_reassoc_ctx; shiftfree.
  rewrite norm_rs_all.
  finst (a + 1).

  (* somehow automate this... *)
  subst.
  funfold1 k.
  lazymatch goal with
  | |- entails_under ?e _ _ => remember e as env
  end.

  rewrite norm_bind_val.
  lazymatch goal with
  | |- context[rs (ens ?H)] =>
    rewrites (>> red_rs_elim (ens H))
  end; shiftfree.
  case_if.

  (* lazymatch goal with
  | |- entails_under ?env _ _ =>
    pose proof (@ent_unk env k (vbool false))
    (* [ | resolve_fn_in_env ]; simpl *)
  end.
  specializes H. resolve_fn_in_env. simpl in H. *)

  rewrite norm_bind_req; shiftfree.

  rewrite norm_ens_req_transpose. 2: { applys b_pts_single. }
  rewrite norm_req_pure_l. 2: { reflexivity. }
  rewrite norm_seq_ens_empty.

  rewrite norm_bind_seq_assoc; shiftfree.
  rewrite norm_bind_val.

  rewrite red_rs_elim; shiftfree.
  rewrite norm_ens_ens_void_l.
  apply ent_ens_single.
  xsimpl.
  - intros. f_equal. math.
  - intros. subst. f_equal.
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
Notation veq a b := (virel (fun x y => x = y) a b).
Notation vneq a b := (virel (fun x y => x <> y) a b).
Notation vsub a b := (viop (fun x y => x - y) a b).
Notation vand a b := (vbop (fun x y => x && y) a b).

Coercion vint : Z >-> val.
Coercion vbool : bool >-> val.

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
  req \[vgt n (vint 0)]
    (disj
      (ens_ \[veq n 1];; toss vunit)
      (ens_ \[vneq n 1];;
        bind (toss vunit) (fun r1 =>
        bind (unk "toss" (vsub n 1)) (fun r2 =>
        ens (fun r => \[r = vand r1 r2]))))).

Definition toss_n_env := Fmap.update empty_env "toss" toss.

(* 

Definition foon n r : flow :=
  rs (
    ∃ v, unk "toss" (vint n) (vbool v);;
    ens (fun r1 => \[v = true /\ r1 = vint 1 \/ v = false /\ r1 = vint 0])
  ) (vint r).

Definition foon_spec : flow :=
  ∀ x a n, req (x~~>vint a \* \[n > 0]) (ens (fun r => x~~>vint (a + Z.pow 2 (n+1) - 2) \* \[r = vint 1])).

Lemma lem : forall acc x n r,
  entails
    (rs (∃ v,
      unk "toss" (vint n) (vbool v);;
      ens (fun r1 =>
        \[andb acc v = true /\ r1 = vint 1 \/ andb acc v = false /\ r1 = vint 0])) r)
    (∃ a, req (x~~>vint a \* \[n > 0]) (ens (fun r => x~~>vint (a + Z.pow 2 (n+1) - 2) \* \[acc = true /\ r = vint 1 \/ acc = false /\ r = vint 0]))).
Proof.
Admitted.

Theorem foon_summary : forall n r,
  entails_under toss_env (foon n r) foon_spec.
Proof.
Abort. *)

End Toss.
