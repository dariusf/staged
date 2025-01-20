
From ShiftReset Require Import Logic Automation.
Local Open Scope string_scope.

Module Toss.

(* let s() =
  shift k.
    x := !x+1;
    let r1 = k true in
    x := !x+1;
    let r2 = k false in
    r1 + r2
*)
Definition s : ufun := fun _ r =>
  (* ∀ k, *)
  sh "k" (
    ∀ x a r1, req (x~~>vint a) (ens_ (x~~>vint (a+1));; unk "k" (vbool true) (vint r1));;
    ∀ b r2, req (x~~>vint b) (ens_ (x~~>vint (b+1));; unk "k" (vbool false) (vint r2));;
    ens (fun r3 => \[r3 = (vint (r1 + r2))])) r.

Definition s_env := Fmap.update empty_env "s" s.

(* let foo () = < let v = s () in if v then 1 else 0 > *)
Definition foo r : flow :=
  rs (
    ∃ v, unk "s" vunit (vbool v);;
    ens (fun r1 => \[v = true /\ r1 = vint 1 \/ v = false /\ r1 = vint 0])
  ) (vint r).

Definition foo_spec : flow :=
  ∀ x a,
  (* ∃ (uf:val->val->flow), defun "k" uf;; *)
  req (x~~>vint a) (ens (fun r => x~~>vint(a+2) \* \[r=vint 1])).

Theorem foo_summary : forall r,
  entails_under s_env (foo r) foo_spec.
Proof.
  intros.
  unfold foo_spec.
  unfold foo.
  rewrite norm_rs_ex. fintro x.
  fintro x0. fintro a.
  funfold1 "s". unfold s.
  rewrite red_init.
  rewrite red_extend.
  rewrite red_shift_elim.

  (* apply ent_discard_intro1.
  Check ent_discard_intro1. *)

simpl.

Check ent_seq_defun.
  Fail apply ent_seq_defun.
  admit.
Abort.

Definition toss : ufun := fun n' r' =>
  ∃ n r, ens_ \[vint n = n' /\ vint r = r'];;
  req \[n > 0]
    (disj
      (ens_ \[n = 1];; s vunit (vint r))
      (ens_ \[n <> 1];;
        ∃ r1 r2, s vunit (vbool r1);;
        unk "toss" (vint (n-1)) (vbool r2);;
        ens (fun r => \[r = vbool (andb r1 r2)]))).

Definition toss_env := Fmap.update empty_env "toss" toss.

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
Abort.

End Toss.