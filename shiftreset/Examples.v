
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
    ∀ x a, ∃ r1, req (x~~>vint a) (ens_ (x~~>vint (a+1));; unk "k" (vbool true) (vint r1));;
    ∀ b, ∃ r2, req (x~~>vint b) (ens_ (x~~>vint (b+1));; unk "k" (vbool false) (vint r2));;
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

  (* terrible defun workaround *)
(* defun "k"
  (fun a0 r0 : val =>
rs
  (ens_ \[vbool x = a0];;
(ens (fun r1 => \[r1 = vbool x]));;
(ens (fun r1 => \[x = true /\ r1 = vint 1 \/ x = false /\ r1 = vint 0])))
  r0);; *)
  
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
  2: { shiftfree. }

(* HANLDE THE DEFUN *)

  apply ent_defun_left.
  {
    apply weaken_seq1.
    apply weaken_defun3.
    apply weaken_rs_admitted.
    apply weaken_with.
    (* Unset Printing Notations. Set Printing Coercions. Set Printing Parentheses. *)
    apply weaken_all. intros.
    apply weaken_all. intros.
    apply weaken_ex. intros.
    apply weaken_seq.
    apply weaken_req.
    unfold ens_. apply weaken_seq.
    apply weaken_ens.
    admit.
    apply weaken_all. intros.
    apply weaken_ex. intros.
    apply weaken_seq.
    apply weaken_req.
    unfold ens_. apply weaken_seq.
    apply weaken_ens.
    admit.
    apply weaken_ens.

    (* apply weaken_ *)
    (* unfold can_weaken_env. *)
    (* admit. *)
    (* admit. *)
  (* unfold can_weaken_env.
  intros.
  admit. *)
  }
  {
  unfold can_strengthen_env.
  intros.
  apply s_req. intros.
  inverts H as H. specializes H H0 H1 H2.
  lets: ens_inv H.
  (* Search (union _ _ = union _ _) in Fmap. *)
  unfold Fmap.update in H3.
  assert (Fmap.disjoint s1 (Fmap.single x1 u)) as ?. admit.
  assert (Fmap.disjoint s2 (Fmap.single x1 u)) as ?. admit.
  lets: union_eq_inv_of_disjoint.
  setoid_rewrite union_comm_of_disjoint in H3.
  specializes H6 H4 H5 H3.
  subst.
  (* clear H3 H4 H5. *)

  inverts H as H. destr H.
  apply s_ens.
  exs. splits*.

  fmap_disjoint.
  fmap_disjoint.
  }
  

(* PREVIOUS ATTEMPT TRYING TO ADD DISCARD *)

  (* apply ent_discard_intro1.
  Check ent_discard_intro1. *)

  (* Check ent_seq_defun.
  Fail apply ent_seq_defun.
  Check ent_seq_defun_discard. *)

pose proof ent_seq_defun_discard.
specializes H
(req (x0 ~~> vint a) (ens (fun r0 => x0 ~~> vint (a + 2) \* \[r0 = vint 1]))).
  rewrite <- H.
  (* 2: { 
    (* Search shift_free. *)
    Check sf_req.
    apply sf_req.

  } *)
clear H.

  apply ent_seq_defun.
  Search (rs _ _).
  Search (rs (fall _) _).

  (* funfold1 "k". unfold k. *)
  Check ent_unk.
  

  (* funfold1 "k". *)
  (* unfold k. *)

  (* simpl. *)
  (* [ | unfold env; resolve_fn_in_env ] *)

  rewrite norm_rs_all. finst x0.
  rewrite norm_rs_all. finst a.
  rewrite norm_rs_ex. fintro r1.

Check norm_reassoc.
  rewrite norm_reassoc.
  rewrite <- norm_seq_assoc.
  (* cannot rewrite on the right of a seq, so need to untangle the discard first *)

  (* apply s_discard. *)

  pose proof (
    @ent_unk
(    Fmap.update s_env "k"
    (fun a0 r0 : val =>
    rs
    (ens_ \[vbool x = a0];;
    (ens (fun r2 => \[r2 = vbool x]));;
    (ens (fun r2 => \[x = true /\ r2 = vint 1 \/ x = false /\ r2 = vint 0]))) r0)
    )
    
    "k" (vbool true) (vint r1)).

  rewrite H.
  



  (* funfold1 "k". *)

(* finst x0. *)
  (* fintro x0. fintro a.
  funfold1 "s". unfold s. *)

  (* apply ent_discard. *)

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