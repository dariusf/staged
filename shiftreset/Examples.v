
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
Definition s : ufun := fun _ =>
  sh (fun k => ∀ x a,
    bind (req (x~~>vint a) (ens_ (x~~>vint (a+1));; unk k (vbool true))) (fun r1 =>
      ∀ b, bind (req (x~~>vint b) (ens_ (x~~>vint (b+1));; unk k (vbool false))) (fun r2 =>
        ens (fun r3 => \[r3 = vadd r1 r2])))).

Definition s_env := Fmap.update empty_env "s" s.

(* let foo () = < let v = s () in if v then 1 else 0 > *)
Definition foo : flow :=
  rs (
    bind (unk "s" vunit) (fun v =>
    ens (fun r1 => \[If v = (vbool true) then r1 = vint 1 else r1 = vint 0]))
  ).
(* v = vbool true /\ r1 = vint 1 \/ v = vbool false /\ r1 = vint 0 *)

Definition foo_spec : flow :=
  ∀ x a, req (x~~>vint a) (ens (fun r => x~~>vint(a+2) \* \[r=vint 1])).


Lemma norm_bind_seq : forall fk f1 f2,
  entails (bind (f1;; f2) fk) (f1;; bind f2 fk).
Admitted.

Lemma norm_bind_ens_void : forall fk H,
  entails (bind (ens_ H) fk) (seq (ens_ H) (fk vunit)).
Proof.
  unfold entails. intros * H.
  inverts H.
  { pose proof H8.
    inverts H8. destr H7. hinv H2. hinv H2. injects H1. subst.
    applys* s_seq. }
  { false sf_ens_ H7. }
Qed.

Lemma norm_bind_req : forall f fk H,
  shift_free f ->
  entails (bind (req H f) fk) (req H (bind f fk)).
Proof.
  unfold entails. intros * Hsf * H.
  applys s_req. intros.
  inverts H.
  2: { inverts H10. specializes H11 H1 H2 H3. false Hsf H11. }
  { inverts H11. specializes H10 H1 H2 H3.
    applys* s_bind. }
Qed.

Lemma ent_req_req : forall f1 f2 H1 H2 env,
  H2 ==> H1 ->
  entails_under env f1 f2 ->
  entails_under env (req H1 f1) (req H2 f2).
Proof.
  unfold entails_under. intros.
  constructor. intros.
  inverts H3. specializes H14 H6; auto.
Qed.

Theorem foo_summary : exists f,
  entails_under s_env foo (f;; foo_spec).
Proof.
  intros.
  exists (∃ k,
    defun k (fun v : val => rs (bind (ens (fun r => \[r = v]))
    (fun v => ens (fun r1 => \[If v = (vbool true) then r1 = vint 1 else r1 = vint 0]))))).
  unfold foo, foo_spec.

  funfold1 "s". unfold s.
  rewrite red_init.
  rewrite red_extend.
  rewrite red_rs_sh_elim.
  fintro k.
  finst k. { intros. shiftfree. }

  apply ent_seq_defun.
  fintro x. rewrite norm_rs_all. finst x.
  fintro a. rewrite norm_rs_all. finst a.

(* Unset Printing Notations. Set Printing Coercions. Set Printing Parentheses. *)

  (* rewrite norm_reassoc. *)
  (* fintro b. rewrite norm_rs_all. finst b. *)
  (* rewrite norm_rs_ex. fintro r1. *)
  funfold1 k.

  rewrite norm_bind_req. 2: { shiftfree. }
  rewrite norm_rs_req.
  apply ent_req_req. xsimpl.

  (* fix printing due to overly-long env *)
  lazymatch goal with
  | |- entails_under ?e _ _ => remember e as env
  end.
  (* rewrite norm_bind_ens. *)
  rewrite norm_bind_seq.

  rewrite norm_bind_val.
  lazymatch goal with
  | |- context[rs (ens ?H)] =>
    rewrites (>> red_rs_elim (ens H))
  end; shiftfree.

  case_if.
  rewrite norm_bind_val.



Search (bind (_ ;; _) _).


  Search (entails_under _ _ (req _ _)).

  (* lazymatch goal with
  | |- entails_under ?env _ _ =>
    pose proof (@ent_unk env k (vbool true))
    (* [ | resolve_fn_in_env ]; simpl *)
  end.
  specializes H. resolve_fn_in_env. simpl in H. *)

(* Close Scope flow_scope. *)
(* Unset Printing Notations. Set Printing Coercions. Set Printing Parentheses. *)
(* Set Typeclasses Debug. *)
  (* rewrite H. *)
  (* Fail setoid_rewrite H. *)


  (* assert (x=(1%nat)) as ?. admit. *)
  (* assert (k="a") as ?. admit. *)
  (* rewrite H. *)

  (* lazymatch goal with
  | |- entails_under ?env _ _ =>
    setoid_rewrite (@ent_unk env k); [ | try unfold env; resolve_fn_in_env ]; simpl
  end. *)

  (* rewrite norm_rs_req.
  apply ent_req_r.
  rewrite norm_ens_req_transpose. 2: { apply b_pts_single. }
  rewrite norm_req_pure_l. 2: { reflexivity. }
  rewrite norm_seq_ens_empty.
  funfold1 k.
  rewrite norm_bind_val.
  match goal with
  | |- context[ens ?H] =>
    rewrites (>> rs_elim (ens H))
  end.
  shiftfree.
  rewrite <- norm_seq_assoc; shiftfree.
  rewrite norm_rs_seq_ens_void.
  rewrite norm_rs_seq_ens.
  rewrite norm_rs_all.
  rewrite <- norm_ens_ens_void_swap.
  fassume v. intros H.
  rewrite norm_seq_all_reassoc_ctx. 2: { shiftfree. }
  finst (a + 1).
  rewrite norm_rs_ex.
  rewrite norm_seq_ex_reassoc_ctx. 2: { shiftfree. }
  fintro x0.
  rewrite norm_reassoc.
  rewrite norm_rs_req.
  rewrite norm_ens_req_transpose. 2: { apply b_pts_single. }
  rewrite norm_req_pure_l. 2: { congruence. }
  rewrite norm_seq_ens_empty.

  funfold1 k.


  rewrite <- norm_seq_assoc; shiftfree.
  rewrite norm_rs_seq_ens_void.



  apply ent_req_r.

Search (entails_under _ (ens_ _;; _) _).
  (* rewrite norm_seq_all. *)

    (* apply ent_seq_all_l. exists a *)

  (* finst x. *)

  Search (rs (fex _)).
  Search (seq _ (fall _)).


  (* 2: { shiftfree. rewrite rs_elim. shiftfree. } *)

  (* rewrites (>> norm_bind_val (f)). *)

  pose proof ent_unk.
  specializes H (Fmap.update s_env "k"
  (fun a0 : val =>
rs
  (ens_ \[vbool x = a0];;
(ens (fun r2=> \[r2 = vbool x]));;
(ens (fun r2=> \[x = true /\ r2 = vint 1 \/ x = false /\ r2 = vint 0])))
  r0)) "k".
  specializes H (vbool true) (vint r1) ___.
  rew_fmap *.

(* Set Typeclasses Debug. *)
  rewrite H. clear H.

  (* pose proof (red_nc). *)
  lets: red_normal (vint r1).
  rewrite H. 2: { shiftfree. }
  clear H.

  rewrite <- norm_ens_ens. *)

Abort.

  (* funfold1 "k". *)
  (* unfold k. *)

  (* rewrite norm_rs_seq_distr.
  2: {
    shiftfree.
  }
  fintro r0.
  rewrite red_skip.
  2: { shiftfree. }
  2: { shiftfree. } *)


  (* apply ent_rs_seq_assoc_unk.

  rewrite <- norm_seq_assoc.
  3: { shiftfree. }
  2: { shiftfree. } *)

  (* rewrite <- norm_seq_assoc.
  3: { shiftfree. }
  2: { shiftfree. } *)

  (* rewrite (red_skip_conv _ (ens_ (x0 ~~> vint (a + 1)))). *)
  (* pose proof red_skip_conv. *)
  (* specializes H (ens_ (x0 ~~> vint (a + 1))). *)
  (* Unset Printing Notations. Set Printing Coercions. Set Printing Parentheses. *)
  (* rewrite H. *)


  (* either prove k is sf, rewrite with sf_entails,
    or have a special case rule *)



(* Unset Printing Notations. Set Printing Coercions. Set Printing Parentheses. *)
  (* Search (entails_under _ (rs (seq (ens _) _)) _). *)
  (* rewrite <- red_skip. *)

  (* rewrite red_normal. *)
  (* rewrite norm_rs_rs. *)


  (* apply ent_rs_ *)
  (* Check 1. *)

  (* rewrite norm_ens_ens_. *)
  (* rewrite red_normal. *)
  (* setoid_rewrite red_normal at 2. *)


  (* apply norm_rs_seq_seq_ens. *)

  (* apply ent_seq_ens_req. *)


  (* need to prove k is shift free to reassoc, but cannot unfold it *)
  (* 2: {
    shiftfree.
  } *)

  (* ent_seq_ens_req. *)
  (* try to prove special case of proper if shift free *)


(* can only rewrite on the left of ;;, so we have to do things in this order *)

  (* Search (req \[_] _). *)
(* norm_seq_req_emp. *)

  

(* HANLDE THE DEFUN *)

  (* apply ent_defun_left.
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
  } *)
  

(* PREVIOUS ATTEMPT TRYING TO ADD DISCARD *)

  (* apply ent_discard_intro1.
  Check ent_discard_intro1. *)

  (* Check ent_seq_defun.
  Fail apply ent_seq_defun.
  Check ent_seq_defun_discard. *)

(* pose proof ent_seq_defun_discard.
specializes H
(req (x0 ~~> vint a) (ens (fun r0 => x0 ~~> vint (a + 2) \* \[r0 = vint 1]))).
  rewrite <- H. *)
  (* 2: { 
    (* Search shift_free. *)
    Check sf_req.
    apply sf_req.

  } *)
(* clear H. *)

  (* apply ent_seq_defun.
  Search (rs _ _).
  Search (rs (fall _) _). *)

  (* funfold1 "k". unfold k. *)
  (* Check ent_unk. *)
  

  (* funfold1 "k". *)
  (* unfold k. *)

  (* simpl. *)
  (* [ | unfold env; resolve_fn_in_env ] *)

  (* rewrite norm_rs_all. finst x0.
  rewrite norm_rs_all. finst a.
  rewrite norm_rs_ex. fintro r1.

Check norm_reassoc.
  rewrite norm_reassoc.
  rewrite <- norm_seq_assoc. *)
  (* cannot rewrite on the right of a seq, so need to untangle the discard first *)

  (* apply s_discard. *)

  (* pose proof (
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
   *)



  (* funfold1 "k". *)

(* finst x0. *)
  (* fintro x0. fintro a.
  funfold1 "s". unfold s. *)

  (* apply ent_discard. *)

  (* admit.
Abort. *)

(* Definition toss : ufun := fun n' =>
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

End Toss. *)
