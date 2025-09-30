From ShiftReset Require Import Logic Automation Entl Norm Propriety.
From ShiftReset Require ExamplesEnt.
Local Open Scope string_scope.

Definition vminus := viop (fun x y => x - y).
Definition vtimes := viop (fun x y => x * y).

Definition landin_rec f :=
  ∃' r f_name,
  ens_ \[f = vfptr f_name];;
  defun "knot" (fun n =>
    fall (fun r_pointee =>
      req (r ~~> r_pointee) 
      (ens_ (r ~~> r_pointee) ;; unk f_name (vtup r_pointee n)))) ;;
  ens_ (r ~~> vfptr "identity");;
  req (r ~~> vfptr "identity")
  (ens (fun res => r ~~> vfptr "knot" \* \[res = vfptr "knot"])).

Definition factorial_inner params :=
  ∃' self n,
    ens_ \[params = vtup (vfptr self) n] ;;
    disj
    (ens (fun r => \[vle n (vint 0) /\ r = vint 1]))
    (ens_ \[vgt n (vint 0)] ;;
    bind (unk self (vminus n (vint 1)))
      (fun rec_call => ens (fun r => \[r = vtimes n rec_call]))).

Fixpoint factorial_pure n :=
  match n with
  | O => 1
  | S n' => n * factorial_pure n'
  end.

Lemma entl_ens_hstar_pure_r : forall (s : senv) (h : hprop) (P : val -> Prop),
  entails_under s
  (ens (fun r => h \* \[P r]))
  (ens_ h ;; ens (fun r => \[P r])).
Proof.
  unfold entails_under.
  intros.
  apply norm_ens_hstar_pure_r.
  assumption.
Qed.


Lemma norm_bind_ens_pure : forall s P fk,
  entails_under s 
  (bind (ens (fun r => \[P r])) fk)
  (∃' r, ens_ \[P r] ;; (fk r)).
Proof.
  intros.

  apply ent_bind_ens_pure_l.
  intros r H.
  fexists_old r.
  unfold entails_under.
  intros.
  apply (@s_seq s h1 vunit _ _ _ _ _ _ _ ).
  apply s_ens. 
  eexists. eexists. intuition.
  - rewrite hstar_hpure_conj. apply hpure_intro. intuition.
  - rewrite Fmap.union_empty_r. reflexivity.
  - assumption.
Qed.

Lemma entl_ens_hstar_pure_l : forall s h P,
  entails_under s
  (ens_ h ;; ens (fun r => \[P r]))
  (ens (fun r => h \* \[P r])).
Proof.
  unfold entails_under.
  intros.
  inverts H.
  {
    inverts H7.
    destruct H5 as (v0&h4&Hnorm&S1&(Hd1&Hd2)).
    inverts Hnorm.
    rewrite hstar_hpure_l in S1. destruct S1 as (Seq&S). subst.
    inverts H8. 
    destruct H5 as (v&h3&HR&H3&H2&Haa).
    hinv H3.
    subst.
    apply s_ens.
    eexists. eexists. intuition.
    rewrite hstar_comm. rewrite hstar_hpure_l. intuition.
  }
  - inverts H6. destruct H5 as (v&_&Hfalse&_). inverts Hfalse.
Qed.

(* some helper lemmas to establish existing entailments, but in the other
  direction *)

Lemma norm_bind_seq_assoc1: forall fk f1 f2,
  shift_free f1 -> entails (f1 ;; bind f2 fk) (bind (f1 ;; f2) fk).
Proof.
  intros * Hsf.
  introv Hseq_bind. 
  inverts Hseq_bind. 2: { false Hsf H5. }
  inverts H7.
  {
    apply (@s_bind s0 h0 v0);
    [ apply (@s_seq s3 h3 v) | ].
    all: assumption.
  }
  {
    apply s_bind_sh.
    apply (@s_seq s3 h3 v).
    all: assumption.
  }
Qed.

Lemma norm_seq_ex_r1 : forall {T : Type} (f1 : flow) (f2 : T -> flow), 
  shift_free f1 -> entails (∃' x, f1 ;; f2 x) (f1 ;; ∃' x, f2 x).
Proof.
  intros. 
  introv Hex_seq.
  inverts Hex_seq.
  destruct H6 as [b Hseq].
  inverts Hseq. 2: { false H H6. }
  apply (@s_seq s3 h3 v).
  - auto.
  - apply s_fex. exists b. auto.
Qed.

(* analogous to ent_seq_defun_both *)
Lemma ent_seq_discard_both : forall s name f1 f2,
  Fmap.indom s name
  -> entails_under (Fmap.remove s name) f1 f2
  -> entails_under s (discard name ;; f1) (discard name ;; f2).
Proof.
  intros s name f1 f2 Hindom Hentail.
  unfold entails_under. intros Hpre Hpost spost R Hf1.
  inverts Hf1.
  2: { inverts H5. }
  inverts H6.
  apply (@s_seq (Fmap.remove s name) h3 vunit).
  - apply s_discard. auto.
  - rewrite Hentail in H7. auto.
Qed.

(* [entl_ens_single], lifted to the entails_under setting *)
Lemma ent_ens_single : forall s (Q1 : postcond) (Q : postcond),
  Q1 ===> Q -> entails_under s (ens Q1) (ens Q).
Proof.
  intros. 
  unfold entails_under.
  intros.
  inverts H0. destr H7. subst.
  apply s_ens.
  eexists. eexists.
  intuition.
  apply H. assumption.
Qed.

(* some custom tactics *)
Ltac resolve_fn_in_env1 := 
  match goal with
  | |- Fmap.read (Fmap.update _ ?k _) ?k = _ =>
    rewrite fmap_read_update; [reflexivity | solve_not_indom]
  | |- Fmap.read (Fmap.update _ _ _) _ = _ =>
    unfold Fmap.update;
    resolve_fn_in_env1
  | |- Fmap.read (Fmap.single ?k _) ?k = _ =>
    rewrite Fmap.read_single; reflexivity
  (* | |- ?g => idtac "resolve_fn_in_env could not solve:"; idtac g *)
  | |- Fmap.read (Fmap.union _ _) _ = _ =>
    first [
      rewrite Fmap.read_union_l; [resolve_fn_in_env1 | apply Fmap.indom_single] |
        rewrite Fmap.read_union_r; [resolve_fn_in_env1 | solve_not_indom]
    ]
  end.

Ltac funfold2_inner f_name :=
  match goal with
  | |- entails_under _ _ _ =>
      rewrite entails_under_unk; [| resolve_fn_in_env1]
  end.

(* wrapper tactic to fold factorial_env out for readability *)
Ltac funfold2 env f := unfold env; funfold2_inner f; fold env.


Module Attempt1.

Definition factorial n := bind (unk "landin_rec" (vfptr "factorial_inner"))
  (fun f => ∃' bound_name, ens_ \[ f = vfptr bound_name ] ;; unk bound_name n).

Definition factorial_env : senv :=
  let map := Fmap.empty in
  let map := Fmap.update map "landin_rec" landin_rec in
  let map := Fmap.update map "factorial_inner" factorial_inner in
  map.

Definition factorial_correctness n' :=
  ∃' r fptr,
  (* some garbage to hide behind an existential (maybe possible if i add a 'discard' to factorial) *)
  defun "knot" (fun n =>
    fall (fun r_pointee =>
      req (r ~~> r_pointee) 
      (ens_ (r ~~> r_pointee) ;; unk "factorial_inner" (vtup r_pointee n))));;
  (* the actual correctness spec *)
  (∃' v, ens (fun res => (r ~~> vfptr fptr) \* \[res = vint v /\ v = factorial_pure n'])).
Lemma factorial_spec : forall n n',
  n = vint (Z.of_nat n') ->
  entails_under factorial_env
  (factorial n)
  (factorial_correctness n').
Proof.
  intros n n' nrefl.


  unfold factorial, factorial_correctness.

  funfold2 factorial_env "landin_rec".
  unfold landin_rec.

  (* now we do a sequence of (painful) rewrites to bring the defun out as the first stage *)
  (* bring the existentials out of the binder *)
  fdestruct_old b.
  fdestruct_old f_name.

  (* lift the f_name equality to the metalogic *)
  rewrite norm_bind_seq_assoc. 2: { apply sf_ens. } (* can i automate solving goal 2 there? *)
  apply ent_seq_ens_void_pure_l. intros H. inverts H.
 
  (* expose both defuns as the first stage *)
  rewrite norm_bind_defun_out.
  apply ent_ex_r. exists b.
  apply ent_ex_r. exists "knot".

  (* how do i rewrite under a [defun]? *)
  (* match both defun stages *)
  apply ent_seq_defun_both.

  (* eliminate the ens/req pair *)
  fbiabduction.
  rewrite entl_ens_hstar_pure_r. rewrite norm_bind_seq_assoc. 2: { apply sf_ens. } (* can i automate solving goal 2 there? *)

  rewrite norm_bind_val.
  rewrite norm_seq_ex_r. 2: { apply sf_ens. }
  apply ent_ex_l. intros knot_name.

  rewrite norm_ens_void_pure_swap.

  apply ent_seq_ens_void_pure_l. intros H. inverts H.

  funfold2 factorial_env "knot".

  (* unfold [knot] *)
  simpl.
  rewrite norm_seq_all_r. 2: { apply sf_ens. }
  apply ent_all_l.
  exists (vfptr "knot").

  funfold2 factorial_env "factorial_inner".

  fbiabduction. subst.

  induction n' as [|npred].
  {
    simpl. unfold factorial_inner.
    rewrite norm_seq_ex_r.
    (* we need to use the _old variants of tactics, because these are the ones
       that work with an entails_under *)
    fdestruct_old x.
    fdestruct_old n0.

    (* lift the unpacking of var into the context *)
    rewrite norm_ens_void_pure_swap.
    apply ent_seq_ens_void_pure_l.
    intros H. inverts H. subst.

    (* clear the right-hand existential *)
    fexists_old 1.

    rewrite norm_seq_disj_r. all: try (apply sf_ens).
    (* handle two cases of the disjunction *)
    apply ent_disj_l.
    {
      rewrite entl_ens_hstar_pure_l.
      apply ent_ens_single.
      xsimpl.
      intuition.
    } 
    {
      rewrite norm_ens_void_pure_swap.
      apply ent_seq_ens_void_pure_l. intros H. invert H.
    }
  }
  {
    unfold factorial_inner.
    rewrite norm_seq_ex_r.
    (* we need to use the _old variants of tactics, because these are the ones
       that work with an entails_under *)
    fdestruct_old x.
    fdestruct_old n0.

    (* lift the unpacking of var into the context *)
    rewrite norm_ens_void_pure_swap.
    apply ent_seq_ens_void_pure_l.
    intros H. 
    (*rewrite Zpos_P_of_succ_nat in H2. rewrite Zpos_P_of_succ_nat. clear H. subst.*)
    inverts H. subst.
    rewrite norm_seq_disj_r. all: try (apply sf_ens).
    apply ent_disj_l.
    {
      apply ent_ex_r. eexists.
      rewrite entl_ens_hstar_pure_l.
      apply ent_ens_single.
      xsimpl.
      intuition. subst.
      unfold vle, virel in H0.
      lia. (* automatically discharge the contradiction *)
    }
    {
      rewrite norm_ens_void_pure_swap.
      apply ent_seq_ens_void_pure_l. intros H.

      funfold2 factorial_env "knot".
      simpl.
      rewrite norm_bind_all_l.
      rewrite norm_seq_all_r. 2: { apply sf_ens. }
      apply ent_all_l.
      exists (vfptr "knot").

      rewrite norm_bind_req.
      fbiabduction.
      
      funfold2 factorial_env "factorial_inner".
       
      (* invoke the induction hypothesis *)
      rewrite Zpos_P_of_succ_nat. (* massage the term to match the IH *)
      autorewrite with nz.
      rewrite IHnpred.


      rewrite norm_bind_ex_l. fdestruct_old rec_result.
      (* match the b ~~> vfptr "knot" on both sides *)
      rewrite entl_ens_hstar_pure_r.
      rewrite norm_bind_seq_assoc. 2: { apply sf_ens. }
       
      apply ent_ex_r. eexists.
      
      (* invoke something like
         bind (ens (fun r => \[P r])) f ⊑ fex (fun r => ens_ \[P r] ;; f r)
         
         [ent_bind_ens_pure_l] is almost this, but the `bind` has to be at the top-level

         [norm_bind_seq_ex] is almost this but it doesn't connect P to the existential *)
      rewrite norm_bind_ens_pure.
      
      (* match the heap state on both sides *)
      rewrite norm_seq_ex_r. 2: { apply sf_ens. }
      fdestruct_old x.
      rewrite norm_ens_void_pure_swap.
      apply ent_seq_ens_void_pure_l. intros [Htemp1 Htemp2]. subst.

      rewrite norm_ens_ens_void_l.

      (* reduce this to an entailment between postconditions *)
      apply (ent_ens_single).
      unfold qimpl. intros res.
      
      xsimpl.
      rewrite Z_of_nat_S.
      intuition.
      auto.
    }
  }
Qed.

End Attempt1.
Module Attempt2.

(* now, let's attempt to prove a spec that doesn't mention the function in the store

   since the underlying separation logic is only selectively affine, we do this by discarding
   knot after the function call completes *)

Definition factorial n := bind (unk "landin_rec" (vfptr "factorial_inner"))
  (fun f => ∃' bound_name, ens_ \[ f = vfptr bound_name ] ;;
    bind (unk bound_name n)
    (fun res =>
      (* 'deallocate' knot, and the function pointer to it *)
      ∀' r,
      req (r ~~> vfptr bound_name)
      (discard bound_name;;
       ens (fun r => \[res = r])
      ))).

Definition factorial_correctness n' :=
  (* now the spec only needs to mention the return value *)
  (∃' v, ens (fun res => \[res = vint v /\ v = factorial_pure n'])).

Definition factorial_env : senv :=
  let map := Fmap.empty in
  let map := Fmap.update map "landin_rec" landin_rec in
  let map := Fmap.update map "factorial_inner" factorial_inner in
  map.


(* we try to prove the same correctness theorem as earlier: *)
Theorem factorial_spec : forall n n',
  n = vint (Z.of_nat n') ->
  entails_under factorial_env
  (factorial n)
  (factorial_correctness n').
Proof.
  intros n n' Hn. subst.
  unfold factorial. 

  funfold2 factorial_env "landin_rec".
  unfold landin_rec.
  fdestruct_old r. fdestruct_old f_name.
  fsimpl.

  apply ent_seq_ens_void_pure_l. intros H. inverts H.

  rewrite norm_bind_defun_out.
  fbiabduction.

  (* we need a defun on the other side to put knot in the environment *)
  (* intrpduce the defun by adding a defun-discard pair *)
  rewrite <- (norm_seq_defun_discard _ "knot" (fun n0 : val =>
     ∀ r_pointee : Val.value,
       req (r ~~> r_pointee)
         (ens_ (r ~~> r_pointee);; unk "factorial_inner" (vtup r_pointee n0)))(factorial_correctness n')).
  
  2: {
    unfold factorial_env.
    unfold Fmap.update.
    (* solve_not_indom should solve this but it's missing some cases *)
    rewrite indom_union_eq. rewrite not_or_eq. split.
    - rewrite indom_single_eq. intuition. inverts H.
    - rewrite indom_union_eq. rewrite not_or_eq. split. 
      + rewrite indom_single_eq. intuition. inverts H.
      + apply not_indom_empty.
    
  }

  apply ent_seq_defun_both.

  rewrite entl_ens_hstar_pure_r.
  fsimpl.

  rewrite norm_seq_ex_r. 2: {shiftfree. }
  apply ent_ex_l. intros knot_name.
  rewrite norm_ens_void_pure_swap.
  apply ent_seq_ens_void_pure_l. intros H. inverts H.

  (* we state a version without the final discard to act as our induction hypothesis. *)
  assert (
  entails_under (Fmap.update factorial_env "knot"
    (fun n0 =>
     ∀' r_pointee,
       req (r ~~> r_pointee)
         (ens_ (r ~~> r_pointee);; unk "factorial_inner" (vtup r_pointee n0))))
    (ens_ (r ~~> vfptr "knot") ;; unk "knot" (Z.of_nat n'))
    (ens_ (r ~~> vfptr "knot") ;; factorial_correctness n')) as IH.

  {
    induction n' as [|npred IH].
    (* this induction mostly proceeds the same as in version 1 *)
    {
      funfold2 factorial_env "knot".
      subst.
      rewrite norm_seq_all_r. 2: { shiftfree. }

      apply ent_all_l. eexists.
      fbiabduction.
      funfold2 factorial_env "factorial_inner".
      unfold factorial_inner.

      rewrite norm_seq_ex_r. 2: { shiftfree. } fdestruct_old self.
      rewrite norm_seq_ex_r. 2: { shiftfree. } fdestruct_old n.
      rewrite norm_ens_void_pure_swap.

      apply ent_seq_ens_void_pure_l. intros H. inverts H.
      
      rewrite norm_seq_disj_r. 2: { shiftfree. }
      apply ent_disj_l.
      - unfold factorial_correctness.
        rewrite entl_ens_hstar_pure_l.
        rewrite <- norm_seq_ex_r1. 2: { shiftfree. }
        fexists_old 1.
        rewrite <- entl_ens_hstar_pure_r.
        apply ent_ens_single.
        xsimpl. intros. intuition.
      - rewrite norm_ens_void_pure_swap.
        apply ent_seq_ens_void_pure_l. intros H. inverts H.
    }
    {
      funfold2 factorial_env "knot".
      subst.
      rewrite norm_seq_all_r. 2: { shiftfree. }

      apply ent_all_l. eexists.
      fbiabduction.
      funfold2 factorial_env "factorial_inner".
      unfold factorial_inner.
      
      rewrite norm_seq_ex_r. 2: { shiftfree. } fdestruct_old self.
      rewrite norm_seq_ex_r. 2: { shiftfree. } fdestruct_old n.
      rewrite norm_ens_void_pure_swap.

      apply ent_seq_ens_void_pure_l. intros H. inverts H.
      rewrite norm_seq_disj_r. 2: { shiftfree. }
      apply ent_disj_l.
      - unfold factorial_correctness.
        rewrite entl_ens_hstar_pure_l.
        rewrite <- norm_seq_ex_r1. 2: { shiftfree. }
        apply ent_ex_r. eexists.
        rewrite <- entl_ens_hstar_pure_r.
        apply ent_ens_single.
        xsimpl. intros r0 [Hn Hr0]. subst. intuition.
      - rewrite norm_ens_void_pure_swap.
        apply ent_seq_ens_void_pure_l. intros H. inverts H.
        unfold vminus. unfold viop. autorewrite with nz.

        rewrite Zpos_P_of_succ_nat. (* massage the term to match the IH *)
        autorewrite with nz.
        rewrite norm_bind_seq_assoc1. 2: { shiftfree. }
        rewrite IH.

        rewrite norm_reassoc_ens_void.
        unfold factorial_correctness.

        rewrite norm_bind_ex_l.
        rewrite norm_seq_ex_r. 2: { shiftfree. }
        apply ent_ex_l. intros x.

        rewrite norm_bind_ens_pure.
        rewrite norm_seq_ex_r. 2: { shiftfree. }
        apply ent_ex_l. intros r0.

        rewrite norm_ens_void_pure_swap.
        apply ent_seq_ens_void_pure_l. intros H. inverts H.

        rewrite entl_ens_hstar_pure_l.
        rewrite <- norm_seq_ex_r1. 2: { shiftfree. }
        apply ent_ex_r. eexists.
        rewrite <- entl_ens_hstar_pure_r. 
        
        apply ent_ens_single.
        xsimpl. intuition. subst. rewrite <- Z_of_nat_S. auto.
    }
  }

  rewrite norm_bind_seq_assoc1. 2: { shiftfree. }
  rewrite IH.
  rewrite norm_bind_seq_assoc. 2: { shiftfree. }

  unfold factorial_correctness.

  rewrite norm_bind_ex_l. rewrite norm_seq_ex_r. 2: {shiftfree. }
  apply ent_ex_l. intros x.
  rewrite norm_bind_ens_pure.
  rewrite norm_seq_ex_r. 2: {shiftfree. }
  apply ent_ex_l. intros x0.
  rewrite norm_ens_void_pure_swap.
  apply ent_seq_ens_void_pure_l. intros H. inverts H.
  rewrite norm_seq_all_r. 2: { shiftfree. }
  apply ent_all_l. exists r.
  fbiabduction.

  apply ent_seq_discard_both.
  1: {apply indom_update. }

  apply ent_ex_r. eexists.
  apply ent_ens_single.
  xsimpl.
  intuition.
  auto.
Qed.

