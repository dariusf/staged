
From ShiftReset Require Import Basics ShiftFree.

(** * Lemmas about satisfies *)
Lemma ens_void_pure_intro : forall P s h,
  P -> satisfies s s h h (norm vunit) (ens_ \[P]).
Proof.
  intros.
  unfold ens_.
  constructor.
  exists vunit.
  exists empty_heap.
  splits*.
  { rewrite hstar_hpure_r.
    intuition.
    apply hpure_intro.
    reflexivity. }
Qed.

Lemma ens_pure_intro : forall P s h r,
  P r -> satisfies s s h h (norm r) (ens (fun v => \[P v])).
Proof.
  intros.
  constructor.
  exists r.
  exists empty_heap.
  hint hpure_intro.
  splits*.
Qed.

Lemma ens_void_pure_inv : forall P s1 s2 h1 h2 R,
  satisfies s1 s2 h1 h2 R (ens_ \[P]) ->
  P /\ h1 = h2 /\ s1 = s2 /\ R = norm vunit.
Proof.
  intros.
  inverts H as H. destr H.
  rewrite hstar_hpure_l in H. destr H.
  apply hpure_inv in H4. destr H4. subst.
  intuition.
Qed.

Lemma empty_intro : forall s1 h1,
  satisfies s1 s1 h1 h1 (norm vunit) empty.
Proof.
  intros.
  unfold empty, ens_.
  constructor.
  exists vunit.
  exists empty_heap.
  splits*.
  { rewrite hstar_hpure_l.
    intuition.
    apply hpure_intro.
    constructor. }
Qed.

Lemma empty_inv : forall s1 s2 h1 h2 R,
  satisfies s1 s2 h1 h2 R empty ->
  s1 = s2 /\ h1 = h2 /\ R = norm vunit.
Proof.
  unfold empty.
  intros.
  apply ens_void_pure_inv in H.
  intuition.
Qed.

Lemma ens_store_frame : forall s1 s2 h1 h2 R x uf Q,
  satisfies s1 s2 h1 h2 R (ens Q) ->
  satisfies (Fmap.update s1 x uf) (Fmap.update s2 x uf) h1 h2 R (ens Q).
Proof.
  intros.
  inverts H as H. destr H.
  subst.
  apply s_ens. exs.
  intuition eauto.
Qed.

(** * Examples for semantics *)
Module Examples.

  Example e1_undelimited : forall k, exists R,
    satisfies empty_env empty_env empty_heap empty_heap R
      (sh k (ens (fun r2 => \[r2 = vint 1]))).
  Proof.
    intros.
    eexists.
    apply* s_sh.
    (* Show Proof. *)
    (* result of continuation can be anything because it's never used *)
  Qed.

  Example e2_reset_value :
    satisfies empty_env empty_env empty_heap empty_heap (norm (vint 1))
      (rs (ens (fun r => \[r = vint 1]))).
  Proof.
    intros.
    apply s_rs_val.
    apply ens_pure_intro.
    reflexivity.
  Qed.

  Example e3_rs_sh_no_k : forall k, exists s,
    satisfies empty_env s empty_heap empty_heap (norm (vint 1))
      (rs (sh k (ens (fun r => \[r = vint 1])))).
  Proof.
    intros.
    eexists.
    (* the ret of the shift can be anything because the cont is never taken *)
    applys s_rs_sh k.
    { apply* s_sh. }
    { apply s_rs_val.
      (* produced by eapply, never instantiated because continuation is never taken *)
      apply ens_pure_intro.
      reflexivity. }
  Qed.

  Definition vplus (a b:val) : val :=
    match a, b with
    | vint a, vint b => vint (a + b)
    | _, _ => vunit
    end.

  (** [reset (1 + shift k (k 2))]. *)
  Example e4_rs_sh_k : forall k, exists s,
  satisfies empty_env s empty_heap empty_heap (norm (vint 3))
    (rs (sh k (unk k (vint 2));; ens (fun r => \[r = vint (1 + 2)]))).
  Proof.
    intros.
    eexists. (* this is okay because it's an output *)
    applys s_rs_sh k.
    (* put the ens into the cont *)
    {
      (* show that the body produces a shift *)
      apply s_bind_sh.
      apply* s_sh. }
    { apply s_rs_val. (* handle reset *)

      eapply s_unk. resolve_fn_in_env. (* reset body *)
      simpl.
      apply s_rs_val.
      eapply s_bind.
      { apply ens_pure_intro. jauto. }
      { apply ens_pure_intro. jauto. }
    }
  Qed.

  (** [(reset (shift k (fun a -> k a))) 4 ==> 4]
  - The whole thing returns what the application of f/k returns
  - The result of the shift is 4 due to the identity k
  - The result of the reset is a function; 4 is the result of an inner reset that appears in the course of reduction *)
  Example e5_shift_k : forall k xf, k <> xf -> exists s,
    satisfies empty_env s empty_heap empty_heap (norm (vint 4))
      (rs (sh k (defun xf (unk k);;
        ens (fun r => \[r = vfptr xf])));; unk xf (vint 4)).
  Proof.
    intros.
    eexists.
    eapply s_bind.
    { (* show that reset produces a function *)
      applys s_rs_sh k.
      (* handle the shift *)
      apply* s_sh.
      (* show how the shift body goes through the reset to produce the function *)
      { apply s_rs_val.
        eapply s_bind.
        apply* s_defun.
        (* { apply not_indom_update.
          apply not_indom_empty.
          symmetry. assumption. } *)
        apply ens_pure_intro. reflexivity. }
    }
    { (* show that applying the function returns 4 *)
      eapply s_unk. resolve_fn_in_env.
      simpl.
      (* applying the function amounts to applying the continuation *)
      eapply s_unk.
      (* TODO resolve_fn_in_env should solve this *)
      { unfold Fmap.update.
        rewrite Fmap.read_union_r.
        rewrite Fmap.read_union_l.
        apply Fmap.read_single.
        apply Fmap.indom_single.
        apply fmap_not_indom_of_neq.
        easy. }
      simpl.

      apply s_rs_val.
      apply~ ens_pure_intro.
    }
  Qed.

  (** [(reset 1 + (shift k (fun a -> k a))) 4 ==> 5]
  - res of shift = arg of k = 4
  - res of reset = res of shift body = fptr
  - final res is that of the inner reset, which doesn't occur syntacically in the code as it is produced by the "handling" of the shift. *)
  Example e6_shift_k : forall k xf, k <> xf -> exists s,
    satisfies empty_env s empty_heap empty_heap (norm (vint 5))
      (rs (bind (sh k (defun xf (unk k);; ens (fun r => \[r = vfptr xf])))
              (fun sr => ens (fun r => \[r = vplus (vint 1) sr])));;
        unk xf (vint 4)).
  Proof.
    intros.
    eexists.
    eapply s_bind.
    { (* reset *)
      (* the shift is still "handled", but produces a lambda without
        applying the continuation *)
      applys s_rs_sh k.
      { apply s_bind_sh. (* this moves the ens into the continuation *)
        apply* s_sh. }
      { apply s_rs_val.
        eapply s_seq.
        apply* s_defun.
        apply* ens_pure_intro. }
    }
    { (* app *)
      eapply s_unk. resolve_fn_in_env. simpl.
      eapply s_unk.
      (* TODO resolve should solve this *)
      { unfold Fmap.update.
        rewrite Fmap.read_union_r.
        rewrite Fmap.read_union_l.
        apply Fmap.read_single.
        apply Fmap.indom_single.
        apply* fmap_not_indom_of_neq. }
      simpl.
      apply s_rs_val.
      eapply s_bind. apply* ens_pure_intro.
      simpl.
      apply* ens_pure_intro.
    }
  Qed.

End Examples.

(* Given a [satisfies ... (shs ... k)] hypothesis,
  produces [satisfies ... (shc ... k)] and an assumption
  that k is shift-free *)
(* Ltac elim_shs H :=
  lazymatch type of H with
  | satisfies _ _ _ _ _ (shs _ _ _ _) =>
    inverts H as H; no_shift; destr H;
    apply ens_void_pure_inv in H; destr H;
    lazymatch goal with
    | H: norm _ = norm _ |- _ => injects H
    end;
    subst
  | _ => fail
  end. *)

(* Given a [satisfies ... (shs ... k)] goal,
  we have to prove [k] is shift-free before we can reduce
  it into a [satisfies ... (shc ... k)] goal. *)
(* Ltac intro_shs :=
  lazymatch goal with
  | |- satisfies _ _ _ _ _ (shs _ _ _ _) =>
    eapply s_seq; [ apply ens_void_pure_intro | ]
  | _ => fail
  end. *)

Lemma ens_req_inv : forall s1 s2 h1 h2 R H f,
  satisfies s1 s2 h1 h2 R (ens_ H;; req H f) ->
  satisfies s1 s2 h1 h2 R f.
Proof.
  intros.
  inverts H0 as H0; no_shift.
  inverts H0 as H0. destr H0. hinv H0. hinv H0.
  inverts H8 as H15. specializes H15 H3.
  subst. rew_fmap *.
Qed.

Lemma req_empty_inv : forall s1 s2 h1 h2 R f,
  satisfies s1 s2 h1 h2 R (req \[] f) ->
  satisfies s1 s2 h1 h2 R f.
Proof.
  intros.
  inverts H as H6. specializes H6 empty_heap h1 ___.
  apply hempty_intro.
Qed.

Lemma req_empty_intro : forall s1 s2 h1 h2 R f,
  satisfies s1 s2 h1 h2 R f ->
  satisfies s1 s2 h1 h2 R (req \[] f).
Proof.
  intros.
  apply s_req. intros.
  hinv H0.
  subst. rew_fmap *.
Qed.

Lemma ens_empty_intro : forall s1 h1 r,
  satisfies s1 s1 h1 h1 (norm r) (ens (fun r => \[])).
Proof.
  intros.
  apply s_ens.
  exists r empty_heap.
  intuition fmap_eq.
  constructor.
Qed.

Lemma ens_void_empty_intro : forall s1 h1,
  satisfies s1 s1 h1 h1 (norm vunit) (ens_ \[]).
Proof.
  intros.
  constructor.
  exs.
  splits*.
  hintro.
  splits*.
  hintro.
  rew_fmap.
  reflexivity.
Qed.

Lemma satisfies_ens_void : forall H1 H2 s1 s2 h1 h2 R,
  H1 ==> H2 ->
  satisfies s1 s2 h1 h2 R (ens_ H1) ->
  satisfies s1 s2 h1 h2 R (ens_ H2).
Proof.
  intros.
  inverts H0 as H3. destruct H3 as (v&h3&?&?&?&?).
  constructor. exists v. exists h3.
  intuition.
  rewrite hstar_hpure_l in H3.
  rewrite hstar_hpure_l.
  intuition.
Qed.

Lemma ens_inv : forall s1 s2 h1 h2 R Q,
  satisfies s1 s2 h1 h2 R (ens Q) ->
  s1 = s2.
Proof.
  intros.
  inverts H as H. destr H.
  reflexivity.
Qed.

Lemma unk_inv : forall s1 s2 h1 h2 R x a uf,
  Fmap.read s1 x = uf ->
  satisfies s1 s2 h1 h2 R (unk x a) ->
  satisfies s1 s2 h1 h2 R (uf a).
Proof.
  intros.
  inverts H0 as H0.
  rewrite H in H0.
  assumption.
Qed.

Lemma satisfies_ens_ens_void_split : forall H1 H2 s1 s2 h1 h2 R,
  satisfies s1 s2 h1 h2 R (ens_ (H1 \* H2)) ->
  satisfies s1 s2 h1 h2 R (ens_ H1;; ens_ H2).
Proof.
  intros.
  inverts H as H. destruct H as (v&h3&H3&H4&H5&H6).
  rewrite hstar_hpure_l in H4. destruct H4 as (H4&H7).
  (* h3 is the heap that H1 and H2 together add *)
  (* find the intermediate heap *)
  apply hstar_inv in H7. destruct H7 as (h0&h4&H8&H9&H10&H11).
  (* H1 h0, H2 h4 *)
  applys s_seq.
  { constructor. exists vunit. exists h0. intuition. rewrite hstar_hpure_l. intuition. }
  { constructor. exists v. exists h4. intuition. rewrite hstar_hpure_l. intuition. }
Qed.

Lemma satisfies_ens_ens_void_combine : forall H1 H2 s1 s2 h1 h2 R,
  satisfies s1 s2 h1 h2 R (ens_ H1;; ens_ H2) ->
  satisfies s1 s2 h1 h2 R (ens_ (H1 \* H2)).
Proof.
  intros.
  inverts H as H; no_shift. destr H.
  (* give up on careful reasoning *)
  inverts H as H. destr H.
  inverts H9 as H9. destr H9.
  hinv H. hinv H. hinv H6. hinv H6.
  applys_eq s_ens_. injects H0. subst. reflexivity.
  exists (h0 \u h4).
  splits*.
  subst.
  hintro; jauto.
  rew_fmap *.
  rew_fmap *.
Qed.

Lemma fall_intro : forall s1 s2 h1 h2 R A (fctx:A -> flow),
  (forall b, satisfies s1 s2 h1 h2 R (fctx b)) ->
  satisfies s1 s2 h1 h2 R (∀ b, fctx b).
Proof.
  intros.
  constructor.
  auto.
Qed.

Lemma req_pure_inv: forall s1 s2 h1 h2 R P f,
  P ->
  satisfies s1 s2 h1 h2 R (req \[P] f) ->
  satisfies s1 s2 h1 h2 R f.
Proof.
  intros.
  inverts H0 as H7.
  specializes H7 empty_heap h1. apply H7.
  hintro. assumption. fmap_eq. fmap_disjoint.
Qed.

Lemma req_pure_intro : forall s1 s2 h1 h2 R P f,
  (P -> satisfies s1 s2 h1 h2 R f) ->
  satisfies s1 s2 h1 h2 R (req \[P] f).
Proof.
  intros.
  apply s_req. intros.
  hinv H0. subst. rew_fmap.
  apply* H.
Qed.
