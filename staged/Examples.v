
From Staged Require Import Logic Automation.
Local Open Scope string_scope.

(** * Examples *)
(** Examples of everything defined so far, which is enough for entailments to be defined and proved. *)

Definition f1 : flow := ens (fun r => \[r=vint 1]).
Definition f2 : flow := fall (fun x => req_ (\[x = vint 1])).
Definition f3 : flow := f1 ;; f2.

Example ex1: satisfies empty_env Fmap.empty Fmap.empty (norm (vint 1)) f1.
Proof.
  intros.
  unfold f1.
  apply s_ens.
  econstructor. eexists. intuition.
  apply hpure_intro_hempty.
  apply hempty_intro.
  reflexivity.
  fmap_eq.
Qed.

Example ex2_ret: flow_res f1 (vint 1).
Proof.
  unfold f1, flow_res.
  intros.
  inverts H as H. destr H.
  injects H0.
  inv H.
  reflexivity.
Qed.

Lemma flow_res_inv: forall v v1 f h1 h2 env,
  satisfies env h1 h2 (norm v) f ->
  flow_res f v1 ->
  v = v1.
Proof.
  unfold flow_res.
  intros.
  specializes H0 H.
  assumption.
Qed.

Example ex2_ret1: forall v, flow_res f1 v -> v = vint 1.
Proof.
  unfold f1, flow_res.
  intros.
  forwards: H empty_heap empty_heap empty_env (vint 1).
  { constructor.
    exists (vint 1). exists empty_heap.
    intuition.
    apply hpure_intro. reflexivity.
    fmap_eq. }
    congruence.
Qed.

Example ex3_req_ret: flow_res f2 vunit.
Proof.
  unfold flow_res, f2.
  intros.
  inverts H as H.
  specializes H (vint 1).
  apply req_pure_ret_inv in H.
  congruence.
  reflexivity.
Qed.

Definition f4 : flow := empty;; fall (fun r => unk "f" (vint 1) r).
Definition f4_env : senv :=
  Fmap.update empty_env "f" (Some (fun _ r => ens_ \[r = vint 2])).

(* has to be 2 *)
Example ex5_f_ret:
  flow_res_in_env f4 (vint 2) f4_env.
Proof.
  unfold flow_res_in_env, f4.
  intros.
  rewrite norm_empty_l in H.
  inverts H as H. specializes H v1.
  funfold f4_env "f" in H.
  simpl in H.
  apply ens_void_pure_inv in H.
  intuition.
Qed.

Definition f5 : flow := ens (fun r => \[r = vint 2]).
Definition f6 : flow := f1 ;; ens (fun r => \[r = vint 2]).

Example ex6_ent : f5 ⊑ f6.
Proof.
  unfold entails, f5, f6.
  intros.
  inverts H as H2.
  destruct H2 as (v & h3 & H1 & H2 & H3 & H4).
  subst r.
  constructor.
  exists h1.
  exists (norm (vint 1)).
  intuition.

  - unfold f1.
    constructor.
    exists (vint 1).
    exists empty_heap.
    intuition.
    apply hpure_intro_hempty.
    apply hempty_intro.
    intuition.
    fmap_eq.
  -
    constructor.
    eexists.
    exists empty_heap.
    intuition.
    apply hpure_intro_hempty.
    apply hempty_intro.
    apply hpure_inv in H2.
    intuition.
    apply hpure_inv in H2.
    intuition.
    fmap_eq.
Qed.

Example ex7_rewrite : f5 ⊑ f6.
Proof.
  rewrite ex6_ent.
  apply entails_refl.
Qed.

Example ex1_rewrite : forall H H1 f,
  entails (req (H \* H1) f) (req H (req H1 f)).
Proof.
  intros.
  rewrite norm_req_req.
  apply entails_refl.
Qed.

Example ex3_rewrite : forall H H1 f,
  bientails (req (H \* H1) f) (req H (req H1 f)).
Proof.
  intros.
  unfold bientails; split.
  { rewrite norm_req_sep_split.
    trivial. }
  { rewrite norm_req_sep_combine.
    apply entails_refl. }
Qed.

Example ex2_rewrite : forall H H1 H2 f,
  entails (req (H \* H1) (req H2 f)) (req H (req (H1 \* H2) f)).
Proof.
  intros.
  rewrite <- norm_req_req.
  rewrite <- norm_req_req.
  rewrite hstar_assoc.
  apply entails_refl.
Qed.

(* ensure that this can be done semantically *)
Example ex1_entail_co_contra : forall x y,
  entails (req \[x>0] (ens_ \[y=1])) (req \[x=1] (ens_ \[y>0])).
Proof.
  unfold entails.
  intros.
  (* get the condition in the req from the right *)
  constructor.
  intros.
  finv H0.
  (* use it to satisfy the req on the left *)
  inverts H as H.
  specialize (H hp hr).
  forward H. subst hp. fintro. math.
  specialize (H H1 H2).
  (* do the same for ens, but from left to right, as per normal *)
  inverts H as H. destr H. finv H. finv H. finv H6.
  constructor. exists v. exists empty_heap.
  intuition.
  rewrite hstar_hpure_r.
  split. fintro; auto. math.
  fmap_eq.
Qed.

Example e1 : forall x,
  satisfies empty_env empty_heap empty_heap (norm vunit) (req_ \[x = 1]).
Proof.
  intros.
  apply s_req.
  intros.
  apply hpure_inv in H as (?&?).
  intuition fmap_eq.
  constructor.
  eexists.
  eexists.
  intuition.
  rewrite hstar_hpure_l.
  split. auto.
  apply hpure_intro.
  constructor.
  assumption.
Qed.

Example e2 : forall x,
  satisfies empty_env (Fmap.single x (vint 1)) (Fmap.single x (vint 1)) (norm vunit) (req (x~~>vint 1) (ens_ (x~~>vint 1))).
Proof.
  intros.
  apply s_req.
  intros hp H.
  intros.

  apply hsingle_inv in H0. rew_fmap *.

  constructor.
  eexists.
  exists (Fmap.single x (vint 1)).
  intuition.
  { rewrite hstar_hpure_l; split; auto.
  apply hsingle_intro. }
  { subst. assumption. }
Qed.

Example e3 : forall x,
  satisfies empty_env empty_heap empty_heap (norm vunit) ((ens_ (x~~>vint 1)) ;; req_ (x~~>vint 1)).
Proof.
  intros.
  constructor.
  exists (Fmap.single x (vint 1)).
  exists (norm vunit).
  split.
  { constructor.
    exists vunit.
    exists (Fmap.single x (vint 1)).
    intuition.
    rewrite hstar_hpure_l; split; auto.
    apply hsingle_intro.
    fmap_eq. }
  {
    apply s_req.
    intros.
    { constructor.
      exists vunit.
      exists empty_heap.
      apply hsingle_inv in H.
      intuition.
      subst.
      rewrite hstar_hpure_l; split; auto.
      apply hpure_intro.
      constructor.
      fmap_eq.
      rewrite <- Fmap.union_empty_l in H0 at 1.
      apply Fmap.union_eq_inv_of_disjoint in H0.
      fmap_eq.
      unfold empty_heap; reflexivity.
      fmap_disjoint.
      fmap_disjoint. } }
Qed.

Example e4_req_false : forall x,
  satisfies empty_env
    (Fmap.single x (vint 1)) (Fmap.single x (vint 2)) (norm vunit)
    (req_ \[False]).
Proof.
  intros.
  apply s_req.
  intros.
  apply hpure_inv in H.
  destr H.
  inv H0.
  inv H2.
Qed.

Example e5_rew : forall x y,
  entails (req (x~~>vint 1) (req_ (y~~>vint 2)))
    (req_ (x~~>vint 1 \* y~~>vint 2)).
Proof.
  unfold entails.
  intros.

  (* reason backwrds *)
  apply s_req.
  intros.
  (* extract info from what we gained *)
  rew_fmap.
  apply hstar_inv in H0 as (hx&hy&Hx&Hy&?&?).

  (* start going forward *)
  inverts H as H.
  specialize (H _ (hy \u hr) Hx).
  forward H by fmap_eq.
  forward H by fmap_disjoint.

  inverts H as H12.
  specialize (H12 hy hr Hy).
  forward H12 by fmap_eq.
  forward H12 by fmap_disjoint.

  assumption.
Qed.

Definition e6_env : senv :=
  Fmap.single "f" (Some (fun y r =>
  match y with
  | vloc x => req (x~~>vint 1) (ens_ (x~~>vint 2))
  | _ => empty
  end)).

Example e6_fn_reassoc : forall x,
  entails_under e6_env
    (unk "f" (vloc x) vunit;; fall (fun a => req (x~~>vint a) (ens_ (x~~>vint a))))
    (req (x~~>vint 1) (ens_ (x~~>vint 2))).
Proof.
  (* Set Mangle Names. *)

  unfold entails_under.
  intros x h1 h2 r H.

  (* first reason backward to access the req *)
  constructor. intros hp hr H0 H1 H2. intros.

  (* the function is unknown, so use its definition,
    make it known, then build back up into a sequence *)
  pose proof H as G.
  inverts G as G. destruct G as (h3&r1&Hf&Hr).
  (* resolve the function *)
  unfold e6_env in Hf;
  eapply unk_inv in Hf; only 2: resolve_fn_in_env; simpl;
  fold e6_env in Hf; simpl in Hf.
  pose proof (@s_seq e6_env _ _ h1 h2 r (ex_intro (fun h3 => _) h3 (ex_intro (fun x => _) r1 (conj Hf Hr)))) as G.
  clear Hr. clear Hf.

  (* this is quite inconvenient compared to rewriting, however *)
  funfold e6_env "f" in H. simpl in H.
  clear G.

  (* reassociate *)
  rewrite norm_reassoc in H.

  (* discharge the req *)
  pose proof (hsingle_inv H0) as H3.
  (* finv H0. *)
  rewrite H1 in H.
  rewrite H3 in H.
  inverts H as H.
  specialize (H hp hr H0).
  forward H. fmap_eq.
  forward H. fmap_disjoint.
  clear H3. clear H0. clear H1. clear H2.

  dup.
  (* a semantic proof *)
  { (* seq *)
    inverts H as H. destruct H as (h0&r2&He&Hr).

    (* assume the ens *)
    inverts He as He. destruct He as (?&h4&?&H3&H4&?).
    rewrite hstar_hpure_l in H3. destruct H3 as [_ H6].
    pose proof (hsingle_inv H6) as H5.
    rewrite H4 in Hr.
    rewrite H5 in Hr.
    clear H4.

    (* existential *)
    inverts Hr as Hr.
    (* destr H4. *)
    specialize (Hr 2).

    (* prove next req *)
    inverts Hr as Hr.
    specialize (Hr h4 hr H6).
    forward Hr. fmap_eq.
    forward Hr. fmap_disjoint.

    auto. }

  (* we can reason at a higher level with rewriting *)

  rewrite norm_forall in H.
  inverts H as H. specialize (H 2).

  rewrites (>> norm_ens_req_transpose) in H.
  { instantiate (1 := fun _ => hempty). simpl.
    rewrite <- (hstar_hempty_r (x ~~> vint 2)).
    apply b_pts_match.
    apply b_base_empty. }

  rew_heap in H.
  rewrite norm_req_pure in H. 2: { reflexivity. }
  rewrite norm_seq_ens_empty in H.
  assumption.
Qed.

(* lfp interpretation *)
(*
  forall n res, sum(n, res) =
        n=0/\res=0
    \/ ex n1. ens n=n1/\n1>0; ex r1. sum(n-1,r1); ens res=1+r1
*)
Definition sum n res :=
  disj
    (ens_ \[exists n1, n = vint n1 /\ n1 <= 0 /\ res = vint 0])
    (fex (fun n1 => ens_ \[n = vint n1 /\ n1 > 0];; fex (fun r1 =>
      (unk "sum" (vint (n1-1)) (vint r1);;
        ens_ \[res = vint (1 + r1)])))).

Definition sum_env := (Fmap.update empty_env "sum" (Some sum)).
Definition sum_property (n res:val) := ens_ \[res = n].

(* Close Scope flow_scope. *)

Lemma ex_sum : forall n1 n res, n1 >= 0 ->
  n = vint n1 ->
  entails_under sum_env (sum n res) (sum_property n res).
Proof.
  unfold sum_property.
  (* do induction on the numeric value of n *)
  intros n.
  induction_wf IH: (downto 0) n.
  unfold sum, entails_under.
  intros.
  inverts H1 as H1.
  (* base case *)
  { apply ens_void_pure_inv in H1. destr H1. subst. injects H2.
    apply ens_void_pure_intro.
    f_equal. math. }
  (* recursive case *)
  { fdestr H1 as (n1&H1).
    apply seq_ens_void_pure_inv in H1. destruct H1 as ((?&?)&H1).
    fdestr H1 as (r1&H1).
    funfold sum_env "sum" in H1.
    specialize (IH (n1-1)).
    forward IH. assert (n1 = n). congruence. unfold downto. math.
    specialize (IH (vint (n1-1)) (vint r1)).
    forward IH. math.
    forward IH. reflexivity.
    rewrite IH in H1.
    clear IH.

    rewrite <- norm_ens_ens_void in H1.
    rewrite hstar_hpure_conj in H1.
    apply ens_void_pure_inv in H1. destr H1. subst.
    fintro.
    injects H2. injects H1. f_equal. math. }
Qed.

Module hello.

  Definition hello (f x y res:val) : flow :=
    match f, x, y with
    | vstr f, vloc x, vloc y =>
      ∃ a, req (x~~>vint a) (ens_ (x~~>vint (a+1));;
      ∃ r, unk f (vloc y) (vint r);;
      ∃ b b1, req (x~~>vint b \* y~~>vint b1)
        (ens_ (x~~>vint b \* y~~>res \* \[res = vint (b+r)])))
    | _, _, _ => empty
    end.

  Lemma hello_capture : forall x y,
    (* note that the ptr value is existentially quantified because
      we want to instantiate it. the forward rules use universal
      quantification because the result ends up on the left side of
      a sequent. *)
    let env := Fmap.single "f"
      (Some (fun y r => ∃ b,
        req (x~~>vint b)
          (ens (fun res =>
            (x~~>vint (b+1) \* \[r = vint 0] \* \[r = res])))))
    in
    let init_heap :=
      Fmap.update (Fmap.single x (vint 0)) y (vint 0)
    in
    let final_heap :=
      Fmap.update (Fmap.single x (vint 2)) y (vint 2)
    in
    x <> y ->
    satisfies env init_heap final_heap (norm vunit)
      (hello (vstr "f") (vloc x) (vloc y) (vint 2)).
  Proof.
    intros. unfold hello.
    constructor. exists 0.
    constructor. intros. finv H0.
    constructor. (* seq *)
      exists (Fmap.update (Fmap.single x (vint 1)) y (vint 0)).
      exists (norm vunit).
    split. constructor. exists vunit. exists (Fmap.single x (vint 1)).
    {

      assert (hr = Fmap.single y (vint 0)).
      {
      applys Fmap.union_eq_inv_of_disjoint hp hr (Fmap.single y (vint 0)).
      fmap_disjoint.
      subst.
      apply Fmap.disjoint_single_single.
      easy.
      fmap_eq.
      rewrite <- H1.
      unfold init_heap.
      unfold Fmap.update.
      fmap_eq.
      reflexivity.
      }
      intuition. fintro. intuition. apply hsingle_intro.
      unfold Fmap.update. fmap_eq.

      subst.
      apply Fmap.disjoint_single_single. easy.
    }

    constructor. exists 0.

    lets: ent_unk.
    specializes H3 env (vint 0) "f" (vloc y) ___.
    unfold env. resolve_fn_in_env. simpl in H3.

    constructor.
      exists (Fmap.update (Fmap.single x (vint 2)) y (vint 0)).
      exists (norm (vint 0)).

    split.
    lets H4: s_unk.
    applys H4.
    { unfold env. resolve_fn_in_env. }
    { 
      simpl.
      constructor. exists 1.
      constructor. intros. finv H5.
      constructor. exists (vint 0).
        exists (Fmap.single x (vint 2)).

      assert (hr0 = Fmap.single y (vint 0)).
      { applys Fmap.union_eq_inv_of_disjoint hp0 hr0 (Fmap.single y (vint 0)).
        fmap_disjoint.
        { subst; apply Fmap.disjoint_single_single; easy. }
        rewrite <- H6.
        unfold Fmap.update.
        fmap_eq.
        reflexivity.
        }
        intuition.
        rewrite hstar_hpure_conj.
        rewrite hstar_hpure_r. intuition.
        apply hsingle_intro.
        unfold Fmap.update. fmap_eq.
        subst hr0.
        apply Fmap.disjoint_single_single; easy. }

    constructor. exists 2.
    constructor. exists 0.

    constructor. intros.

    assert (hr0 = empty_heap).
    { unfold Fmap.update in H5. finv H4. finv H7. finv H4. subst x0 x1.
      change (HeapF.Fmap.single) with (Fmap.single) in H8.
      rewrite H9 in H5.
      lets: Fmap.union_eq_inv_of_disjoint
              (Fmap.single y (vint 0) \u Fmap.single x (vint 2))
              hr0 empty_heap.
      apply H4.
      fmap_disjoint.
      fmap_disjoint.
      rew_fmap.
      symmetry.
      change (HeapF.Fmap.single) with (Fmap.single) in H5.
      rewrite H5 at 1.
      
      fmap_eq.
      rewrite Fmap.union_comm_of_disjoint.
      2: {
        apply Fmap.disjoint_single_single; easy.
      }
      reflexivity.
    }

    constructor.
    exists vunit.
    exists (Fmap.update (Fmap.single x (vint 2)) y (vint 2)).
    splits; auto.
    unfold Fmap.update.
    rewrite hstar_hpure_l.
    rewrite hstar_comm.
    split.
    reflexivity.
    apply hstar_intro.
    rewrite hstar_hpure_r.
    split.
    apply hsingle_intro.
    reflexivity.
    apply hsingle_intro.
    apply Fmap.disjoint_single_single; easy.
    unfold final_heap.
    unfold Fmap.update.
    fmap_eq.
  Qed.

  (* TODO hello can be called with a function that captures x *)

End hello.

Module foldr.

  Definition foldr : ufun := fun (args:val) rr =>
    match args with
    | vtup (vstr f) (vtup (vint a) (vlist l)) =>
      disj
        (ens_ \[rr = vint a /\ l = nil])
        (fex (fun x => fex (fun r => fex (fun l1 =>
          ens_ \[l = cons (vint x) l1];;
          unk "foldr" (vtup (vstr f) (vtup (vint a) (vlist l1))) r;;
          unk f (vtup (vint x) r) rr))))
    | _ => empty
    end.

  Fixpoint sum (xs:list int) : int :=
    match xs with
    | nil => 0
    | y :: ys => y + sum ys
    end.

  (* Fixpoint sum_val (xs:list val) : expr :=
    match xs with
    | nil => pval (vint 0)
    | vint y :: ys => padd (pval (vint y)) (sum_val ys)
    | _ :: ys => pval vunit
    end. *)

  Fixpoint to_int_list (xs:list val) : list int :=
    match xs with
    | nil => nil
    | vint y :: ys => cons y (to_int_list ys)
    | _ :: _ => nil
    end.

  (* This isn't actually needed at this point *)
  Definition uncurried_plus_program :=
    vfun "x"
      (plet "a" (pfst (pvar "x"))
      (plet "b" (psnd (pvar "x"))
      (padd (pvar "a") (pvar "b")))).

  (* plus((a, b), r) = ens[_] r=a+b *)
  Definition uncurried_plus_spec : ufun := fun args rr =>
    match args with
    | vtup (vint a) (vint b) => ens_ \[rr = vint (a + b)]
    | _ => empty
    end.

  Definition foldr_env :=
    Fmap.update
        (Fmap.single "foldr" (Some foldr))
        "f" (Some uncurried_plus_spec).

  (** A re-summarization lemma *)
  Definition foldr_sum := forall xs res,
    entails_under foldr_env
      (unk "foldr" (vtup (vstr "f") (vtup (vint 0) (vlist xs))) res)
      (fex (fun r => ens_ \[res = vint r /\ r = sum (to_int_list xs)])).

  (** Reasoning semantically *)
  Lemma foldr_sum_semantic:
    foldr_sum.
  Proof.
    { unfold foldr_sum. intros xs. induction_wf IH: list_sub xs. intros.
      unfold entails_under. introv H.
      funfold foldr_env "foldr" in H. simpl in H.
      inverts H.
      { (* base case *)
        fdestr H5.
        fexists 0.
        subst. fintro.
        intuition. }
      { (* rec *)
        (* get at all the facts... *)
        fdestr H5 as (x&H5).
        fdestr H5 as (r0&H5).
        fdestr H5 as (l1&H5).
        fdestr H5 as (h3&r1&H1&H2).
        fdestr H1.
        (* apply induction hypothesis *)
        specialize (IH l1). forward IH. rewrite H. auto.
        rewrite IH in H2.

        fdestr H2 as (h0&r2&H0&Hf).
        fdestr H0 as (v&?H0).
        fdestr H0.

        (* reason about f *)
        funfold foldr_env "f" in Hf.

        simpl in Hf. subst r0.
        fdestr Hf.

        fexists (x + v).
        subst. fintro.
        intuition. } }
  Qed.

  (** Proof using entailment rules *)
  Lemma foldr_sum_entailment:
    foldr_sum.
  Proof.
    { unfold foldr_sum. intros xs. induction_wf IH: list_sub xs. intros.
      funfold foldr_env "foldr". simpl.
      apply ent_disj_l.

      { apply ent_ex_r. exists 0.
        apply ent_ens_single_pure.
        intuition. subst. reflexivity. }

      { apply ent_ex_l. intros x.
        apply ent_ex_l. intros r.
        apply ent_ex_l. intros l1.
        apply ent_seq_ens_l. intros H.
        (* specialize (IH l1). forward IH. rewrite H. auto. *)
        rewrite IH; [ | subst; auto ].
        funfold foldr_env "f".
        apply ent_seq_ex_l. intros r0.
        apply ent_seq_ens_l. intros (?&?). subst r.
        simpl.
        apply ent_ex_r. exists (x + r0).
        apply ent_ens_single_pure.
        subst. intuition. } }
  Qed.

  (* Automated proof *)
  Lemma foldr_sum_auto:
    foldr_sum.
  Proof.
    unfold foldr_sum. intros xs. induction_wf IH: list_sub xs. intros.
    funfold foldr_env "foldr".
    simpl.
    solve_entailment.
  Qed.

  Fixpoint length (xs:list int) : int :=
    match xs with
    | nil => 0
    | _ :: ys => 1 + length ys
    end.

  Definition uncurried_plus_closure_spec : ufun := fun args rr =>
    match args with
    | vtup (vint a) (vint b) => fall (fun x => fall (fun c =>
        req (x~~>vint c) (ens_ (x~~>vint (c+1) \* \[rr = vint (a + b)]))
      ))
    | _ => empty
    end.

  Definition foldr_env1 :=
    Fmap.update
      (Fmap.single "foldr" (Some foldr))
        "f" (Some uncurried_plus_closure_spec).

  Definition foldr_sum_state := forall xs res,
    entails_under foldr_env1
      (unk "foldr" (vtup (vstr "f") (vtup (vint 0) (vlist xs))) res)
      (∀ x a, req (x~~>vint a)
        (∃ r, ens_ (x~~>vint (a+length (to_int_list xs)) \*
          \[res = vint r /\ r = sum (to_int_list xs)]))).

  Lemma foldr_sum_state_entailment:
    foldr_sum_state.
  Proof.
    unfold foldr_sum. intros xs. induction_wf IH: list_sub xs. intros.
    funfold foldr_env1 "foldr".
    simpl.
    ent_step.
    { apply ent_all_r. intros x.
      apply ent_all_r. intros a.
      apply ent_req_r.
      apply ent_ex_r. exists 0.
      rewrite norm_ens_ens_void_combine.
      apply ent_ens_single.
      xsimpl.
      { intros (?&?). subst. f_equal. simpl. math. }
      { intros (?&?). split. assumption. subst. reflexivity. } }
    { (* simple rewrites *)
      apply ent_ex_l. intros x.
      apply ent_ex_l. intros r.
      apply ent_ex_l. intros l1.
      apply ent_seq_ens_l. intros H.
      rewrite IH; [ | subst; auto ].
      funfold foldr_env1 "f".
      (* figure out what r is before we simpl *)

      (* match locations *)
      apply ent_all_r. intros x0.
      apply ent_seq_all_l. exists x0.
      apply ent_all_r. intros a.
      apply ent_seq_all_l. exists a.

      (* dispatch the req *)
      rewrite norm_reassoc.
      apply ent_req_req. xsimpl.

      (* move the pure constraints on r to the top,
        as we need them to simpl *)
      apply ent_seq_ex_l. intros r0.
      rewrite norm_ens_ens_void.
      rewrite norm_ens_ens_void_comm.
      rewrite <- norm_seq_assoc.
      apply ent_seq_ens_l. intros (?&?). subst r.

      (* we finally know what r is *)
      simpl.

      (* we need the locations to agree to use biab *)
      rewrite norm_forall.
      apply ent_all_l. exists x0.
      rewrite norm_forall.
      apply ent_all_l. exists (a + length (to_int_list l1)).
      rewrite norm_ens_req_transpose.
      2: { instantiate (1:=(fun _ => \[])).
        simpl.
        apply b_pts_single. }
      simpl.
      apply ent_req_l. reflexivity.
      norm.

      (* this existential is delayed all the way until the end *)
      apply ent_ex_r. exists (x + r0).
      apply ent_ens_single.
      xsimpl; intros; subst. simpl. f_equal. math. split; reflexivity. }
  Qed.

  Definition uncurried_plus_assert_spec : ufun := fun args rr =>
    match args with
    | vtup (vint x) (vint r) =>
        req \[x+r>=0] (ens_ \[rr=vint (x+r)])
    | _ => empty
    end.

  Fixpoint all_s_pos (xs:list int) : Prop :=
    match xs with
    | nil => True
    | y :: ys => sum xs >= 0 /\ all_s_pos ys
    end.

  Definition foldr_env2 :=
    Fmap.update
      (Fmap.single "foldr" (Some foldr))
        "f" (Some uncurried_plus_assert_spec).

  Lemma foldr_ex2: forall xs res,
    entails_under foldr_env2
      (unk "foldr" (vtup (vstr "f") (vtup (vint 0) (vlist xs))) res)
      (req \[all_s_pos (to_int_list xs)]
        (ens_ \[res = vint (sum (to_int_list xs))])).
  Proof.
    intros xs. induction_wf IH: list_sub xs. intros.
    funfold foldr_env2 "foldr".
    simpl.
    apply ent_disj_l.
    { apply ent_req_r.
      rewrite norm_ens_ens_void_combine.
      apply ent_ens_single.
      xsimpl. intros ? (?&?). subst. f_equal. }
    { apply ent_ex_l. intros x.
      apply ent_ex_l. intros r.
      apply ent_ex_l. intros l1.
      apply ent_seq_ens_l. intros H.
      rewrite IH; [ | subst; auto ].
      funfold foldr_env2 "f".

      apply ent_req_r.
      apply ent_seq_ens_l. intros H1.
      rewrite norm_reassoc.
      apply ent_req_l.
      { subst. simpl in H1. destruct H1. assumption. }

      apply ent_seq_ens_l. intros H2. subst r.
      simpl.
      apply ent_req_l.
      { subst xs. simpl in H1. destruct H1. assumption. }

      apply ent_ens_single.
      xsimpl.
      intros. subst.
      simpl. reflexivity. }
  Qed.

  Definition uncurried_plus_exc_spec : ufun := fun args rr =>
    match args with
    | vtup (vint x) (vint r) =>
      disj (ens_ \[x >= 0 /\ rr = vint (x + r)])
        (ens_ \[x < 0];; unk "exc" vunit vunit)
    | _ => empty
    end.

  Fixpoint all_pos (xs:list int) : Prop :=
    match xs with
    | nil => True
    | y :: ys => y >= 0 /\ all_pos ys
    end.

  Definition foldr_env3 :=
    Fmap.update
      (Fmap.single "foldr" (Some foldr))
        "f" (Some uncurried_plus_exc_spec).

  Lemma foldr_ex3: forall xs res,
    entails_under foldr_env3
      (unk "foldr" (vtup (vstr "f") (vtup (vint 0) (vlist xs))) res)
        (disj
          (ens_ \[all_pos (to_int_list xs) /\
            res = vint (sum (to_int_list xs))])
          (ens_ \[not (all_pos (to_int_list xs))];; unk "exc" vunit vunit)).
  Proof.
    intros xs. induction_wf IH: list_sub xs. intros.
    funfold foldr_env3 "foldr".
    simpl.
    apply ent_disj_l.
    { apply ent_disj_r_l.
      apply ent_ens_single.
      xsimpl. intros (?&?). subst. simpl. intuition. }
    { apply ent_ex_l. intros x.
      apply ent_ex_l. intros r.
      apply ent_ex_l. intros l1.
      apply ent_seq_ens_l. intros H.
      rewrite IH; [ | subst; auto ].
      funfold foldr_env3 "f".
      (* after rewriting with the IH, we have a disj on the left, because it's possible the recursive call raises an exception *)
      apply ent_seq_disj_l.
      { (* if the recursive call returns *)
        apply ent_seq_ens_l. intros (?&?).
        subst r. simpl.
        (* now we have 2 cases from the two branches in the call to f *)
        apply ent_disj_l.
        { apply ent_disj_r_l.
          apply ent_ens_single.
          xsimpl.
          intros (?&?).
          subst.
          split.
          simpl. intuition math.
          simpl. reflexivity. }
        { apply ent_disj_r_r.
          apply ent_seq_ens_l. intros (?&?).
          apply ent_seq_ens_r.
          { unfold not. intros. subst xs. simpl in H3. destr H3. math. }
          apply ent_unk_single. } }
      { (* if the recursive call raises *)
        apply ent_disj_r_r.
        rewrite <- norm_seq_assoc.
        apply ent_seq_ens_l. intros H1.
        apply ent_seq_ens_r.
        { unfold not. intros. subst xs. simpl in H0. destr H0. false. }
        (* it seems we can't finish this proof without a semantics for exceptions, as because the recursive call raises, we know nothing about r, and without the aforementioned semantics, we have no way to discard the call to f *)
        admit.
      }
  Abort.

End foldr.
