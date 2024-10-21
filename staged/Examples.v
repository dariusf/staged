
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
  hinv H0.
  (* use it to satisfy the req on the left *)
  inverts H as H.
  specialize (H hp hr).
  forward H. subst hp. hintro. math.
  specialize (H H1 H2).
  (* do the same for ens, but from left to right, as per normal *)
  inverts H as H. destr H. hinv H. hinv H. hinv H6.
  constructor. exists v. exists empty_heap.
  intuition.
  rewrite hstar_hpure_r.
  split. hintro; auto. math.
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
  { rewrite <- (hstar_hempty_r (x ~~> vint 2)).
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
    apply ens_void_pure_intro.
    injects H2. injects H1. f_equal. math. }
Qed.

Module hello.

  Definition hello : ufun := fun args res =>
    match args with
    | vtup (vstr f) (vtup (vloc x) (vloc y)) =>
      ∀ a, req (x~~>vint a) (ens_ (x~~>vint (a+1));;
      ∃ r, unk f (vloc y) (vint r);;
      ∀ b b1, req (x~~>vint b \* y~~>vint b1)
        (ens_ (x~~>vint b \* y~~>res \* \[res = vint (b+r)])))
    | _ => empty
    end.

  Definition hello_env (x y:loc) :=
    Fmap.update
      (Fmap.single "f"
        (Some (fun y r => ∀ b,
          req (x~~>vint b)
            (ens_ ((x~~>vint (b+1) \* \[r = vint 0]))))))
        "hello" (Some hello).

  (* [f] is allowed to capture [x] *)
  Lemma hello_capture : forall x y res,
    (* x <> y is implied by the precondition *)
    entails_under (hello_env x y)
      (unk "hello" (vtup (vstr "f") (vtup (vloc x) (vloc y))) res)
      (∀ a b, req (x~~>vint a \* y~~>vint b)
        (ens_ (x~~>vint (a+2) \* y~~>res \* \[res = vint (a+2)]))).
  Proof.
    intros x y res.
    funfold1 "hello".
    simpl.
    fintro a.
    fintro b.
    finst a.
    fassume.

    rewrite (norm_ens_req_transpose).
    2: { 
      rewrite <- (hstar_hempty_r (x~~>vint a)) at 2.
      apply b_pts_match.
      apply b_base_empty.
    }

    (* norm. *)
    (* prove trivial reqs *)
    rewrite hstar_hempty_r.
    apply ent_req_l. reflexivity.

    (* combine everything into the SL context *)
    rewrite norm_seq_assoc.
    rewrite norm_ens_ens_void_combine.

    (* rewrite under the existential *)
    rewrites (>> ent_ex_seq_unk (hello_env x y)).
    { unfold hello_env. resolve_fn_in_env. }
    simpl.

    (* intro the existential, and specialize the forall *)
    fintro v.
    rewrite norm_seq_all_reassoc.
    finst (a + 1).
    rewrite norm_reassoc.

    rewrite (norm_ens_req_transpose).
    2: { 
      rewrite hstar_comm.
      rewrite <- (hstar_hempty_r (x~~>vint (a + 1))) at 2.
      apply b_pts_match.
      apply b_base_empty.
    }

    (* norm *)
    rewrite hstar_hempty_r. apply ent_req_l. reflexivity.

    (* move the pure assumption up... *)
    rewrite norm_ens_ens_void_split.
    rewrite norm_seq_assoc.
    rewrite norm_seq_assoc.
    rewrite norm_ens_ens_void_combine.
    rewrite norm_ent_ent_pure_comm.
    rewrite <- norm_seq_assoc.
    fassume H.

    (* instantiate before biabduction *)
    finst (a + 2).
    finst b.

    rewrite norm_ens_req_transpose.
    2: {
      rewrite hstar_comm.
      apply b_pts_match.
      apply b_pts_single.
    }

    (* dispatch trivial req again *)
    rewrite hstar_hpure_conj.
    apply ent_req_l.
    { split. f_equal. math. reflexivity. }
    rewrite norm_seq_ens_empty.

    (* close *)
    apply ent_ens_single.
    injects H.
    xsimpl.
    intros. rewrite H. f_equal. math.
  Qed.

  (* Suppose we have a hello that does not release x,
     and it is called with an f that captures x *)
  Definition hello1 : ufun := fun args res =>
    match args with
    | vtup (vstr f) (vtup (vloc x) (vloc y)) =>
      ∀ a, req (x~~>vint a)
      (∃ r, unk f (vloc y) (vint r);;
      ∀ b1, req (y~~>vint b1)
        (ens_ (x~~>vint (a+1) \* y~~>res \* \[res = vint (a+1+r)])))
    | _ => empty
    end.

  (* same as before except for using hello1 *)
  Definition hello_env1 (x y:loc) :=
    Fmap.update
      (Fmap.single "f"
        (Some (fun y r => ∀ b,
          req (x~~>vint b)
            (ens_ ((x~~>vint (b+1) \* \[r = vint 0]))))))
        "hello" (Some hello1).

  (* the proof should not go through *)
  Lemma hello_capture1 : forall x y res,
    entails_under (hello_env1 x y)
      (unk "hello" (vtup (vstr "f") (vtup (vloc x) (vloc y))) res)
      (∀ a b, req (x~~>vint a \* y~~>vint b)
        (ens_ \[True])).
  Proof.
    intros.
    fintro a.
    fintro b.
    fassume.
    funfold1 "hello". simpl.
    finst a.

    rewrite norm_ens_req_transpose.
    2: {
      (* rewrite hstar_comm. *)
      rewrite <- (hstar_hempty_r (x ~~> vint a)) at 2.
      apply b_pts_match.
      apply b_base_empty.
    }

    (* norm *)
    rewrite hstar_hempty_r.
    apply ent_req_l. reflexivity.

    rewrites (>> ent_ex_seq_unk (hello_env1 x y) "f").
    { unfold hello_env1. resolve_fn_in_env. }
    simpl.
    fintro v.
    (* f cannot capture x *)
  Abort.

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
        constructor. exists 0.
        subst. apply ens_void_pure_intro.
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

        constructor. exists (x + v).
        subst. apply ens_void_pure_intro.
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
      2: { apply b_pts_single. }
      simpl.
      apply ent_req_l. reflexivity.
      norm.

      (* this existential is delayed all the way until the end *)
      apply ent_ex_r. exists (x + r0).
      apply ent_ens_single.
      xsimpl; intros; subst. simpl. f_equal. math. split; reflexivity. }
  Qed.

  (* Examples *)

  (* specialized to int list for simplicity *)
  Fixpoint IsList (L:list val) (p:loc) : hprop :=
    match L with
    | nil => \[p = null]
    | (vint x)::L' => \[p <> null] \*
      \exists q, (p ~~> vtup (vint x) (vloc q) \* (IsList L' q))
    | _ => \[False]
    end.

  Lemma IsList_nil : forall p,
    (IsList nil p) = \[p = null].
  Proof using. auto. Qed.

  Lemma IsList_cons : forall p x L',
    IsList (vint x::L') p =
    \[p <> null] \* \exists q, (p ~~> (vtup (vint x) (vloc q))) \* (IsList L' q).
  Proof using. auto. Qed.

  Lemma IsList_if : forall (p:loc) (L:list val),
        (IsList L p)
    ==> (If p = null
          then \[L = nil]
          else \[p <> null] \* \exists x q L', \[L = vint x::L']
              \* (p ~~> (vtup (vint x) (vloc q))) \* (IsList L' q)).
  Proof.
    intros p xs.
    destruct xs.
    { xchange IsList_nil.
      intros ->.
      case_if.
      xsimpl. reflexivity. }
    {
      destruct v;
        match goal with
        | |- IsList (vint _ :: _) _ ==> _ => idtac
        | _ => simpl; xsimpl
        end.
      rewrite IsList_cons.
      xpull. intros H q.
      case_if. (* absurd case eliminated *)
      xsimpl. assumption.
      reflexivity. }
  Qed.

  (* Instead of taking a pure list, this takes a location *)
  Definition foldr_mut : ufun := fun (args:val) rr =>
    match args with
    | vtup (vstr f) (vtup (vint a) (vloc l) (* list->loc *)) =>
      disj
        (ens_ \[rr = vint a /\ l = null (* nil->null *)])
        (* must know l is not null to work with a shape predicate *)
        (ens_ \[l <> null];; (
          ∀ l1, (* to be instantiated from the shape pred, analogous to the ∀ over the argument l in the pure version *)
          ∃ r, unk "foldr" (vtup (vstr f) (vtup (vint a) (vloc l1))) r;;
          unk f (vtup (vloc l) r) rr))
    | _ => empty
    end.

  Fixpoint mapinc (xs:list int) : list int :=
    match xs with
    | nil => nil
    | y :: ys => (y+1) :: mapinc ys
    end.

  Definition uncurried_plus_mut_spec : ufun := fun args res =>
    match args with
    | vtup (vloc a) (vint b) => ∀ c l,
        req (a~~>vtup (vint c) (vloc l))
          (ens_ (a~~>vtup (vint (c+1)) (vloc l) \*
            \[res = vint (c + b)]))
    | _ => empty
    end.

  Definition foldr_env0 :=
    Fmap.update
      (Fmap.single "foldr" (Some foldr_mut))
        "f" (Some uncurried_plus_mut_spec).

  Lemma foldr_ex0: forall xs res l,
    entails_under foldr_env0
      (unk "foldr" (vtup (vstr "f") (vtup (vint 0) (vloc l))) res)
      (req (IsList xs l)
        (∃ ys, ens_ (IsList ys l \*
          \[res = vint (sum (to_int_list xs)) /\
            to_int_list ys = mapinc (to_int_list xs)]))).
  Proof.
    intros xs. induction_wf IH: list_sub xs. intros.
    funfold1 "foldr".
    simpl.
    apply ent_disj_l.
    { fassume (?&?).
      subst.
      fassume.
      rewrite norm_ens_empty_r.
      finst (@nil val).
      apply ent_ens_single.
      xchange IsList_if.
      case_if.
      xsimpl.
      intros ->.
      split.
      f_equal.
      reflexivity.
      simpl.
      xsimpl.
      reflexivity. }
    { fassume.
      rewrites (>> entails_ens_void IsList_if).
      case_if.
      { fassume H1.
        fassume H2.
        false. }
      rewrite norm_ens_ens_void_split.
      rewrite <- norm_seq_assoc.
      fassume H1.
      fintro x.
      fintro q.
      fintro L'.
      rewrite norm_ens_ens_void_split.
      rewrite <- norm_seq_assoc.
      fassume H2.
      rewrite norm_seq_assoc.
      rewrite norm_ent_ent_pure_comm.
      rewrite <- norm_seq_assoc.
      fassume H3.
      finst q.
      fintro r.
      rewrite IH; [ | subst; auto ].
      rewrite norm_seq_assoc.
      rewrite (norm_ens_req_transpose).
      2: {
        rewrite hstar_comm.
        rewrite <- (hstar_hempty_r (IsList L' q)) at 2.
        apply b_any_match.
        apply b_base_empty.
      }

      rewrite norm_reassoc.
      apply ent_req_emp_l.
      rewrite norm_seq_ex_reassoc_ctx.
      rewrite norm_seq_ex_reassoc.
      fintro ys.
      rewrite norm_ens_ens_void_split.
      rewrite norm_ens_ens_void_comm.
      rewrite norm_seq_assoc.
      rewrite norm_ens_ens_void_comm.
      rewrite <- norm_seq_assoc.
      rewrite <- norm_seq_assoc.
      fassume (?&?).
      rewrite norm_seq_assoc.
      rewrite norm_ens_ens_void_combine.

      (* figure out what foldr returns first *)
      funfold1 "f".
      subst r.
      simpl.
      finst x.
      finst q.

      rewrite (norm_ens_req_transpose).
      2: {
        rewrite <- (hstar_hempty_r (l ~~> vtup (vint x) (vloc q))) at 2.
        apply b_pts_match.
        apply b_base_empty.
      }

      rewrite hstar_hempty_r.
      apply ent_req_l. reflexivity.

      rewrite norm_ens_ens_void_combine.
      finst (vint (x+1)::ys).
      apply ent_ens_single.
      xsimpl.
      { intros ->.
        split.
        { subst xs.
          simpl.
          reflexivity. }
        { subst xs.
          simpl.
          rewrite <- H0.
          reflexivity. } }
      { intros ->.
        xchange <- IsList_cons.
        assumption. }
    }
  Qed.

  (* Example 2 *)

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
