
From Staged Require Import Logic Automation.
Local Open Scope string_scope.

Example ex0:
  satisfies empty_env empty_heap empty_heap (norm (vint 1)) (req_ \[False]).
Proof.
  constructor. intros.
  hinv H.
  contradiction.
Qed.

Example ex0_heap: forall x,
  satisfies empty_env empty_heap empty_heap (norm (vint 1)) (req_ (x~~>vunit)).
Proof.
  constructor. intros.
  hinv H.
  symmetry in H0.
  pose proof (Fmap.union_eq_empty_inv_r H0).
  subst hp.
  (* H2 is false, but no lemmas to prove it *)
Abort.

Definition f1 : flow := ens (fun r => \[r=vint 1]).
Definition f2 : flow := fall (fun x => req_ (\[x = vint 1])).
Definition f3 : flow := f1 ;; f2.

Example ex1: satisfies empty_env empty_heap empty_heap (norm (vint 1)) f1.
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

Lemma ex1_req_ens_duality:
  entails (req_ \[False]) (ens_ \[False]).
Proof.
  unfold entails. intros.
  (* This is not provable *)
  inverts H as H.
  constructor.
Abort.

Lemma ex2_req_ens_duality:
  entails (ens_ \[False]) (req_ \[False]).
Proof.
  unfold entails. intros.
  constructor. intros.
  inverts H as H. destr H. hinv H0. hinv H. hinv H. hinv H7. subst. rew_fmap.
  apply empty_intro.
Abort.
