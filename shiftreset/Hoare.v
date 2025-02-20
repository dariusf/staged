
From ShiftReset Require Import Logic.
Local Open Scope string_scope.

(** * Big-step semantics *)
Inductive eresult : Type :=
  | enorm : val -> eresult.

(** Program environment *)
#[global]
Instance Inhab_val_expr : Inhab (val -> expr).
Proof.
  constructor.
  exists (fun v => pval v).
  constructor.
Qed.

Definition penv := Fmap.fmap var (val -> expr).
Definition empty_penv : penv := Fmap.empty.

Implicit Types Re : eresult.
Implicit Types p : penv.

Definition flow_res (f:flow) (v:val) : Prop :=
  forall s1 s2 h1 h2 R, satisfies s1 s2 h1 h2 R f -> R = norm v.

Inductive bigstep : penv -> penv -> heap -> expr -> heap -> eresult -> Prop :=
  | eval_pval : forall h v p,
    bigstep p p h (pval v) h (enorm v)

  (* there is no var rule *)

  | eval_plet : forall h1 h3 h2 x e1 e2 v Re p1 p2 p3,
    bigstep p1 p3 h1 e1 h3 (enorm v) ->
    bigstep p3 p2 h3 (subst x v e2) h2 Re ->
    bigstep p1 p2 h1 (plet x e1 e2) h2 Re

  | eval_padd : forall h x y p p,
    bigstep p p h (padd (pval (vint x)) (pval (vint y))) h (enorm (vint (x + y)))

  | eval_pminus : forall h x y p p,
    bigstep p p  h (pminus (pval (vint x)) (pval (vint y))) h (enorm (vint (x - y)))

  | eval_pfun : forall h x e p p,
    bigstep p p h (pfun x e) h (enorm (vfun x e))

  | eval_pfix : forall h x e xf p p,
    bigstep p p h (pfix xf x e) h (enorm (vfix xf x e))

  | eval_app_fun : forall v1 v2 h x e Re p p p,
    v1 = vfun x e ->
    bigstep p p h (subst x v2 e) h Re ->
    bigstep p p h (papp (pval v1) (pval v2)) h Re

  | eval_app_fix : forall v1 v2 h x e Re xf p p,
    v1 = vfix xf x e ->
    bigstep p p h (subst x v2 (subst xf v1 e)) h Re ->
    bigstep p p h (papp (pval v1) (pval v2)) h Re

  | eval_app_unk : forall va h Re efn xf p p,
    Fmap.read p xf = efn ->
    bigstep p p h (efn va) h Re ->
    bigstep p p h (papp (pvar xf) (pval va)) h Re

  | eval_pif_true : forall h1 h2 Re e1 e2 p p,
    bigstep p p h1 e1 h2 Re ->
    bigstep p p h1 (pif (pval (vbool true)) e1 e2) h2 Re

  | eval_pif_false : forall h1 h2 Re e1 e2 p p,
    bigstep p p h1 e2 h2 Re ->
    bigstep p p h1 (pif (pval (vbool false)) e1 e2) h2 Re

  | eval_pref : forall h v l p p,
    ~ Fmap.indom h l ->
    bigstep p p h (pref (pval v)) (Fmap.update h l v) (enorm (vloc l))

  | eval_pderef : forall h l p p,
    Fmap.indom h l ->
    bigstep p p h (pderef (pval (vloc l))) h (enorm (Fmap.read h l))

  | eval_passign : forall h l v p p,
    Fmap.indom h l ->
    bigstep p p h (passign (pval (vloc l)) (pval v)) (Fmap.update h l v) (enorm vunit)

  | eval_passert : forall h p p,
    bigstep p p h (passert (pval (vbool true))) h (enorm vunit).

(* TODO is a rule for function pointers needed? *)

Module Soundness.

  (** * Specification assertions *)
  (** A #<i>specification assertion</i># is our equivalent of a (semantic) Hoare triple: a valid one ensures ensures that the given program satisfies the given specification. *)
  Definition pair_valid_under p1 s1 e f : Prop :=
    forall h1 h2 v p2 s2,
      bigstep p1 p2 h1 e h2 (enorm v) -> satisfies s1 s2 h1 h2 (norm v) f.

(* TODO do we need to update the env due to fptrs? *)

  (** Roughly, this says that for every binding in the program environment, we can find a "corresponding" one in the spec environment, where "corresponding" means related by a valid specification assertion. *)
  Definition env_compatible p1 s1 :=
    forall pfn xf x,
      Fmap.read p1 xf = pfn ->
      exists sfn, Fmap.read s1 xf = sfn /\
      forall v, pair_valid_under p1 s1 (pfn x) (sfn x v).

  (** The full definition requires compatible environments. *)
  Definition spec_assert (e: expr) (f: flow) : Prop :=
    forall p1 p2 s1 s2,
      env_compatible p1 s1 ->
      env_compatible p2 s2 ->
      pair_valid_under p1 s1 e f.

  #[global]
  Instance Proper_spec_assert : Proper
    (eq ====> entails ====> impl)
    spec_assert.
  Proof.
    unfold entails, Proper, respectful, impl, spec_assert, pair_valid_under.
    intros. subst.
    specializes H1 H2 H3 h1 h2 v.
  Qed.

  (** Structural rules *)
  Lemma sem_consequence : forall f1 f2 e,
    entails f1 f2 ->
    spec_assert e f1 ->
    spec_assert e f2.
  Proof.
    introv He H.
    unfold spec_assert. intros.
    rewrite He in H.
    eauto.
  Qed.

  (** Rules for program constructs *)
  Lemma sem_pval: forall n,
    spec_assert (pval n) (ens (fun res => \[res = n])).
  Proof.
    unfold spec_assert, pair_valid_under. intros.
    (* appeal to how e executes to tell us about the heaps *)
    inverts H1 as H1.
    (* justify that the staged formula describes the heap *)
    apply ens_pure_intro.
    reflexivity.
  Qed.

  Lemma sem_plet: forall x e1 e2 f1 f2 v,
    spec_assert e1 f1 ->
    flow_res f1 v ->
    spec_assert (subst x v e2) f2 ->
    spec_assert (plet x e1 e2) (f1;; f2).
  Proof.
    intros.
    unfold spec_assert, pair_valid_under. intros.
    (* exists s1. *)
    exs.
    intros Hb.

    (* reason about how the let executes *)
    inverts Hb as. introv He1 He2.

    (* use the specification assertion we have about e1 *)
    (* unfold spec_assert, pair_valid_under in H. *)
    lets: H H2 H3 h1 h3 v1. destr H4. specializes H4 He1.
    specializes H0 H4. injects H0.

    (* unfold spec_assert, pair_valid_under in H1. *)
    specializes H1 H2 h3 h2 v0. destr H1. specializes H0 He2.


    (* exact Hc. clear H He1. sort. *)

    (* we need to know that spec value and program value are the same *)
    (* specializes H0 H3. subst. *)
    (* injects H0. *)

    (* know about f2 *)
    (* specializes H1 env h3 h2 v0 He2. clear He2. *)

    applys* s_seq.
    apply H0.

  Qed.

  Lemma sem_pif: forall b e1 e2 f1 f2,
    spec_assert e1 f1 ->
    spec_assert e2 f2 ->
    spec_assert (pif (pval (vbool b)) e1 e2) (disj
      (ens_ \[b = true];; f1)
      (ens_ \[b = false];; f2)).
  Proof.
    introv Ht Hf.
    unfold spec_assert. introv Hc Hb.
    inverts Hb as Hb.
    { (* true *)
      unfold spec_assert in Ht.
      specializes Ht env Hb.
      apply s_disj_l.
      eapply s_seq.
      apply ens_void_pure_intro. reflexivity.
      assumption. }
    { (* false *)
      unfold spec_assert in Hf.
      specializes Hf env Hb.
      apply s_disj_r.
      eapply s_seq.
      apply ens_void_pure_intro. reflexivity.
      assumption. }
  Qed.

  Lemma sem_pif_ignore_cond: forall b e1 e2 f1 f2,
    spec_assert e1 f1 ->
    spec_assert e2 f2 ->
    spec_assert (pif b e1 e2) (disj f1 f2).
  Proof.
    introv Ht Hf.
    unfold spec_assert. introv Hc Hb.
    inverts Hb as Hb.
    { (* true *)
      unfold spec_assert in Ht.
      specializes Ht env Hb.
      now apply s_disj_l. }
    { (* false *)
      unfold spec_assert in Hf.
      specializes Hf env Hb.
      now apply s_disj_r. }
  Qed.

  Lemma sem_pderef: forall x,
    spec_assert (pderef (pval (vloc x)))
      (fall (fun y => (req (x~~>y)
        (ens (fun res => \[res = y] \* x~~>y))))).
  Proof.
    intros. unfold spec_assert. introv Hc Hb.
    inverts Hb as Hb.
    constructor. intros v.
    constructor. intros.
    constructor. exists v. exists hp.
    intuition.
    { f_equal.
      apply hsingle_inv in H.
      rewrite H in H1.
      subst.
      rewrite Fmap.union_comm_of_disjoint; auto.
      rewrite Fmap.read_union_l.
      apply Fmap.read_single.
      apply Fmap.indom_single. }
    { rewrite hstar_hpure_l.
      intuition. }
  Qed.

  Lemma sem_pref: forall v,
    spec_assert (pref (pval v)) (fex (fun y =>
      (ens (fun r => \[r = vloc y] \* y~~>v)))).
  Proof.
    intros.
    unfold spec_assert. introv Hc Hb.
    inverts Hb as Hb.
    constructor. exists p.
    constructor. exists (vloc p). exists (Fmap.single p v).
    forwards H1: Fmap.disjoint_single_of_not_indom h1 p v.
    { unfold not. exact Hb. }

    intuition.
    { rewrite hstar_hpure_l.
      intuition.
      apply hsingle_intro. }
    { rewrite Fmap.union_comm_of_disjoint; only 2: auto.
      apply Fmap.update_eq_union_single. }
  Qed.

  Lemma sem_passign: forall x y v,
    spec_assert (passign (pval (vloc x)) (pval y))
      (req (x~~>v) (ens_ (x~~>y))).
  Proof.
    intros.
    unfold spec_assert. introv Hc Hb.
    inverts Hb as Hb.
    constructor. intros.
    constructor. exists vunit. exists (Fmap.update hp x y).

    (* the heap reasoning is most of this *)
    intuition.

    { rewrite hstar_hpure_l. intuition.
      apply hsingle_inv in H.
      rewrite H.
      rewrite Fmap.update_single.
      apply hsingle_intro. }

    { rewrite H0.
      apply hsingle_inv in H.
      rewrite H.
      rewrites* Fmap.update_union_r.
      { rewrite H in H1.
        unfold not; applys Fmap.disjoint_inv_not_indom_both (Fmap.single x v) hr.
        - fmap_disjoint.
        - apply Fmap.indom_single. } }

    { apply Fmap.disjoint_sym.
      applys Fmap.disjoint_update_l.
      fmap_disjoint.
      apply hsingle_inv in H.
      rewrite H.
      apply Fmap.indom_single. }
  Qed.

  Lemma sem_passert: forall b,
    spec_assert (passert (pval (vbool b))) (req_ \[b = true]).
  Proof.
    intros.
    unfold spec_assert. introv Hc Hb.
    inverts Hb as Hb.
    constructor.
    intros.
    apply hpure_inv in H. destruct H. rewrite H2 in H0. rew_fmap. rewrite H0.
    apply empty_intro.
  Qed.

  Lemma sem_papp_fun: forall vf x e va f,
    vf = vfun x e ->
    spec_assert (subst x va e) f ->
    spec_assert (papp (pval vf) (pval va)) f.
  Proof.
    intros. subst.
    unfold spec_assert. introv Hc Hb.
    inverts Hb as.
    { introv H Hb.
      injection H; intros; subst e0 x0; clear H.
      unfold spec_assert in H0.
      specializes H0 env Hb. }
    { intros. false. }
  Qed.

  Lemma sem_papp_fix: forall vf x e va f xf,
    vf = vfix xf x e ->
    spec_assert (subst x va (subst xf vf e)) f ->
    spec_assert (papp (pval vf) (pval va)) f.
  Proof.
    intros. subst.
    unfold spec_assert. introv Hc Hb.
    inverts Hb as.
    { intros. false. }
    { introv H Hb. injection H; intros; subst e0 x0 xf0; clear H.
      unfold spec_assert in H0.
      specializes H0 env Hb. }
  Qed.

  Lemma sem_papp_unk: forall xf va,
    spec_assert (papp (pvar xf) (pval va)) (fex (fun r => unk xf va r)).
  Proof.
    intros.
    unfold spec_assert. introv Hc Hb.
    inverts Hb.
    constructor. exists v.
    unfold env_compatible in Hc. specializes Hc va ___. destr Hc.
    eapply s_unk. { exact H0. }
    specializes H1 v H6.
  Qed.

  Local Notation derivable := forward.
  Local Notation valid := spec_assert.

  (** * Soundness *)
  Theorem soundness : forall e f,
    derivable e f -> valid e f.
  Proof.
    introv H.
    induction H.
    - apply sem_pval.
    - eapply sem_plet; eauto.
    - apply sem_pif; auto.
    - apply sem_pderef.
    - apply sem_pref.
    - apply sem_passign.
    - apply sem_passert.
    - eapply sem_papp_fun; eauto.
    - eapply sem_papp_fix; eauto.
    - eapply sem_papp_unk.
  Qed.

End Soundness.

Module HistoryTriples.

  Import Soundness.

  (** * History triples *)
  (** A #<i>history triple</i># (i.e. not just a "triple", which typically refers to a Hoare triple) also constrains the history of a program. *)
  (* 
      h0 ╶─[fh]──▶ h1 ╶─[e]──▶ h2
      ╷                        ▲
      └───────────[f]──────────┘
  *)
  Definition hist_triple fh e f :=
    forall penv env h0 h1 h2 v R,
      satisfies env h0 h1 R fh ->
      env_compatible penv env ->
      bigstep penv h1 e h2 (enorm v) ->
      satisfies env h0 h2 (norm v) f.

  (** History triples are contravariant in the history. *)
  #[global]
  Instance Proper_hist_triple : Proper
    (flip entails ====> eq ====> entails ====> impl)
    hist_triple.
  Proof.
    unfold entails, Proper, respectful, impl, hist_triple, flip.
    intros. subst.
    apply H1.
    applys H2.
    apply H.
    exact H3.
    exact H4.
    exact H5.
  Qed.

  #[global]
  Instance Proper_hist_triple_bi : Proper
    (bientails ====> eq ====> bientails ====> impl)
    hist_triple.
  Proof.
    unfold entails, Proper, respectful, impl, hist_triple, flip.
    intros. subst.
    apply H1.
    applys H2.
    apply H.
    exact H3.
    exact H4.
    exact H5.
  Qed.

  (** Structural rules *)
  Lemma hist_conseq : forall f1 f2 f3 f4 e,
    entails f1 f3 ->
    entails f4 f2 ->
    hist_triple f3 e f4 ->
    hist_triple f1 e f2.
  Proof.
    unfold hist_triple. introv He1 He2 H. introv Hf1 Hc.
    rewrite He1 in Hf1.
    specializes H Hf1 Hc.
  Qed.

  Lemma hist_frame : forall fh fr f e,
    hist_triple fh e f ->
    hist_triple (fr;; fh) e (fr;; f).
  Proof.
    unfold hist_triple. introv H. intros.
    inverts H0 as H0. destr H0.
    applys* s_seq.
  Qed.

  Lemma hist_sem : forall f e,
    spec_assert e f <->
    hist_triple empty e f.
  Proof.
    iff H.
    { unfold hist_triple. intros.
      apply empty_inv in H0. destruct H0. subst h0.
      unfold spec_assert, pair_valid_under in H.
      specializes H H1 H2. }
    { unfold spec_assert, pair_valid_under. intros.
      unfold hist_triple in H.
      applys H.
      apply empty_intro.
      apply H0.
      assumption. }
  Qed.

  (** The (arbitrary) result of the history does not matter, enabling this rewriting. *)
  Lemma hist_pre_result : forall fh f e,
    hist_triple (fh;; empty) e f ->
    hist_triple fh e f.
  Proof.
    unfold hist_triple.
    introv H. intros.
    eapply H.
    - applys s_seq. eassumption. apply empty_intro.
    - eassumption.
    - assumption.
  Qed.

  (** History triples which only append to history can be derived directly from the history-frame rule. *)
  Lemma hist_frame_sem: forall fh e f,
    spec_assert e f ->
    hist_triple fh e (fh;; f).
  Proof.
    intros.
    apply hist_sem in H.
    lets H3: hist_frame fh H. clear H.
    apply hist_pre_result in H3.
    exact H3.
  Qed.

  (** Rules for program constructs *)
  Lemma hist_pval: forall n fh,
    hist_triple fh (pval n) (fh;; ens (fun res => \[res = n])).
  Proof.
    unfold hist_triple. introv Hh Hc Hb.
    applys s_seq h1 R.
    assumption.
    lets H: sem_pval n Hc.
    unfold pair_valid_under, spec_assert in H.
    apply H; auto.
  Qed.

  Remark hist_pval_via_frame: forall n fh,
    hist_triple fh (pval n) (fh;; ens (fun res => \[res = n])).
  Proof.
    intros.
    applys hist_frame_sem (@sem_pval n).
  Qed.

  Lemma hist_pref: forall v fh,
    hist_triple fh (pref (pval v))
      (fh;; fex (fun y =>(ens (fun r => \[r = vloc y] \* y ~~> v)))).
  Proof.
    intros.
    applys hist_frame_sem (@sem_pref v).
  Qed.

  Lemma hist_pderef: forall x fh,
    hist_triple fh (pderef (pval (vloc x)))
      (fh;; fall (fun y =>
        req (x ~~> y) (ens (fun res => \[res = y] \* x ~~> y)))).
  Proof.
    intros.
    applys hist_frame_sem (@sem_pderef x).
  Qed.

  Lemma hist_passign: forall x y v fh,
    hist_triple fh (passign (pval (vloc x)) (pval y))
      (fh;; req (x ~~> v) (ens_ (x ~~> y))).
  Proof.
    intros.
    applys hist_frame_sem (@sem_passign x).
  Qed.

  Lemma hist_passert: forall fh b,
    hist_triple fh (passert (pval (vbool b))) (fh;; req_ \[b = true]).
  Proof.
    intros.
    applys hist_frame_sem (@sem_passert b).
  Qed.

  Lemma hist_pif: forall fh b e1 e2 f1 f2,
    hist_triple (fh;; ens_ \[b = true]) e1 f1 ->
    hist_triple (fh;; ens_ \[b = false]) e2 f2 ->
    hist_triple fh (pif (pval (vbool b)) e1 e2) (disj f1 f2).
  Proof.
    introv He1 He2.
    unfold hist_triple. intros.
    destruct b.
    { forwards: He1.
      { applys s_seq h1 R.
        exact H.
        pose proof (ens_void_pure_intro).
        apply ens_void_pure_intro.
        reflexivity. }
      { exact H0. }
      { inverts H1 as H1. exact H1. }
      apply s_disj_l. assumption. }

    { forwards: He2.
      { applys s_seq h1 R.
        exact H.
        pose proof (ens_void_pure_intro).
        apply ens_void_pure_intro.
        reflexivity. }
      { exact H0. }
      { inverts H1 as H1. exact H1. }
      apply s_disj_r. assumption. }
  Qed.

  (* TODO alternative formulation of if, which appends only *)
  (* TODO sem_pif should treat conditions more precisely first *)

  Lemma hist_papp_fun: forall vf x e va f fh,
    vf = vfun x e ->
    hist_triple fh (subst x va e) f ->
    hist_triple fh (papp (pval vf) (pval va)) f.
  Proof.
    intros. subst.
    unfold hist_triple. intros.
    inverts H2 as H2.
    { injects H2.
      unfold hist_triple in H0.
      specializes H0 H H1 H9. }
    { false. }
  Qed.

  Lemma hist_papp_fix: forall vf x e va f xf fh,
    vf = vfix xf x e ->
    hist_triple fh (subst x va (subst xf vf e)) f ->
    hist_triple fh (papp (pval vf) (pval va)) f.
  Proof.
    intros. subst.
    unfold hist_triple. intros.
    inverts H2 as H2.
    { false. }
    { injects H2.
      unfold hist_triple in H0.
      specializes H0 H H1 H9. }
  Qed.

  Lemma hist_papp_unk: forall xf va fh,
    hist_triple fh (papp (pvar xf) (pval va))
      (fh;; fex (fun r => unk xf va r)).
  Proof.
    intros.
    applys hist_frame_sem fh (@sem_papp_unk xf va).
  Qed.

  Lemma hist_plet: forall fh e1 f1 e2 f2 v x,
    hist_triple fh e1 f1 ->
    flow_res f1 v ->
    hist_triple f1 (subst x v e2) f2 ->
    hist_triple fh (plet x e1 e2) f2.
  Proof.
    introv He1 Hres He2.
    unfold hist_triple. introv Hfh Hc Hb.

    (* reason about how let executes, as the composition of e1 and e2 *)
    inverts Hb as. introv Hb1 Hb2.

    (* reason about the execution of e1 *)
    unfold hist_triple in He1.
    specializes He1 Hfh Hc Hb1.

    (* reason about the result of e1 *)
    specializes Hres He1. subst.
    injects Hres.

    (* reason about the execution of e2 *)
    unfold hist_triple in He2.
    specializes He2 He1 Hc.
  Qed.

End HistoryTriples.
