
From ShiftReset Require Import Logic.
Local Open Scope string_scope.
(* Require Import Coq.Program.Equality. *)

(** * Big-step semantics *)
Inductive eresult : Type :=
  | enorm : val -> eresult
  | eshft : val -> val -> eresult.

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

Definition flow_res1 (f:flow) (v:val) : Prop :=
  forall s1 s2 h1 h2 R,
  satisfies s1 s2 h1 h2 R f ->
  match R with
  | norm v1 => v = v1
  | shft _ _ v1 _ => v = v1
  end.

Inductive bigstep : penv -> heap -> expr -> heap -> eresult -> Prop :=
  | eval_pval : forall h v p,
    bigstep p h (pval v) h (enorm v)

  (* there is no var rule *)

  | eval_plet : forall h1 h3 h2 x e1 e2 v Re p1,
    bigstep p1 h1 e1 h3 (enorm v) ->
    bigstep p1 h3 (subst x v e2) h2 Re ->
    bigstep p1 h1 (plet x e1 e2) h2 Re

  | eval_plet_sh : forall x e1 e2 h1 h2 p1 x1 x2 xy xtmp eb ek,
    bigstep p1 h1 e1 h2 (eshft (vfun x1 eb) (vfun x2 ek)) ->
    bigstep p1 h1 (plet x e1 e2) h2
      (eshft (vfun x1 eb)
        (vfun xy (plet xtmp (papp (pval (vfun x2 ek)) (pvar xy))
          (plet x (pvar xtmp) e2))))

  | eval_padd : forall h x y p,
    bigstep p h (padd (pval (vint x)) (pval (vint y))) h (enorm (vint (x + y)))

  | eval_pminus : forall h x y p,
    bigstep p  h (pminus (pval (vint x)) (pval (vint y))) h (enorm (vint (x - y)))

  | eval_pfun : forall h x e p,
    bigstep p h (pfun x e) h (enorm (vfun x e))

  | eval_pfix : forall h x e xf p,
    bigstep p h (pfix xf x e) h (enorm (vfix xf x e))

  | eval_app_fun : forall v1 v2 h x e Re p p,
    v1 = vfun x e ->
    bigstep p h (subst x v2 e) h Re ->
    bigstep p h (papp (pval v1) (pval v2)) h Re

  | eval_app_fix : forall v1 v2 h x e Re xf p,
    v1 = vfix xf x e ->
    bigstep p h (subst x v2 (subst xf v1 e)) h Re ->
    bigstep p h (papp (pval v1) (pval v2)) h Re

  | eval_app_unk : forall va h Re efn xf p,
    Fmap.read p xf = efn ->
    bigstep p h (efn va) h Re ->
    bigstep p h (papp (pvar xf) (pval va)) h Re

  | eval_pif_true : forall h1 h2 Re e1 e2 p,
    bigstep p h1 e1 h2 Re ->
    bigstep p h1 (pif (pval (vbool true)) e1 e2) h2 Re

  | eval_pif_false : forall h1 h2 Re e1 e2 p,
    bigstep p h1 e2 h2 Re ->
    bigstep p h1 (pif (pval (vbool false)) e1 e2) h2 Re

  | eval_pref : forall h v l p,
    ~ Fmap.indom h l ->
    bigstep p h (pref (pval v)) (Fmap.update h l v) (enorm (vloc l))

  | eval_pderef : forall h l p,
    Fmap.indom h l ->
    bigstep p h (pderef (pval (vloc l))) h (enorm (Fmap.read h l))

  | eval_passign : forall h l v p,
    Fmap.indom h l ->
    bigstep p h (passign (pval (vloc l)) (pval v)) (Fmap.update h l v) (enorm vunit)

  | eval_passert : forall h p,
    bigstep p h (passert (pval (vbool true))) h (enorm vunit)

  | eval_pshift : forall h p k eb,
    bigstep p h (pshift k eb) h
      (eshft (vfun k eb) (vfun "x" (preset (pvar "x"))))

  | eval_preset_val : forall h1 h2 p e v,
    bigstep p h1 e h2 (enorm v) ->
    bigstep p h1 (preset e) h2 (enorm v)

  | eval_preset_sh : forall h1 h2 h3 R p e x1 x2 eb ek,
    bigstep p h1 e h3 (eshft (vfun x1 eb) (vfun x2 ek)) ->
    bigstep p h3 ((* non-0 *) (subst x1 (vfun x2 ek) eb)) h2 R ->
    bigstep p h1 (preset e) h2 R

  .

(* TODO is a rule for function pointers needed? *)

Module SpecAssertions.

  Definition expr_shift_free e :=
    forall p1 h1 h2 v1 v2, bigstep p1 h1 e h2 (eshft v1 v2) -> False.

  Definition expr_res e v :=
    forall p1 h1 h2 r, bigstep p1 h1 e h2 (enorm r) -> v = r.

  Lemma sf_pval : forall v,
    expr_shift_free (pval v).
  Proof.
    unfold expr_shift_free. intros.
    inverts H as H.
  Qed.

  Lemma sf_plet : forall x e1 e2 r,
    expr_shift_free e1 ->
    expr_res e1 r ->
    expr_shift_free (subst x r e2) ->
    expr_shift_free (plet x e1 e2).
  Proof.
    unfold expr_shift_free. intros.
    inverts H2 as H2.
    { specializes H0 H2. subst.
      specializes H1 H10.
      false. }
    { specializes H H2. false. }
  Qed.


  (* Lemma sf_subst : forall e x v,
    expr_shift_free (subst x v e) ->
    expr_shift_free e.
  Proof.
  intros e. induction e;
  try solve [ unfold expr_shift_free; intros; inverts H0 as H0 ].
  {
    intros. simpl in H.
    {
    destruct (var_eq x x0); subst; simpl.
    - eapply sf_plet.
      eapply IHe1.
      unfold expr_shift_free in H.
    }
      unfold expr_shift_free. intros.
      eapply H.
      (* eapply eval_plet.
      admit.
      apply H0. *)
  }
  Qed. *)

  (* Lemma sf_plet0 : forall x e1 e2,
    expr_shift_free e1 ->
    expr_shift_free e2 ->
    expr_shift_free (plet x e1 e2).
  Proof.
    unfold expr_shift_free. intros.
    inverts H1 as H1.
    { specializes H0 H9. subst.
      specializes H1 H10.
      false. }
    { specializes H H2. false. }
  Qed. *)


  Definition expr_no_res e :=
    forall p1 h1 h2 v, bigstep p1 h1 e h2 (enorm v) -> False.

  (* n is the number of shifts that can be done *)
  Fixpoint spec_assert (n:nat) (e: expr) (f: flow) : Prop :=
    match n with
    | O =>
    (* env compat *)
    (* shift_free f /\ *)

      (* forall p1 s1 h1 h2, *)
      (* (forall v1 v2, bigstep p1 h1 e h2 (eshft v1 v2) -> False) *)
      expr_shift_free e /\

      (* forall v, *)
      forall p1 s1 h1 h2 v,
        bigstep p1 h1 e h2 (enorm v) ->
        satisfies s1 s1 h1 h2 (norm v) f
    | S n1 =>
      (* forall p1 s1,
      (* env_compatible n1 p1 s1 -> *)
      forall h1 h2,
      (forall v,
      bigstep p1 h1 e h2 (enorm v) -> False) *)
      expr_no_res e
      /\
( 

      forall p1 s1 h1 h2 x1 eb x2 ek k fb v1 fk r,
        (* k occurs in fb as a stage, not a value. we can't sub inside flow.
          sub it into eb instead, as a vfptr, not a var. *)
        spec_assert n1 (subst x1 (vfptr k) eb) fb ->
        (* v1 occurs in fk as a value. we can sub this into ek. *)
        (* not sure about r, might need to be existential,
          as we can't get the result of ek *)
        spec_assert n1 (subst x2 v1 ek) (fk r) ->

      bigstep p1 h1 e h2 (eshft (vfun x1 eb) (vfun x2 ek)) ->
      satisfies s1 s1 h1 h2 (shft k fb v1 fk) f
      )
    end
    .
  (* with env_compatible (n:nat) (p1:penv) (s1:senv) :=
    match n with
    | O =>
      forall pfn xf x,
        Fmap.read p1 xf = pfn ->
        exists sfn, Fmap.read s1 xf = sfn /\
      (* inlining defn from above *)
        forall h1 h2 v, 
          bigstep p1 h1 (pfn x) h2 (enorm v) ->
          satisfies s1 s1 h1 h2 (norm v) (sfn x v)
    | S n1 =>
      forall pfn xf x,
        Fmap.read p1 xf = pfn ->
        exists sfn, Fmap.read s1 xf = sfn /\
        forall v, spec_assert n1 (pfn x) (sfn x v)
    end. *)

  Lemma sem_pval: forall v,
    spec_assert 0 (pval v) (ens (fun res => \[res = v])).
  Proof.
    (* intros n.
    induction n; intros.
    { *)
      simpl. intros.
      splits; intros.
      (* { shiftfree. } *)
      { unfold expr_shift_free. intros. inverts H as H. }
      inverts H as H.
      apply ens_pure_intro. reflexivity.
      (* }
    {
      simpl. intros.
      (* split; intros.
      {

        (* can't be proved if n is the number of shifts *)
        (* if we weaken it to tbe upper bound on the number of shifts? *)
        unfold not. intros.
        inverts H as H.
      } *)
      { inverts H1. }
    } *)
  Qed.

  Lemma sem_plet: forall n n1, n1 <= n ->
    forall x e1 e2 f1 f2 v,
    spec_assert n1 e1 f1 ->
    flow_res1 f1 v ->
    spec_assert (n-n1) (subst x v e2) f2 ->
    spec_assert n (plet x e1 e2) (f1;; f2).
  Proof.
    intros n.
    induction n.
    (* induction_wf IH: wf_lt n. *)
    (* induction_wf IH: wf_peano_lt n. *)
    {
      (* index is zero, so there are no shifts anywhere *)
    intros.
    inverts H as H.
    simpl in *. destr H0. destr H2.
    splits.
    {
      admit.
    }
    (* { shiftfree. } *)
    (* {
      (* apply sf_plet. *)
      applys sf_plet H H0.

      unfold expr_shift_free.

      intros.
      inverts H2 as H2.
      (* specializes H0 H12. *)
      eapply H0.
      applys_eq H12.
      (* reflexivity. *)
      (* inverts H2 as H2. *)
      (* specializes H3 H2. *)
      (* specializes H H2. *)
    } *)
    (* shiftfree. *)
    clear H H0.
    intros.

    inverts H as. introv He1 He2.
    specializes H3 He1. clear He1.
    specializes H1 H3. subst.
    specializes H4 He2. clear He2.
    applys* s_seq.
    }
    {
      (* index is nonzero, so there are shifts *)
      intros. simpl. intros.
      split; intros.
      {
        (* since there is at least one shift according to n,
        it cannot be that the let results in norm *)
        unfold expr_no_res. intros.
        inverts H3 as H3.
        simpl in H2.
        destruct n1.
        {
          (* if n1 is zero, f1 has no shift, f2 has shift, which it cannot *)
          simpl in H0.
          destruct H0 as [_ H0].
          specializes H0 H3. specializes H1 H0. subst.
          clear H0.

          simpl in H2. specializes H2. destruct H2 as [H2 _].
          specializes H2 v0 H11.
        }
        {
          (* if n1 is not zero, f1 has shifts, which it cannot have *)
          simpl in H0.
          specializes H0. destruct H0 as [H0 _].
          jauto.
        }
      }
      {

      (* the result of the let is a shift *)
        inverts H5 as H5.
        {
          (* e1 is norm, e2 has a shift *)
          destruct n1.
          {
          (* n1=0, e1 norm *)
          simpl in H0. destruct H0 as [_ H0].
          specializes H0 H5.
          specializes H1 H0. subst.
          simpl in H2.
          specializes H2. destruct H2 as [_ H2].
          specializes H2 H3 H4 H13.
          (* clear H3 H4 H13. *)

          (* TODO in order to do this, we need the constructive shift free continuation in exprs as well *)
          (* TODO which might need similar cps hacks in expr. try to relax the ones in flow first *)
          (* applys_eq s_seq_sh. *)
          (* apply* s_seq_sh. *)
          apply* s_seq.
          }

          (* second case, where there are shifts in f1, is vacuous *)
           {
            (* there is more than one shift in f1 *)
            (* we are just prevented from using H0 *)
            simpl in H0. destruct H0 as [H0 _].
            (* specializes H6 p1 s1 h1 h3. *)
            (* destruct H0. *)
            specializes H0 H5.
            false.
          }

        }
        {
          (* the result of let is shift, the shift comes from e1,
            and e2 goes into the continuation *)
          (* n1 must be nonzero *)
          destruct n1.
          {
            (* vacuous *)
            unfold flow_res1 in H1.
            simpl in H0. destruct H0.
            (* since n1 is zero, we get to use the fact that f1 is
              shift free to get a contradiction *)
            specializes H0 H5. false.
          }
          {
            (* this case is ok *)

            (* inverts H as H.
            {
              simpl in H2.
            } *)

            (* simpl in H2. *)
            (* simpl in H. *)
            (* Print Le. *)
            (* Print le. *)
            (* Check le. *)

            (* rew_nat in H. *)
            (* Print le. *)
            (* Unset Printing Notations. Set Printing Coercions. Set Printing Parentheses. *)
            (* inverts H as H. *)

            (* rew_math H. *)

            (* simpl in H0. destruct H0. *)

            (* specializes H0. destruct H0 as [_ H0]. *)
            (* specializes H0. *)

            (* specializes H0 . *)


            (* applys_eq s_seq_sh. *)
          admit.
          }
        }

      }

    }
    Abort.
End SpecAssertions.

(*

  (** * Specification assertions *)
  (** A #<i>specification assertion</i># is our equivalent of a (semantic) Hoare triple: a valid one ensures ensures that the given program satisfies the given specification. *)
  Definition pair_valid_under p1 s1 e f : Prop :=
    forall h1 h2 Re R,
      res_compatible Re R ->
      bigstep p1 h1 e h2 Re -> satisfies s1 s1 h1 h2 R f.

(* TODO do we need to update the env due to fptrs? *)

  (** Roughly, this says that for every binding in the program environment, we can find a "corresponding" one in the spec environment, where "corresponding" means related by a valid specification assertion. *)
  Definition env_compatible (p1:penv) (s1:senv) :=
    forall pfn xf x,
      Fmap.read p1 xf = pfn ->
      exists sfn, Fmap.read s1 xf = sfn /\
      forall v, pair_valid_under p1 s1 (pfn x) (sfn x v).

  Definition res_compatible (pres:eresult) (res:result) :=
    match pres, res with
    | enorm v1, norm v2 => v1 = v2
    | eshft (vfun x1 eb) (vfun x2 ek),
      shft k fb v1 fk =>
      forall vb, spec_assert (subst x1 vb eb) fb /\
        exists r, spec_assert (subst x2 v1 ek) (fk r)
    | _, _ => False
    end.

  (** The full definition requires compatible environments. *)
  Definition spec_assert (e: expr) (f: flow) : Prop :=
    forall p1 s1,
      env_compatible p1 s1 ->
      pair_valid_under p1 s1 e f.

  Module TestRes.
    (* < 1 + shift k. k 1 > *)
    Definition e1p := eshft
      (vfun "k" (papp (pvar "k") (pval (vint 1))))
      (vfun "x" (pvar "x")).

    Definition e1s vk := shft
      "k" (∃ r, unk "k" (vint 1) (r))
      vk (fun r => rs (ens (fun r1 => \[vk = r1])) r).

    Example e1_compat: forall v,
      res_compatible e1p (e1s v).
    Proof.
      unfold e1p, e1s. simpl. intros.
      unfold spec_assert, pair_valid_under.
      split; intros.
      { inverts H0 as H0.
        apply s_fex. exists v0.
        remember (Fmap.read p1 "k") as u eqn:H1. symmetry in H1.
        unfold env_compatible in H. specializes H H1. destr H.
        specializes H3 v0. unfold pair_valid_under in H3.
        specializes H3 H0.
        applys s_unk H.
        assumption. }
      { exs. intros.
        inverts H0 as H0.
        apply s_rs_val.
        apply ens_pure_intro.
        reflexivity.
      }
    Qed.
  End TestRes.

  #[global]
  Instance Proper_spec_assert : Proper
    (eq ====> entails ====> impl)
    spec_assert.
  Proof.
    unfold entails, Proper, respectful, impl, spec_assert, pair_valid_under.
    intros. subst.
    jauto.
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
    inverts H0 as H0.
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

    (* reason about how the let executes *)
    inverts H3 as. introv He1 He2.

    (* use the specification assertion we have about e1 *)
    (* unfold spec_assert, pair_valid_under in H. *)
    lets: H H2 h1 h3 v1.
    specializes H3 He1.
    specializes H0 H3. injects H0.

    (* unfold spec_assert, pair_valid_under in H1. *)
    specializes H1 H2 h3 h2 v0.
    specializes H1 He2.
    applys* s_seq.
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
      specializes Ht Hc Hb.
      apply s_disj_l.
      eapply s_seq.
      apply ens_void_pure_intro. reflexivity.
      assumption. }
    { (* false *)
      unfold spec_assert in Hf.
      specializes Hf Hc Hb.
      apply s_disj_r.
      eapply s_seq.
      apply ens_void_pure_intro. reflexivity.
      assumption. }
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
    constructor. exists l0.
    constructor. exists (vloc l0). exists (Fmap.single l0 v).
    forwards H1: Fmap.disjoint_single_of_not_indom h1 l0 v.
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
      injection Hb; intros; subst e0 x0; clear H.
      unfold spec_assert in H0.
      specializes H0 Hc H7. }
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
      specializes H0 Hc Hb. }
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

End SpecAssertions.

Module HistoryTriplesValues.

  Import SpecAssertions.

  (** * History triples *)
  (** A #<i>history triple</i># (i.e. not just a "triple", which typically refers to a Hoare triple) also constrains the history of a program. *)
  (* 
      h0 ╶─[fh]──▶ h1 ╶─[e]──▶ h2
      ╷                        ▲
      └───────────[f]──────────┘
  *)
  Definition hist_triple fh e f :=
    forall p1 s0 s1 h0 h1 h2 v R,
      satisfies s0 s1 h0 h1 R fh ->
      env_compatible p1 s1 ->
      bigstep p1 h1 e h2 (enorm v) ->
      satisfies s0 s1 h0 h2 (norm v) f.

  (** History triples are contravariant in the history. *)
  #[global]
  Instance Proper_hist_triple : Proper
    (flip entails ====> eq ====> entails ====> impl)
    hist_triple.
  Proof.
    unfold entails, Proper, respectful, impl, hist_triple, flip.
    intros. subst.
    jauto.
  Qed.

  #[global]
  Instance Proper_hist_triple_bi : Proper
    (bientails ====> eq ====> bientails ====> impl)
    hist_triple.
  Proof.
    unfold entails, Proper, respectful, impl, hist_triple, flip.
    intros. subst.
    apply H1.
    specializes H2 H4 H5.
    apply* H.
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

  (* This version doesn't constrain the result to be of a certain form *)
  Definition shift_free_any (f:flow) : Prop :=
    forall s1 s2 h1 h2 k fk r fb,
        not (satisfies s1 s2 h1 h2 (shft k fk r fb) f).

  Lemma hist_frame : forall fh fr f e,
    shift_free_any fr ->
    hist_triple fh e f ->
    hist_triple (fr;; fh) e (fr;; f).
  Proof.
    unfold hist_triple. introv H. intros.
    inverts H1 as H1.
    { applys* s_seq. }
    { apply H in H1. false. }
  Qed.

  Lemma hist_sem : forall f e,
    spec_assert e f <->
    hist_triple empty e f.
  Proof.
    iff H.
    { unfold hist_triple. intros.
      apply empty_inv in H0. destr H0. subst.
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
    shift_free_any fh ->
    hist_triple (fh;; empty) e f ->
    hist_triple fh e f.
  Proof.
    unfold hist_triple. introv H. intros.
    destruct R. 2: { apply H in H1. false. }
    applys H0.
    - applys s_seq.
      eassumption.
      apply empty_intro.
    - eassumption.
    - eassumption.
  Qed.

  (** History triples which only append to history can be derived directly from the history-frame rule. *)
  Lemma hist_frame_sem: forall fh e f,
    shift_free_any fh ->
    spec_assert e f ->
    hist_triple fh e (fh;; f).
  Proof.
    intros.
    apply hist_sem in H0.
    lets H3: hist_frame fh H0. clear H0.
    assumption.
    apply hist_pre_result in H3.
    apply H3.
    assumption.
  Qed.

  (** Rules for program constructs *)
  Lemma hist_pval: forall n fh,
    shift_free_any fh ->
    hist_triple fh (pval n) (fh;; ens (fun res => \[res = n])).
  Proof.
    unfold hist_triple. intros * Hsf * Hh * Hc Hb.
    destruct R. 2: { apply Hsf in Hh. false. }
    applys s_seq h1 v0 Hh.
    lets H: sem_pval n Hc.
    unfold pair_valid_under, spec_assert in H.
    apply H; auto.
  Qed.

  Remark hist_pval_via_frame: forall n fh,
    shift_free_any fh ->
    hist_triple fh (pval n) (fh;; ens (fun res => \[res = n])).
  Proof.
    intros.
    applys* hist_frame_sem (@sem_pval n).
  Qed.

  Lemma hist_pref: forall v fh,
    shift_free_any fh ->
    hist_triple fh (pref (pval v))
      (fh;; fex (fun y =>(ens (fun r => \[r = vloc y] \* y ~~> v)))).
  Proof.
    intros.
    applys* hist_frame_sem (@sem_pref v).
  Qed.

  Lemma hist_pderef: forall x fh,
    shift_free_any fh ->
    hist_triple fh (pderef (pval (vloc x)))
      (fh;; fall (fun y =>
        req (x ~~> y) (ens (fun res => \[res = y] \* x ~~> y)))).
  Proof.
    intros.
    applys* hist_frame_sem (@sem_pderef x).
  Qed.

  Lemma hist_passign: forall x y v fh,
    shift_free_any fh ->
    hist_triple fh (passign (pval (vloc x)) (pval y))
      (fh;; req (x ~~> v) (ens_ (x ~~> y))).
  Proof.
    intros.
    applys* hist_frame_sem (@sem_passign x).
  Qed.

  Lemma hist_passert: forall fh b,
    shift_free_any fh ->
    hist_triple fh (passert (pval (vbool b))) (fh;; req_ \[b = true]).
  Proof.
    intros.
    applys* hist_frame_sem (@sem_passert b).
  Qed.

  Lemma hist_pif: forall fh b e1 e2 f1 f2,
    shift_free_any fh ->
    hist_triple (fh;; ens_ \[b = true]) e1 f1 ->
    hist_triple (fh;; ens_ \[b = false]) e2 f2 ->
    hist_triple fh (pif (pval (vbool b)) e1 e2) (disj f1 f2).
  Proof.
    introv Hsf He1 He2.
    unfold hist_triple. intros.
    destruct R. 2: { apply Hsf in H. false. }
    destruct b.
    { forwards: He1.
      { applys s_seq h1 v0.
        exact H.
        pose proof (ens_void_pure_intro).
        apply ens_void_pure_intro.
        reflexivity. }
      { exact H0. }
      { inverts H1 as H1. exact H1. }
      apply s_disj_l. assumption. }

    { forwards: He2.
      { applys s_seq h1 v0.
        exact H.
        pose proof (ens_void_pure_intro).
        apply ens_void_pure_intro.
        reflexivity. }
      { exact H0. }
      { inverts H1 as H1. exact H1. }
      apply s_disj_r. assumption. }
  Qed.

  Lemma hist_papp_fun: forall vf x e va f fh,
    vf = vfun x e ->
    hist_triple fh (subst x va e) f ->
    hist_triple fh (papp (pval vf) (pval va)) f.
  Proof.
    intros. subst.
    unfold hist_triple. intros.
    inverts H2 as H2.
    { injects H6.
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
    shift_free_any fh ->
    hist_triple fh (papp (pvar xf) (pval va))
      (fh;; fex (fun r => unk xf va r)).
  Proof.
    intros.
    applys* hist_frame_sem fh (@sem_papp_unk xf va).
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

End HistoryTriplesValues.

Module HistoryTriples.

  Import SpecAssertions.

  (** * History triples *)
  (** A #<i>history triple</i># (i.e. not just a "triple", which typically refers to a Hoare triple) also constrains the history of a program. *)
  (* 
      h0 ╶─[fh]──▶ h1 ╶─[e]──▶ h2
      ╷                        ▲
      └───────────[f]──────────┘
  *)
  Definition hist_triple fh e f :=
    forall p1 s0 s1 h0 h1 h2 R0 R Re,
      satisfies s0 s1 h0 h1 R0 fh ->
      env_compatible p1 s1 ->
      res_compatible Re R ->
      bigstep p1 h1 e h2 Re ->
      satisfies s0 s1 h0 h2 R f.

  (** History triples are contravariant in the history. *)
  #[global]
  Instance Proper_hist_triple : Proper
    (flip entails ====> eq ====> entails ====> impl)
    hist_triple.
  Proof.
    unfold entails, Proper, respectful, impl, hist_triple, flip.
    intros. subst.
    apply H1.
    specializes H H3.
    specializes H2 H H4 H5.
  Qed.

  #[global]
  Instance Proper_hist_triple_bi : Proper
    (bientails ====> eq ====> bientails ====> impl)
    hist_triple.
  Proof.
    unfold entails, Proper, respectful, impl, hist_triple, flip.
    intros. subst.
    apply H1.
    specializes H2 H4 H5.
    apply* H.
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

  (* This version doesn't constrain the result to be of a certain form *)
  Definition shift_free_any (f:flow) : Prop :=
    forall s1 s2 h1 h2 k fk r fb,
        not (satisfies s1 s2 h1 h2 (shft k fk r fb) f).

  Lemma hist_frame : forall fh fr f e,
    shift_free_any fr ->
    hist_triple fh e f ->
    hist_triple (fr;; fh) e (fr;; f).
  Proof.
    unfold hist_triple. introv H. intros.
    inverts H1 as H1.
    { applys* s_seq. }
    { apply H in H1. false. }
  Qed.

  Lemma hist_sem : forall f e,
    spec_assert e f <->
    hist_triple empty e f.
  Proof.
    iff H.
    { unfold hist_triple. intros.
      apply empty_inv in H0. destr H0. subst.
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
    shift_free_any fh ->
    hist_triple (fh;; empty) e f ->
    hist_triple fh e f.
  Proof.
    unfold hist_triple. introv H. intros.
    destruct R. 2: { apply H in H1. false. }
    applys H0.
    - applys s_seq.
      eassumption.
      apply empty_intro.
    - eassumption.
    - eassumption.
  Qed.

  (** History triples which only append to history can be derived directly from the history-frame rule. *)
  Lemma hist_frame_sem: forall fh e f,
    shift_free_any fh ->
    spec_assert e f ->
    hist_triple fh e (fh;; f).
  Proof.
    intros.
    apply hist_sem in H0.
    lets H3: hist_frame fh H0. clear H0.
    assumption.
    apply hist_pre_result in H3.
    apply H3.
    assumption.
  Qed.

  (** Rules for program constructs *)
  Lemma hist_pval: forall n fh,
    shift_free_any fh ->
    hist_triple fh (pval n) (fh;; ens (fun res => \[res = n])).
  Proof.
    unfold hist_triple. intros * Hsf * Hh * Hc Hb.
    destruct R. 2: { apply Hsf in Hh. false. }
    applys s_seq h1 v0 Hh.
    lets H: sem_pval n Hc.
    unfold pair_valid_under, spec_assert in H.
    apply H; auto.
  Qed.

  Remark hist_pval_via_frame: forall n fh,
    shift_free_any fh ->
    hist_triple fh (pval n) (fh;; ens (fun res => \[res = n])).
  Proof.
    intros.
    applys* hist_frame_sem (@sem_pval n).
  Qed.

  Lemma hist_pref: forall v fh,
    shift_free_any fh ->
    hist_triple fh (pref (pval v))
      (fh;; fex (fun y =>(ens (fun r => \[r = vloc y] \* y ~~> v)))).
  Proof.
    intros.
    applys* hist_frame_sem (@sem_pref v).
  Qed.

  Lemma hist_pderef: forall x fh,
    shift_free_any fh ->
    hist_triple fh (pderef (pval (vloc x)))
      (fh;; fall (fun y =>
        req (x ~~> y) (ens (fun res => \[res = y] \* x ~~> y)))).
  Proof.
    intros.
    applys* hist_frame_sem (@sem_pderef x).
  Qed.

  Lemma hist_passign: forall x y v fh,
    shift_free_any fh ->
    hist_triple fh (passign (pval (vloc x)) (pval y))
      (fh;; req (x ~~> v) (ens_ (x ~~> y))).
  Proof.
    intros.
    applys* hist_frame_sem (@sem_passign x).
  Qed.

  Lemma hist_passert: forall fh b,
    shift_free_any fh ->
    hist_triple fh (passert (pval (vbool b))) (fh;; req_ \[b = true]).
  Proof.
    intros.
    applys* hist_frame_sem (@sem_passert b).
  Qed.

  Lemma hist_pif: forall fh b e1 e2 f1 f2,
    shift_free_any fh ->
    hist_triple (fh;; ens_ \[b = true]) e1 f1 ->
    hist_triple (fh;; ens_ \[b = false]) e2 f2 ->
    hist_triple fh (pif (pval (vbool b)) e1 e2) (disj f1 f2).
  Proof.
    introv Hsf He1 He2.
    unfold hist_triple. intros.
    destruct R. 2: { apply Hsf in H. false. }
    destruct b.
    { forwards: He1.
      { applys s_seq h1 v0.
        exact H.
        pose proof (ens_void_pure_intro).
        apply ens_void_pure_intro.
        reflexivity. }
      { exact H0. }
      { inverts H1 as H1. exact H1. }
      apply s_disj_l. assumption. }

    { forwards: He2.
      { applys s_seq h1 v0.
        exact H.
        pose proof (ens_void_pure_intro).
        apply ens_void_pure_intro.
        reflexivity. }
      { exact H0. }
      { inverts H1 as H1. exact H1. }
      apply s_disj_r. assumption. }
  Qed.

  Lemma hist_papp_fun: forall vf x e va f fh,
    vf = vfun x e ->
    hist_triple fh (subst x va e) f ->
    hist_triple fh (papp (pval vf) (pval va)) f.
  Proof.
    intros. subst.
    unfold hist_triple. intros.
    inverts H2 as H2.
    { injects H6.
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
    shift_free_any fh ->
    hist_triple fh (papp (pvar xf) (pval va))
      (fh;; fex (fun r => unk xf va r)).
  Proof.
    intros.
    applys* hist_frame_sem fh (@sem_papp_unk xf va).
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
*)
