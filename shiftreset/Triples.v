
From ShiftReset Require Import Logic.
Local Open Scope string_scope.

Inductive eresult : Type :=
  | enorm : val -> eresult
  | eshft : (var -> expr) -> (val -> expr) -> eresult.

Notation "'eshft(' k ',' eb ',' x ',' ek ')'" :=
  (eshft k eb x ek) (at level 30, only printing,
  format "'eshft(' k ','  eb ','  x ','  ek ')'" ).

Definition penv := Fmap.fmap var (val -> expr).
Implicit Types p penv : penv.

#[global]
Instance Inhab_pfun : Inhab (val -> expr).
Proof.
  constructor.
  exists (fun a:val => pval vunit).
  constructor.
Qed.

Definition empty_penv : penv := Fmap.empty.

Coercion pval : val >-> expr.
Coercion pvar : var >-> expr.

Inductive bigstep : penv -> heap -> expr -> heap -> eresult -> Prop :=

  | eval_pval : forall p1 h v,
    bigstep p1 h (pval v) h (enorm v)

  | eval_pfun : forall p h x e,
    bigstep p h (pfun x e) h (enorm (vfun x e))

  | eval_padd : forall p1 h v1 v2 i1 i2,
    vint i1 = v1 ->
    vint i2 = v2 ->
    bigstep p1 h (padd (pval v1) (pval v2)) h (enorm (vint (i1 + i2)))

  | eval_pshift : forall h p (eb:var->expr),
    bigstep p h (pshift eb) h (eshft eb (fun v => pval v))

  | eval_plet : forall p1 h1 h3 h2 x e1 e2 v Re,
    bigstep p1 h1 e1 h3 (enorm v) ->
    bigstep p1 h3 (subst x v e2) h2 Re ->
    bigstep p1 h1 (plet x e1 e2) h2 Re

  | eval_plet_sh : forall x e1 e2 h1 h2 p1 (eb:var->expr) (ek:val->expr),
    bigstep p1 h1 e1 h2 (eshft eb ek) ->
    bigstep p1 h1 (plet x e1 e2) h2 (eshft eb (fun y => plet x (ek y) e2))

  | eval_papp_fun : forall v1 v2 h x e Re p1,
    v1 = vfun x e ->
    bigstep p1 h (subst x v2 e) h Re ->
    bigstep p1 h (papp (pval v1) (pval v2)) h Re

  (* | eval_app_fix : forall v1 v2 h x e Re xf p,
    v1 = vfix xf x e ->
    bigstep p h (subst x v2 (subst xf v1 e)) h Re ->
    bigstep p h (papp (pval v1) (pval v2)) h Re *)

  | eval_papp_unk : forall v h1 h2 Re (ef:val->expr) (f:var) p1,
    Fmap.read p1 f = ef ->
    bigstep p1 h1 (ef v) h2 Re ->
    bigstep p1 h1 (papp (pvar f) (pval v)) h2 Re

  | eval_preset_val : forall p1 h1 h2 p e v,
    bigstep p1 h1 e h2 (enorm v) ->
    bigstep p1 h1 (preset e) h2 (enorm v)

  | eval_preset_sh : forall k p1 h1 h2 h3 e (eb:var->expr) (ek:val->expr) Re,
    bigstep p1 h1 e h3 (eshft eb ek) ->
    bigstep (Fmap.update p1 k ek) h3 (eb k) h2 Re ->
    bigstep p1 h1 (preset e) h2 Re

  .


Module BigStepExamples.

Example e1_shift : exists Re,
  bigstep empty_penv empty_heap (pshift (fun k => pval (vint 1)))
    empty_heap Re.
Proof.
  intros. eexists.
  applys eval_pshift.
  (* Show Proof. *)
Qed.

Example e2_shift_reset : forall (k1:var), exists Re,
  bigstep empty_penv empty_heap (preset (pshift (fun k => papp k (pval (vint 1)))))
    empty_heap Re.
Proof.
  intros. eexists.
  applys eval_preset_sh k1.
  applys eval_pshift.
  simpl.
  applys eval_papp_unk. reflexivity.
  rewrite fmap_read_update.
  applys eval_pval.
  (* Show Proof. *)
Qed.

(* < let x1 = shift k. k in x1 + 1 > 1 *)
Example e3_shift_k_k : forall (k:var), exists Re,
  bigstep empty_penv empty_heap
    (plet "x2"
      (preset (plet "x1"
        (pshift (fun k => pfun "x" (papp k (pvar "x"))))
        (padd 1 (pvar "x1"))))
      (papp (pvar "x2") 1))
    empty_heap Re.
Proof.
  intros. eexists.
  applys eval_plet.
  { applys eval_preset_sh k.
    (* we have to name the binders of the new functions created *)
    { applys eval_plet_sh. applys_eq eval_pshift. }
    { simpl. applys eval_pfun. } }
  { simpl.
    applys eval_papp_fun. reflexivity. simpl.
Abort.
(* we cannot handle dynamic continuations in triples without a simulation relation *)
    (* applys eval_papp_fun. reflexivity. simpl.
    applys eval_plet.
    { applys eval_papp_fun. reflexivity. simpl.
      applys eval_pval. }
    simpl.
    applys* eval_padd.
  }
  (* Show Proof. *)
Qed. *)

End BigStepExamples.

Notation " '[' p1 ','  h1  '|'  e ']'  '~~>'  '[' p2 ','  h2  '|'  Re ']'" :=
  (bigstep p1 h1 e p2 h2 Re) (at level 30, only printing).

Notation "'pshift' k '.' e" :=
  (pshift k e) (at level 30, only printing,
  format "'pshift'  k '.'  e" ).


Inductive spec_assert_valid_under penv (env:senv) : expr -> flow -> Prop :=
  | sav_base: forall e f,
    (forall h1 h2 (eb:var->expr) (ek:val->expr),
        not (bigstep penv h1 e h2 (eshft eb ek))) ->
    (forall h1 h2 v,
        bigstep penv h1 e h2 (enorm v) ->
        satisfies env env h1 h2 (norm v) f) ->
    spec_assert_valid_under penv env e f

| sav_shift: forall e f,
    (forall h1 h2 v, not (bigstep penv h1 e h2 (enorm v))) ->
    (forall h1 h2 (eb:var->expr) (ek:val->expr),
        bigstep penv h1 e h2 (eshft eb ek) ->
        exists k (fb:flow) (fk:val->flow),
          satisfies env env h1 h2 (shft k fb fk) f /\
            spec_assert_valid_under penv env (eb k) fb /\
            (forall v, spec_assert_valid_under penv env (ek v) (fk v))) ->
    spec_assert_valid_under penv env e f.

Lemma spec_assert_valid_under_ind1 :
  forall penv env (P:expr->flow->Prop),
    (forall e f,
      (forall h1 h2 eb ek, ~ bigstep penv h1 e h2 (eshft eb ek)) ->
      (forall h1 h2 v,
        bigstep penv h1 e h2 (enorm v) ->
        satisfies env env h1 h2 (norm v) f) ->
      P e f) ->
    (forall e f,
      (forall h1 h2 v, ~ bigstep penv h1 e h2 (enorm v)) ->
      (forall h1 h2 eb ek,
        bigstep penv h1 e h2 (eshft eb ek) ->
        exists k fb fk, satisfies env env h1 h2 (shft k fb fk) f /\
        (spec_assert_valid_under penv env (eb k) fb) /\
        (P (eb k) fb) /\
        (forall v, spec_assert_valid_under penv env (ek v) (fk v)) /\
        (forall v, P (ek v) (fk v))) ->
      P e f) ->
    forall e f,
      spec_assert_valid_under penv env e f -> P e f.
Proof.
  intros * Hbase Hrec.
  fix ind 3.
  intros.
  destruct H.
  - eauto.
  - apply* Hrec.
    intros.
    specializes H0 H1.
    destr H0.
    exists k fb fk.
    splits*.
Qed.

Definition spec_assert_valid e f : Prop :=
  forall penv env,
    spec_assert_valid_under penv env e f.


Lemma pval_sound: forall v,
  spec_assert_valid (pval v) (ens (fun r => \[r = v])).
Proof.
  unfold spec_assert_valid. intros.
  applys sav_base. { introv H. false_invert H. }
  introv H.
  inverts H.
  applys s_ens.
  exs. intuition. hintro. reflexivity.
  fmap_eq.
Qed.

(* Lemma pshift_sound: forall eb k fb,
  spec_assert_valid (eb k) (fb) ->
  spec_assert_valid (pshift eb) (sh k fb).
Proof.
  unfold spec_assert_valid. intros * Heb **.
  applys sav_shift. { introv H. false_invert H. } intros.
  inverts H.
  exs.
  splits.
  { applys* s_sh. }
  { specializes Heb penv0 env. }
  { intros v. simpl. applys pval_sound. }
Qed. *)

Lemma papp_unk_sound: forall penv (env:senv) (f:var) v (ef:val->expr) (f1:val->flow),
  Fmap.read penv f = ef ->
  Fmap.read env f = f1 ->
  spec_assert_valid_under penv env (ef v) (f1 v) ->
  spec_assert_valid_under penv env (papp f v) (unk f v).
Proof.
  unfold spec_assert_valid. intros * ? ? He.
  inverts He as.
  { introv Hne He.
    applys sav_base.
    { introv H1. inverts H1 as H1 H2. rewrite H in H1. false Hne H1. }
    intros * Hb.
    inverts Hb as. intros Hb.
    rewrite H in Hb.
    specializes He Hb.
    applys s_unk.
    eassumption.
    assumption. }
  { intros * Hne He.
    applys sav_shift.
    { introv H1. inverts H1 as H1 H2. rewrite H in H1. false Hne H1. }
    intros * Hb.
    inverts Hb as H3 H4.
    rewrite H in H3.
    specializes He H3. destruct He as (fk&fb&rb&?&?).
    exs.
    split*.
    applys s_unk.
    eassumption.
    assumption. }
Qed.


Lemma papp_sound: forall x e (v:val) f,
  spec_assert_valid (subst x v e) f ->
  spec_assert_valid (papp (vfun x e) v) f.
Proof.
  unfold spec_assert_valid.
  intros * He penv env.
  specializes He penv env.
  inverts He as.
  { introv Hne He.
    (* no shift in the body of the fn being applied *)
    applys sav_base.
    { intros * H. inverts H as H H1. injects H. false Hne H1. }
    intros.
    inverts H as H H1. injects H.
    specializes He H1.
    assumption. }
  { intros * Hne He.
    (* shift *)
    applys sav_shift.
    { introv H.
      inverts H as H H1. injects H.
      false Hne H1. }
    intros.
    inverts H as H H1. injects H.
    specializes He H1. destr He.
    exs.
    splits*.
  }
Qed.

Lemma plet_sound: forall x e1 e2 f1 (f2:val->flow),
  spec_assert_valid e1 f1 ->
  (forall v, spec_assert_valid (subst x v e2) (f2 v)) ->
  spec_assert_valid (plet x e1 e2) (bind f1 f2).
Proof.
  unfold spec_assert_valid. introv He1 He2. intros. specializes He1 penv0 env.
  inverts He1 as.
  {
    (* e1 has no shift *)
    introv Hne1 Hb1.

    (* if i am able to predict, this is all good *)
    (* applys sav_shift.
    admit. *)
    (* intros.
    inverts H.
    { specializes He2 v penv0 env.
    inverts He2. { false H H8. }
    specializes H0 H8.
    destr H0. exists fb fk.
    splits*.
    applys s_bind.
    specializes Hb1 H7. eassumption.
    assumption.
    }
    { false Hne1 H6. } *)

    specializes He2 penv0 env.
    inverts He2 as.
    {
      (* e2 has no shift *)
      introv Hne2 Hb2.
      applys sav_base.
      {
        introv H1.
        inverts H1.
        (* false Hne2 H8. *)
        applys_eq Hne2. applys_eq H8. f_equal.
        Fail reflexivity.
        (* cyclic dependency, we need to know how e2 evaluates to choose shift or no *)
        (* supply v -> invert He2 -> reason backwards -> supply v *)
        admit.
        admit.
      }
      admit.
    }
    {
      (* e2 has shift *)
      introv Hne2 Hb2.
      admit.
    }
  }
  {
    (* e1 has shift *)
    introv Hne1 Hb1.
    applys sav_shift.
    { introv H. inverts H as H1. false Hne1 H1. }
    { intros.
      inverts H.
      {
          false Hne1 H7. }
        (* specializes He2 v penv0 env.
        inverts He2 as. { (* e2 has no shift *) introv Hne2 Hb2. false Hne2 H8. }
        { (* e2 has shift *)
          false Hne1 H7. }
      } *)
      {
        (* e1 has a shift *)
        specializes Hb1 H6.
        destruct Hb1 as (fb&fk&?&?&?&?).
        exs. splits.
        applys s_bind_sh H.
        assumption.
        intros. specializes H1 v.
        (* simpl. case_if. clear C. *)
        (* assert (x<>x0) as ?. admit. *)
        (* case_if. clear H2 C. *)

        (* prove the continuation satisfies triple *)
        (* need the induction hypothesis for ek and e2 *)
        admit.
      }
    }
  }
Abort.

Require Import Coq.Program.Equality.

Lemma plet_sound_aux: forall penv env x v (ek:val->expr) (fk:val->flow),
  (forall v, spec_assert_valid_under penv env (ek v) (fk v)) ->
  spec_assert_valid_under penv env (plet x (ek v) (padd (pvar x) 1))
    ((fun r1 => bind (fk r1)
      (fun x => ens (fun r => \[exists i : int, x = i /\ r = i + 1])))
    v).
Proof.
  intros.
  specializes H v.
  induction H using spec_assert_valid_under_ind1.
  { (* ek has no shift *)
      applys sav_base.
      { intros.
        introv H2.
        inverts H2.
        { false_invert H10. }
        { false H H8. } }
      intros.
      inverts H1. simpl in H10.
      case_if.
      specializes H0 H9.
      applys s_bind H0.

      inverts H10.
      injects H8.

      applys s_ens.
      exs.
      splits*.
      hintro.
      exists i1.
      splits*.
      fmap_eq. }
  { (* ek has shift *)
    applys sav_shift. { introv H1. inverts H1. false H H9. }
    intros.
    inverts H1. { false H H9. } clear H.
    specializes H0 H8.
    destr H0.
    exs.
    splits.
    applys s_bind_sh H0.
    { assumption. }
    { eauto. } }
Qed.

Lemma plet_sound_test: forall x e1 e2 f1 (f2:val->flow),
  spec_assert_valid e1 f1 ->
  (forall v, spec_assert_valid (subst x v e2) (f2 v)) ->
  spec_assert_valid (plet x e1 e2) (bind f1 f2).
Proof.
  unfold spec_assert_valid. introv He1 He2. intros. specializes He1 penv0 env.
  assert (x = "x") as ?. admit.
  assert (e1 = pshift (fun k => papp (pvar k) 1)) as ?. admit.
  assert (f1 = sh "k" (unk "k" 1)) as ?. admit.
  assert (e2 = padd (pvar "x") 1) as ?. admit.
  assert (f2 = (fun x => ens (fun r => \[exists i, x = vint i /\ r = i + 1]))) as ?. admit.
  subst.

  inverts He1.
  { applys sav_base.
    { intros. introv H1. inverts H1. false_invert H9. false H H8. }
    { intros. inverts H1. false_invert H9. } }
  applys sav_shift. { intros. introv H1. inverts H1. inverts H9. }
  intros.
  inverts H1. { false_invert H9. }
  specializes H0 H8.
  clear H.
  destr H0.

  exs. splits.

  - applys s_bind_sh.
    eassumption.

  - assumption.

  -
    pose proof plet_sound_aux.
    intros.
    specializes H1 penv0 env v H2.

    (* specializes H1 fk. *)


    (* v H2. *)


    (* specializes H1 v. *)
    (* specializes H1 H0. *)


  (* - intros.
    specializes He2 v penv0 env.
    simpl in He2.
    specializes H2 v.

    (* see whether ek has shift *)
    inverts H2.
    {
      (* ek has no shift *)
      applys sav_base.
      { intros.
        introv H2.
        inverts H2.
        { false_invert H13. }
        { false H1 H11. } }
      intros.
      inverts H2.
      specializes H3 H12.
      applys s_bind H3.

      simpl in H13.
      inverts H13.
      injects H11.

      applys s_ens.
      exs.
      splits*.
      hintro.
      Set Printing Coercions.
      exists i1.
      splits*.
      fmap_eq.
    }
    {
      (* ek has shift *)
      applys sav_shift. { introv H2. inverts H2. false H1 H12. }
      intros.
      inverts H2.
      { simpl in H13. inverts H13. }

      specializes H3 H11.
      destr H3.
      exs.
      splits.
      applys s_bind_sh.
      applys H2.
      assumption.
      intros.
      (* induction? *)

      admit.
    } *)
Abort.

Lemma plet_sound_test: forall x e1 e2 f1 (f2:val->flow),
  spec_assert_valid e1 f1 ->
  (forall v, spec_assert_valid (subst x v e2) (f2 v)) ->
  spec_assert_valid (plet x e1 e2) (bind f1 f2).
Proof.
  unfold spec_assert_valid. introv He1 He2. intros. specializes He1 penv0 env.
  assert (x = "x") as ?. admit.
  assert (e1 = 1) as ?. admit.
  assert (f1 = ens (fun r => \[r = 1])) as ?. admit.
  assert (e2 = padd (pvar "x") 1) as ?. admit.
  assert (f2 = (fun x => ens (fun r => \[exists i, x = vint i /\ r = i + 1]))) as ?. admit.
  subst.

  inverts He1.
  2: { applys sav_shift. intros. introv H1. inverts H1. false H H9. intros. inverts H1. inverts H10. inverts H8. }

  applys sav_base.
  { intros. introv H1. inverts H1. inverts H10. inverts H8. }
  intros.
  inverts H1.
  specializes H0 H9.
  specializes He2 v0 penv0 env.
  simpl in He2.
  inverts He2. 2: { false H1 H10. }

  applys s_bind H0.
  applys* H2.

Abort.
