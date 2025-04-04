
From ShiftReset Require Import LogicBind.
Local Open Scope string_scope.

Inductive eresult : Type :=
  | enorm : val -> eresult
  | eshft : var -> expr -> var -> expr -> eresult.

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
Coercion vint : Z >-> val.

Inductive bigstep : penv -> heap -> expr -> heap -> eresult -> Prop :=

  | eval_pval : forall p1 h v,
    bigstep p1 h (pval v) h (enorm v)

  | eval_pfun : forall p h x e,
    bigstep p h (pfun x e) h (enorm (vfun x e))

  | eval_padd : forall p1 h v1 v2 i1 i2,
    vint i1 = v1 ->
    vint i2 = v2 ->
    bigstep p1 h (padd (pval v1) (pval v2)) h (enorm (vint (i1 + i2)))

  | eval_pshift : forall x h p k eb,
    bigstep p h (pshift k eb) h (eshft k eb x (pvar x))

  | eval_plet : forall p1 h1 h3 h2 x e1 e2 v Re,
    bigstep p1 h1 e1 h3 (enorm v) ->
    bigstep p1 h3 (subst x v e2) h2 Re ->
    bigstep p1 h1 (plet x e1 e2) h2 Re

  | eval_plet_sh : forall x e1 e2 h1 h2 p1 k eb ek y x1,
    bigstep p1 h1 e1 h2 (eshft k eb x1 ek) ->
    bigstep p1 h1 (plet x e1 e2) h2 (eshft k eb y (plet x (papp (vfun x1 ek) y) e2))

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

  | eval_preset_sh : forall x p1 h1 h2 h3 e k eb ek Re,
    bigstep p1 h1 e h3 (eshft k eb x ek) ->
    bigstep p1 h3 (subst k (vfun x ek) eb) h2 Re ->
    bigstep p1 h1 (preset e) h2 Re

  .


Module BigStepExamples.

Example e1_shift : forall k, exists Re,
  bigstep empty_penv empty_heap (pshift k (pval (vint 1)))
    empty_heap Re.
Proof.
  intros. eexists.
  applys eval_pshift "x".
  (* Show Proof. *)
Qed.

Example e2_shift_reset : forall k, exists Re,
  bigstep empty_penv empty_heap (preset (pshift k (pval (vint 1))))
    empty_heap Re.
Proof.
  intros. eexists.
  applys eval_preset_sh.
  applys eval_pshift "r".
  simpl.
  applys eval_pval.
  (* Show Proof. *)
Qed.

Example e3_shift_k_k : exists Re,
  bigstep empty_penv empty_heap
    (plet "x2"
      (preset (plet "x1"
        (pshift "k" (pfun "x" (papp (pvar "k") (pvar "x"))))
        (padd 1 (pvar "x1"))))
      (papp (pvar "x2") 1))
    empty_heap Re.
Proof.
  intros. eexists.
  applys eval_plet.
  { applys eval_preset_sh "x3".
    (* we have to name the binders of the new functions created *)
    applys eval_plet_sh.
    applys eval_pshift "r".
    simpl.
    applys eval_pfun. }
  { simpl.
    applys eval_papp_fun. reflexivity. simpl.
    applys eval_papp_fun. reflexivity. simpl.
    applys eval_plet.
    { applys eval_papp_fun. reflexivity. simpl.
      applys eval_pval. }
    simpl.
    applys* eval_padd.
  }
  (* Show Proof. *)
Qed.

End BigStepExamples.

Notation " '[' p1 ','  h1  '|'  e ']'  '~~>'  '[' p2 ','  h2  '|'  Re ']'" :=
  (bigstep p1 h1 e p2 h2 Re) (at level 30, only printing).

Notation "'pshift' k '.' e" :=
  (pshift k e) (at level 30, only printing,
  format "'pshift'  k '.'  e" ).


Inductive spec_assert_valid_under penv (env:senv) : expr -> flow -> Prop :=
  | sav_base: forall e f,
    (forall h1 h2 k eb x ek,
        not (bigstep penv h1 e h2 (eshft k eb x ek))) ->
    (forall h1 h2 v,
        bigstep penv h1 e h2 (enorm v) ->
        satisfies env env h1 h2 (norm v) f) ->
    spec_assert_valid_under penv env e f

| sav_shift: forall e f,
    (forall h1 h2 v, not (bigstep penv h1 e h2 (enorm v))) ->
    (forall h1 h2 k eb x ek,
        bigstep penv h1 e h2 (eshft k eb x ek) ->
        exists fb (fk:val->flow),
          satisfies env env h1 h2 (shft k fb fk) f /\
            spec_assert_valid_under penv env eb fb /\
            forall v, spec_assert_valid_under penv env (subst x v ek) (fk v)) ->
    spec_assert_valid_under penv env e f.


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

Lemma pshift_sound: forall k eb fb,
  spec_assert_valid eb fb ->
  spec_assert_valid (pshift k eb) (sh k fb).
Proof.
  unfold spec_assert_valid. intros * Heb **.
  specializes Heb penv0 env.
  applys sav_shift. { intros. introv H. false_invert H. } intros.
  inverts H.
  exs.
  splits.
  applys s_sh.
  assumption.
  { intros. simpl. case_if.
    applys pval_sound. }
Qed.

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
        destruct Hb1 as (fb&fk&?&?&?).
        exs. splits.
        applys s_bind_sh H.
        assumption.
        intros. specializes H1 v.
        simpl. case_if. clear C.
        assert (x<>x0) as ?. admit.
        case_if. clear H2 C.
        (* prove the continuation satisfies triple *)
        admit.
      }
    }
  }
Admitted.