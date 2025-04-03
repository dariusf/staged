
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

  (* | eval_papp_unk : forall v h1 h2 Re fe (f:var) p s1 s2 s3 x r,
    Fmap.read p f = (x, fe) ->
    s3 = Fmap.update s1 x v ->
    (* s4 = Fmap.update s2 r r -> *)
    bigstep p s3 h1 fe s2 h2 r Re ->
    bigstep p s1 h1 (papp (pvar f) (pval v)) s2 h2 r Re *)

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
    (forall p1 h1 h2 k eb x ek,
        not (bigstep p1 h1 e h2 (eshft k eb x ek))) ->
    (forall h1 h2 v,
        bigstep penv h1 e h2 (enorm v) ->
        satisfies env env h1 h2 (norm v) f) ->
    spec_assert_valid_under penv env e f

| sav_shift: forall e f,
    (forall p1 h1 h2 v, not (bigstep p1 h1 e h2 (enorm v))) ->
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


Lemma pshift_sound: forall k eb fb,
  spec_assert_valid eb fb ->
  spec_assert_valid (pshift k eb) (sh k fb).
Proof.
  intros.
Admitted.

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