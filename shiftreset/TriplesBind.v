
From ShiftReset Require Import LogicBind.
Local Open Scope string_scope.

Inductive eresult : Type :=
  | enorm : val -> eresult
  | eshft : var -> expr -> (var -> expr) -> eresult.

Notation "'eshft(' k ',' eb ',' ek ')'" :=
  (eshft k eb ek) (at level 30, only printing,
  format "'eshft(' k ','  eb ','  ek ')'" ).

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

Inductive bigstep : penv -> heap -> expr -> penv -> heap -> eresult -> Prop :=

  | eval_pval : forall p1 h v,
    bigstep p1 h (pval v) p1 h (enorm v)

  | eval_pfun : forall p h x e,
    bigstep p h (pfun x e) p h (enorm (vfun x e))

  | eval_padd : forall p1 h v1 v2 i1 i2,
    vint i1 = v1 ->
    vint i2 = v2 ->
    bigstep p1 h (padd (pval v1) (pval v2)) p1 h (enorm (vint (i1 + i2)))

  | eval_pshift : forall h p k eb,
    bigstep p h (pshift k eb) p h (eshft k eb (fun r => pvar r))

  | eval_plet : forall p1 p2 p3 h1 h3 h2 x e1 e2 v Re,
    bigstep p1 h1 e1 p3 h3 (enorm v) ->
    bigstep p1 h3 (subst x v e2) p2 h2 Re ->
    bigstep p1 h1 (plet x e1 e2) p2 h2 Re

  | eval_plet_sh : forall x e1 e2 h1 h2 p1 p2 k eb (ek:var->expr),
    bigstep p1 h1 e1 p2 h2 (eshft k eb ek) ->
    bigstep p1 h1 (plet x e1 e2) p2 h2 (eshft k eb (fun y => plet x (ek y) e2))

  | eval_papp_fun : forall v1 v2 h x e Re p1 p2,
    v1 = vfun x e ->
    bigstep p1 h (subst x v2 e) p2 h Re ->
    bigstep p1 h (papp (pval v1) (pval v2)) p2 h Re

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

  | eval_preset_val : forall p1 p2 h1 h2 p e v,
    bigstep p1 h1 e p2 h2 (enorm v) ->
    bigstep p1 h1 (preset e) p2 h2 (enorm v)

  | eval_preset_sh : forall x p1 p2 p3 h1 h2 h3 e k eb (ek:var->expr) Re,
    bigstep p1 h1 e p3 h3 (eshft k eb ek) ->
    bigstep p3 h3 (subst k (vfun x (ek x)) eb) p2 h2 Re ->
    bigstep p1 h1 (preset e) p2 h2 Re

  .


Module BigStepExamples.

Example e1_shift : forall k, exists Re,
  bigstep empty_penv empty_heap (pshift k (pval (vint 1)))
    empty_penv empty_heap Re.
Proof.
  intros. eexists.
  applys eval_pshift.
  (* Show Proof. *)
Qed.

Example e2_shift_reset : forall k, exists Re,
  bigstep empty_penv empty_heap (preset (pshift k (pval (vint 1))))
    empty_penv empty_heap Re.
Proof.
  intros. eexists.
  applys eval_preset_sh "r".
  applys eval_pshift.
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
    empty_penv empty_heap Re.
Proof.
  intros. eexists.
  applys eval_plet.
  { applys eval_preset_sh "x3".
    (* we have to name the binders of the new functions created *)
    applys eval_plet_sh.
    applys eval_pshift.
    simpl.
    applys eval_pfun. }
  { simpl.
    applys eval_papp_fun. reflexivity. simpl.
    applys eval_papp_fun. reflexivity. simpl.
    applys eval_plet.
    { applys eval_pval. }
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
    (forall p1 p2 h1 h2 k eb x (ek:var->expr),
        not (bigstep p1 h1 e p2 h2 (eshft k eb ek))) ->
    (forall p1 p2 s1 s2 h1 h2 v,
      (* TODO use penv env *)
        bigstep p1 h1 e p2 h2 (enorm v) ->
        satisfies s1 s2 h1 h2 (norm v) f) ->
    spec_assert_valid_under penv env e f

| sav_shift: forall e f,
    (forall p1 p2 h1 h2 v, not (bigstep p1 h1 e p2 h2 (enorm v))) ->
    (forall p1 p2 s1 s2 h1 h2 k eb x ek,
        bigstep p1 h1 e p2 h2 (eshft k eb ek) ->
        exists fb (fk:val->flow),
          satisfies s1 s2 h1 h2 (shft k fb fk) f /\
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
  (* applys s_ens. *)
  (* admit *)
Admitted.