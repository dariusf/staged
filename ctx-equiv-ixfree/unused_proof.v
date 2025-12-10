(*
(* composition of subst and subst_map,
  where the variable to be substituted doesn't appear in the substitution *)
Lemma subst_subst_map : ∀ (e:expr) Γ (x : string) (es : val) (map : sub),
  subst_is_closed Γ ∅ map →
  subst x es (subst_map (delete x map) e) =
  subst_map (insert x es map) e
with subst_subst_map_val : ∀ (v:val) Γ (x : string) (es : val) (map : sub),
  subst_is_closed Γ ∅ map →
  subst x es (subst_map_val (delete x map) v) =
  subst_map_val (insert x es map) v.
Proof.
  { intros e. induction e.
    { intros. apply (subst_subst_map_val _ _ _ _ _ H). }
    { (* e is a variable x *)
      intros. simpl. destruct (decide (x0=x)) as [->|Hne].
      { (* if x=x0, we'll end up substituting es into x *)
        rewrite lookup_delete_eq with (m:=map).
        rewrite lookup_insert_eq with (m:=map).
        simpl.
        by rewrite decide_True. }
      { (* if not equal, the deletion and insertion will have no effect *)
        rewrite lookup_delete_ne with (m:=map). 2: { assumption. }
        rewrite lookup_insert_ne with (m:=map). 2: { assumption. }
        (* we then need to see if x is in the map to begin with *)
        destruct (map !! x) as [v1|] eqn:Hkey.
        { Fail rewrite Hkey. (* why does regular rewrite not work? *)
          setoid_rewrite Hkey.
          simpl.
          rewrite (subst_val_closed _ ∅ _ _).
          - reflexivity.
          - apply (subst_is_closed_elim_closed _ _ x _ _ H Hkey).
          - set_solver. }
      { setoid_rewrite Hkey.
        simpl.
        by rewrite decide_False. } } }
    { intros. simpl. f_equal; eauto. } }
  { intros v. induction v; intros.
    (*{ reflexivity. }*)
    { (* the lambda case *)
      simpl. f_equal. f_equal.
      case_decide.
      { subst.
        rewrite delete_delete_eq with (m:=map).
        rewrite delete_insert_eq with (m:=map). done. }
      { rewrite delete_insert_ne with (m:=map). 2: { congruence. }
        rewrite delete_delete with (m:=map).
        eapply subst_subst_map.
        apply (subst_is_closed_subseteq (Γ ∖ {[x]}) Γ _ (delete x map) map).
        destruct H as [H1 H2].
        rewrite H1.
        set_solver.
        apply delete_subseteq.
        set_solver.
        assumption. } }
    (*{ reflexivity. }*) }
Qed.

(** Special case of Theorem A.1 from Erlang paper:
  scoping of extended substitutions.
  Given a closed substitution, we can add a closed value to it. *)
Lemma scope_extend1 Γ x (v:val) (γ:sub):
  closed ∅ v →
  subst_is_closed Γ ∅ γ →
  subst_is_closed (Γ ∪ {[x]}) ∅ (<[x := v]> γ).
Proof.
  intros Hc Hsc.
  split.
  { destruct Hsc. rewrite H. set_solver. }
  intros x0 Hd v0 Hs.
  (* we have to prove that for an arbitrary binding x0 := v0 in γ, v0 is closed *)
  destruct (decide (x=x0)) as [->|Hne].
  (* if x = x0, the premise tells us v0 is closed *)
  { rewrite lookup_insert_eq with (m:=γ) in Hs.
    injection Hs. intros. subst.
    exact Hc. }
  (* if they are not equal, we know x0 is in Γ and have to use the fact
    that the subst_is_closed *)
  { rewrite elem_of_union in Hd. destruct Hd. 2: { assert (x0 = x). set_solver. done. }
    destruct Hsc as [_ Hsc].
    rewrite lookup_insert_ne with (m:=γ) in Hs. 2: { assumption. }
    specialize (Hsc x0 H v0 Hs).
    assumption. }
Qed.

(* we can extend related substitutions with related values *)
Lemma sem_context_rel_insert Γ x v1 v2 γ1 γ2 n:
  n ⊨ V_rel v1 v2 →
  n ⊨ G_rel Γ γ1 γ2 →
  n ⊨ G_rel (Γ ∪ {[x]}) (<[x := v1]> γ1) (<[x := v2]> γ2).
Proof.
  intros Hv Hγ.
  destruct (V_rel_elim _ _ _ Hv) as (Hvc1 & Hvc2 & Hv').
  destruct (G_rel_elim _ _ _ _ Hγ) as (Hγc1 & Hγc2 & Hγ').
  apply G_rel_intro.
  { by apply scope_extend1. }
  { by apply scope_extend1. }

  iintros x0 v0 v3 H1 H2.
  destruct (decide (x=x0)).
  { subst.
    rewrite lookup_insert_eq with (m:=γ2) in H2. idestruct H2. injection H2 as ->.
    rewrite lookup_insert_eq with (m:=γ1) in H1. idestruct H1. injection H1 as ->.
    assumption. }
  { rewrite lookup_insert_ne with (m:=γ2) in H2. idestruct H2. 2: { assumption. }
    rewrite lookup_insert_ne with (m:=γ1) in H1. idestruct H1. 2: { assumption. }
    iapply Hγ'.
    - iintro. eassumption.
    - iintro. eassumption. }
Qed.

Lemma lambda_closed Γ γ x e :
  closed (Γ ∪ {[x]}) e  →
  subst_is_closed Γ ∅ γ  →
  closed ∅ (vlambda x (subst_map (delete x γ) e)).
Proof.
  intros Hec [Heq Hγc].
  rewrite closed_lambda.
  eapply subst_map_closed'_2.
  - eapply closed_weaken.
    exact Hec.
    setoid_rewrite dom_delete.
    intros y. destruct (decide (x = y)); set_solver.
  - apply (subst_is_closed_subseteq (Γ ∖ {[x]}) Γ _ (delete x γ) γ).
    + set_solver.
    + apply delete_subseteq.
    + set_solver.
    + unfold subst_is_closed. split.
      * exact Heq.
      * intros x' Hin v Hlookup.
        specialize (Hγc x' Hin v Hlookup).
        by eapply closed_weaken.
Qed.
*)

(*
Notation name := string.
Definition sub : Set := gmap name val.
Definition scope : Set := gset name.

Fixpoint subst_map_val (γ : sub) (v : val) : val :=
  match v with
  (*| vunit => vunit
  | vint n => vint n*)
  | vlambda x e => vlambda x (subst_map (delete x γ) e)
  end
with subst_map (γ : sub) (e : expr) : expr :=
  match e with
  | ret v => ret (subst_map_val γ v)
  (* | eunit => eunit *)
  | var x => match γ !! x with Some v => ret v | _ =>  var x end
  | app e1 e2 => app (subst_map γ e1) (subst_map γ e2)
  (* | abs x e => abs x (subst_map (binder_delete x xs) e) *)
  (* | eplus e1 e2 => eplus (subst_map xs e1) (subst_map xs e2) *)
  end.

Lemma fold_unfold_subst_map_val_vlambda γ x e :
  subst_map_val γ (vlambda x e) =
  vlambda x (subst_map (delete x γ) e).
Proof. auto. Qed.

Lemma fold_unfold_subst_map_ret γ v :
  subst_map γ (ret v) =
  ret (subst_map_val γ v).
Proof. auto. Qed.

Lemma fold_unfold_subst_map_var γ x :
  subst_map γ (var x) =
  match γ !! x with
  | Some v => ret v
  |  _ =>  var x
  end.
Proof. auto. Qed.

Lemma fold_unfold_subst_map_app γ e1 e2 :
  subst_map γ (app e1 e2) =
  app (subst_map γ e1) (subst_map γ e2).
Proof. auto. Qed.

Fixpoint is_closed (X : scope) (e : expr) : bool :=
  match e with
  | var x => bool_decide (x ∈ X)
  (*| ret vunit | ret (vint _) => true*)
  | ret (vlambda x e) => is_closed (X ∪ {[x]}) e
  | app e1 e2
  (* | eplus e1 e2 *)
  => is_closed X e1 && is_closed X e2
  end.

(* aka a scoping judgment, the untyped equivalent of a typing judgment *)
Definition closed (X : scope) (e : expr) : Prop := Is_true (is_closed X e).

Lemma closed_weaken e X Y:
  closed X e → X ⊆ Y → closed Y e
with closed_weaken_val (v:val) X Y:
  closed X v → X ⊆ Y → closed Y v.
Proof.
  { revert X Y.
    induction e; intros.
    - apply (closed_weaken_val _ _ _ H H0).
    - unfold closed, is_closed in *.
      apply bool_decide_unpack in H.
      apply bool_decide_pack.
      set_solver.
    - unfold closed in *. simpl in *.
      apply andb_prop_intro.
      apply andb_prop_elim in H.
      destruct H.
      split.
      apply (IHe1 _ _ H H0).
      apply (IHe2 _ _ H1 H0). }
  { revert X Y.
    induction v; intros.
    (*- constructor.*)
    - unfold closed in *.
      simpl in *.
      apply (closed_weaken e _ _ H).
      set_solver.
    (*- constructor.*) }
Qed.

Lemma closed_subst :
  ∀ Γ x e1 e2,
    closed (Γ ∪ {[x]}) e1 →
    closed ∅ e2 →
    closed Γ (subst x e2 e1)
with closed_subst_val :
  ∀ Γ x (v : val) e,
    closed (Γ ∪ {[x]}) v →
    closed ∅ e →
    closed Γ (subst_val x e v).
Proof.
  {
    unfold closed in *.
    intros Γ x e1 e2 H_closed1 H_closed2.
    induction e1.
    - simpl in *. auto.
    - simpl in *.
      rewrite -> decide_bool_decide.
      destruct (bool_decide_reflect (x = x0)) as [H_eq | H_neq].
      + eapply closed_weaken.
        exact H_closed2.
        set_solver.
      + simpl in *.
        apply bool_decide_unpack in H_closed1.
        apply bool_decide_pack.
        set_solver.
    - simpl in *.
      apply andb_prop_elim in H_closed1 as [Hc1 Hc2].
      apply andb_prop_intro. split.
      + exact (IHe1_1 Hc1).
      + exact (IHe1_2 Hc2).
  }
  {
    unfold closed in *.
    intros Γ x v e H_closed1 H_closed2.
    induction v.
    (* - simpl in *. auto. *)
    - simpl in *.
      rewrite -> decide_bool_decide.
      destruct (bool_decide_reflect (x = x0)) as [H_eq | H_neq].
      + rewrite -> H_eq in H_closed1.
        eapply closed_weaken.
        exact H_closed1. set_solver.
      + simpl in *.
        apply closed_subst.
        eapply closed_weaken.
        exact H_closed1. set_solver.
        exact H_closed2.
    (*- simpl in *. auto.*)
  }
Qed.

Lemma closed_app xs e1 e2:
  closed xs (app e1 e2) ↔
  closed xs e1 ∧ closed xs e2.
Proof. unfold closed. simpl. by rewrite andb_True. Qed.

Lemma closed_lambda e Γ x : closed Γ (vlambda x e) ↔ closed (Γ ∪ {[x]}) e.
Proof. split. auto. auto. Qed.

Lemma closed_var Γ x : closed Γ (var x) ↔ x ∈ Γ.
Proof. unfold closed. simpl. by rewrite bool_decide_spec. Qed.

Lemma base_step_preserve_closedness :
  ∀ e1 e1',
    base_step e1 e1' →
    closed ∅ e1 →
    closed ∅ e1'.
Proof.
  unfold closed.
  intros e1 e1' Hred H_closed.
  inversion Hred. subst. simpl in *.
  apply andb_prop_elim in H_closed as [Hc1 Hc2].
  exact (closed_subst ∅ x e0 e2 Hc1 Hc2).
Qed.

Definition ectx_is_closed (X : scope) (E : ectx) :=
  ∀ e, closed ∅ e → closed X (fill E e).

Lemma closed_decompose :
  ∀ E e,
    closed ∅ (fill E e) →
    ectx_is_closed ∅ E ∧ closed ∅ e.
Proof.
  unfold ectx_is_closed.
  intros E.
  induction E; intros e' H_closed.
  - simpl in *. auto.
  - simpl in *.
    apply IHE in H_closed as [H_fill H_closed].
    apply closed_app in H_closed as [H_closed1 H_closed2].
    split.
    + intros e'' H_closed3.
      apply H_fill.
      apply closed_app. auto.
    + auto.
  - simpl in *.
    apply IHE in H_closed as [H_fill H_closed].
    apply closed_app in H_closed as [H_closed1 H_closed2].
    split.
    + intros e'' H_closed3.
      apply H_fill.
      apply closed_app. auto.
    + auto.
Qed.

Lemma closed_compose :
  ∀ E e,
    ectx_is_closed ∅ E →
    closed ∅ e →
    closed ∅ (fill E e).
Proof. unfold ectx_is_closed. auto. Qed.

Lemma contextual_step_preserve_closedness :
  ∀ e1 e1',
    contextual_step e1 e1' →
    closed ∅ e1 →
    closed ∅ e1'.
Proof.
  unfold closed.
  intros e1 e1' Hred H_closed.
  inversion Hred. subst. simpl in *. clear Hred.
  apply closed_decompose in H_closed as [H_closed1 H_closed2].
  apply (base_step_preserve_closedness _ _ H1) in H_closed2.
  apply closed_compose; auto.
Qed.

(** subscoped from the Erlang paper *)
Definition subst_is_closed (Γ free : scope) (sub : sub) :=
  Γ = dom sub ∧
  ∀ x, x ∈ Γ →
    ∀ v, sub !! x = Some v → closed free (ret v).

Lemma subst_is_closed_subseteq: ∀ (Γ1 Γ2 X : scope) (γ1 γ2: sub),
  Γ1 = dom γ1 →
  γ1 ⊆ γ2 → Γ1 ⊆ Γ2 → subst_is_closed Γ2 X γ2 → subst_is_closed Γ1 X γ1.
Proof.
  intros * Hd Hγ HΓ Hclosed2.
  destruct Hclosed2 as [Hd2 Hc2].
  split.
  assumption.
  intros x Hl v Hs.
  rewrite (map_subseteq_spec γ1 γ2) in Hγ.
  (* specialize (Hγ _ _ Hs). *)
  specialise Hγ Hs.
  apply (Hc2 x ltac:(set_solver) _ Hγ).
Qed.

Lemma closed_ectx_app1 :
  ∀ E e,
    ectx_is_closed ∅ E →
    closed ∅ e →
    ectx_is_closed ∅ (ectx_app1 E e).
Proof.
  intros E e Hc1 Hc2.
  unfold ectx_is_closed in *.
  intros e' Hc3. simpl.
  apply Hc1. apply closed_app. auto.
Qed.

Lemma closed_ectx_app2 :
  ∀ (v : val) E,
    closed ∅ v →
    ectx_is_closed ∅ E →
    ectx_is_closed ∅ (ectx_app2 v E).
Proof.
  intros v E Hc1 Hc2.
  unfold ectx_is_closed in *.
  intros e' Hc3. simpl.
  apply Hc2. apply closed_app. auto.
Qed.

Lemma subst_is_closed_elim_closed Γ (γ:sub) x X (v:val):
  subst_is_closed Γ X γ →
  γ !! x = Some v →
  closed X v.
Proof.
  intros [Hdom Hsc] He.
  assert (H := elem_of_dom_2 _ _ _ He).
  (* have: elem_of_dom_2 He. *)
  (* pose proof (elem_of_dom_2 _ _ _ He). *)
  assert (x ∈ Γ). set_solver.
  apply (Hsc x H0 v He).
Qed.

(* if e is closed under Y, we can split the variables in Y between X and γ *)
Lemma subst_map_closed' (e : expr) (X Y : scope) (γ:sub) :
  closed Y e →
  (∀ x, x ∈ Y → match γ !! x with Some v0 => closed X (ret v0) | None => x ∈ X end) →
  closed X (subst_map γ e)
with subst_map_closed'_val (v : val) (X Y : scope) (γ:sub) :
  closed Y (ret v) →
  (∀ x, x ∈ Y → match γ !! x with Some v0 => closed X (ret v0) | None => x ∈ X end) →
  closed X (subst_map_val γ v).
Proof.
  {
    revert X Y γ. induction e.
    { eapply subst_map_closed'_val; eauto. }
    { intros * Hc H.
      (* e is a variable x *)
      unfold closed in Hc; simpl in Hc; apply bool_decide_unpack in Hc.
      specialize (H x Hc). simpl.
      destruct (γ !! x) eqn:He.
      - assumption.
      - unfold closed; simpl; apply bool_decide_pack. assumption.
    }
    { intros *.
      unfold closed. simpl.
      rewrite !andb_True. intros [? ?] **.
      split.
      by eapply IHe1.
      by eapply IHe2. }
  }
  { revert X Y γ. induction v.
    (*{ intros. assumption. }*)
    { unfold closed. simpl.
      intros * Hce H.
      eapply subst_map_closed'. eassumption.
      intros y [|]%elem_of_union.
      { destruct (decide (x = y)).
        { by subst; rewrite lookup_delete_eq with (m:=γ); set_solver. }
        rewrite lookup_delete_ne with (m:=γ). 2: { assumption. }
        eapply H in H0.
        destruct lookup; last set_solver.
        eapply closed_weaken; eauto with set_solver. }
      { rewrite elem_of_singleton in H0.
        subst. rewrite lookup_delete_eq with (m:=γ). set_solver. }
    }
    (*{ intros. assumption. }*) }
Qed.

(* simple corollary of [subst_map_closed'],
  where we have split Y into X and dom γ upfront *)
Lemma subst_map_closed'_2 Γ X γ e :
  closed (X ∪ (dom γ)) e ->
  subst_is_closed Γ X γ ->
  closed X (subst_map γ e).
Proof.
  intros Hcl Hsubst.
  eapply subst_map_closed'; first eassumption.
  intros x Hx.
  destruct (γ !! x) as [e'|] eqn:Heq.
  - apply (subst_is_closed_elim_closed _ _ _ _ _ Hsubst Heq).
  - apply not_elem_of_dom in Heq.
    set_solver.
Qed.

(* given a value and a substitution closed under the same scope,
  applying the substitution gives us a completely closed value *)
Lemma subst_map_closed'_3 (v:val) Γ γ:
  closed Γ v ->
  subst_is_closed Γ ∅ γ ->
  closed ∅ (subst_map γ v).
Proof.
  pose proof (subst_map_closed'_2 Γ ∅ γ v).
  simpl in H.
  intros.
  apply H. 2: { assumption. }
  destruct H1 as [? _].
  rewrite <- H1.
  replace (∅ ∪ Γ) with Γ. assumption.
  set_solver.
Qed.

Lemma subst_map_val_closed_val_aux Γ γ (v : val) :
  closed Γ v →
  Γ ∩ dom γ = ∅ →
  subst_map_val γ v = v
with subst_map_closed_aux Γ γ (e : expr) :
  closed Γ e →
  Γ ∩ dom γ = ∅ →
  subst_map γ e = e.
Proof.
  { intros Hc Hdom.
    induction v.
    - rewrite -> closed_lambda in Hc.
      rewrite -> fold_unfold_subst_map_val_vlambda.
      rewrite -> (subst_map_closed_aux (Γ ∪ {[x]}) (delete x γ) e Hc ltac:(set_solver)).
      reflexivity. }
  { intros Hc Hdom.
    induction e.
    - rewrite -> fold_unfold_subst_map_ret.
      f_equal. by eapply subst_map_val_closed_val_aux.
    - unfold closed in Hc.
      simpl in Hc.
      rewrite -> bool_decide_spec in Hc.
      rewrite -> fold_unfold_subst_map_var.
      assert (H_not_in : x ∉ dom γ) by set_solver.
      rewrite -> (not_elem_of_dom γ x) in H_not_in.
      setoid_rewrite -> H_not_in.
      reflexivity.
    - apply closed_app in Hc as [Hc1 Hc2].
      rewrite -> fold_unfold_subst_map_app.
      rewrite -> (IHe1 Hc1).
      rewrite -> (IHe2 Hc2).
      reflexivity. }
Qed.

Lemma subst_map_val_closed_val γ (v : val) :
  closed ∅ v →
  subst_map_val γ v = v.
Proof.
  intros Hc.
  eapply subst_map_val_closed_val_aux.
  - exact Hc.
  - set_solver.
Qed.

Lemma subst_map_closed γ (e : expr) :
  closed ∅ e →
  subst_map γ e = e.
Proof.
  intros Hc.
  eapply subst_map_closed_aux.
  - exact Hc.
  - set_solver.
Qed.
*)

(*
Lemma subset_is_closed_absurd x Γ γ:
  x ∈ Γ →
  subst_is_closed Γ ∅ γ →
  γ !! x = None →
  False.
Proof.
  intros Hx Hs He.
  pose proof (not_elem_of_dom_2 _ _ He).
  destruct Hs as [? _].
  setoid_rewrite <- H0 in H.
  set_solver.
Qed.
*)

(*
Lemma subst_val_closed v X x es :
  closed X (of_val v) → x ∉ X → subst_val x es v = v
with subst_closed X e x es :
  closed X e → x ∉ X → subst x es e = e.
Proof.
  { induction v.
    (*{ reflexivity. }*)
    { simpl.
      case_decide.
      - reflexivity.
      - intros.
        f_equal.
        rewrite closed_lambda in H0.
        apply (subst_closed _ _ _ _ H0).
        set_solver. }
    (*{ reflexivity. }*) }
 { induction e; intros; simpl.
    { f_equal.
      eapply subst_val_closed.
      apply H. assumption. }
    { case_decide.
      - subst.
        unfold closed in H. simpl in H. apply bool_decide_unpack in H.
        set_solver.
      - reflexivity. }
    { apply closed_app in H.
      destruct H as (H1&H2).
      specialize (IHe1 H1 H0).
      specialize (IHe2 H2 H0).
      f_equal.
      - assumption.
      - assumption. } }
Qed.
*)

(*
(* aka contextual scoping C : Γ ~> Γ', a special case of contextual typing.
  defined inductively because we need to invert it. *)
Inductive closed_ctx : scope → scope → ctx → Prop :=
  | cc_hole Γ :
    closed_ctx Γ Γ ctx_hole

  | cc_lambda x Γ Γ' C :
    closed_ctx Γ (Γ' ∪ {[x]}) C →
    closed_ctx Γ Γ' (ctx_lam x C)

  | cc_app1 Γ Γ' C e :
    closed_ctx Γ Γ' C →
    closed Γ' e →
    closed_ctx Γ Γ' (ctx_app1 C e)

  | cc_app2 Γ Γ' C v :
    closed_ctx Γ Γ' C →
    closed Γ' (ret v) →
    closed_ctx Γ Γ' (ctx_app2 v C)
  .
*)

(*
Definition closed_ctx_sem (Γ Γ' : scope) (C:ctx) : Prop :=
  forall e, closed Γ e → closed Γ' (cplug C e).

Lemma closed_ctx_sound Γ Γ' e :
  closed_ctx Γ Γ' e → closed_ctx_sem Γ Γ' e.
Proof.
  intros H. induction H; unfold closed_ctx_sem.
  - simpl. done.
  - intros e Hc.
    simpl.
    specialize (IHclosed_ctx e Hc).
    unfold closed. simpl.
    apply IHclosed_ctx.
  - intros e2 Hc.
    specialize (IHclosed_ctx _ Hc).
    simpl.
    unfold closed. simpl.
    unfold closed in IHclosed_ctx. simpl in IHclosed_ctx.
    auto.
  - intros e1 Hc.
    specialize (IHclosed_ctx _ Hc).
    simpl.
    unfold closed. simpl.
    unfold closed in IHclosed_ctx. simpl in IHclosed_ctx.
    auto.
Qed.
*)

(*
Lemma G_rel_empty n :
  n ⊨ G_rel ∅ ∅ ∅.
Proof.
  apply G_rel_intro.
  - unfold subst_is_closed. split; set_solver.
  - unfold subst_is_closed. split; set_solver.
  - iintros.
    idestruct H.
    setoid_rewrite lookup_empty in H.
    discriminate H.
Qed.

Lemma subst_map_empty (e:expr) :
  subst_map ∅ e = e
with subst_map_val_empty (v:val) :
  subst_map_val ∅ v = v.
Proof.
  { induction e.
    - simpl. f_equal. eapply subst_map_val_empty.
    - simpl.
      setoid_rewrite lookup_empty.
      reflexivity.
    - simpl. rewrite IHe1. rewrite IHe2. reflexivity. }
  { induction v.
    - simpl.
      f_equal.
      setoid_rewrite delete_empty.
      apply subst_map_empty. }
Qed.

Lemma fundamental_property_sub Γ γ n :
  subst_is_closed Γ ∅ γ →
  n ⊨ G_rel Γ γ γ.
Proof.
  intros Hc.
  apply G_rel_intro.
  { exact Hc. }
  { exact Hc. }
  iintros x v1 v2 Heq1 Heq2.
  idestruct Heq1.
  idestruct Heq2.
  rewrite -> Heq1 in Heq2.
  injection Heq2 as ->.
  destruct Hc as [-> Hc].
  assert (Hcv2 : closed ∅ v2).
  { eapply Hc.
    - setoid_rewrite -> elem_of_dom.
      unfold is_Some. eauto.
    - exact Heq1. }
  assert (H_fundamental := fundamental_property_v ∅ v2 n Hcv2).
  apply V_rel_o_elim in H_fundamental.
  ispec H_fundamental ∅ ∅ (G_rel_empty n).
  rewrite -> subst_map_val_empty in H_fundamental.
  exact H_fundamental.
Qed.

Lemma fundamental_property_ectx E n :
  n ⊨ K_rel E E.
Proof.
  apply K_rel_intro.
  iintros v1 v2 Hv.
  admit.
Admitted.
*)
