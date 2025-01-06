
From Staged Require Import Logic Automation.
Local Open Scope string_scope.

(** * Specification of foldr *)
Definition foldr : ufun := fun (args:val) rr =>
  match args with
  | vtup (vstr f) (vtup (vint a) (vlist l)) =>
    disj
      (ens_ \[rr = vint a /\ l = nil])
      (∃ x l1, ens_ \[l = cons (vint x) l1];;
       ∃ r, unk "foldr" (vtup (vstr f) (vtup (vint a) (vlist l1))) r;;
        unk f (vtup (vint x) r) rr)
  | _ => empty
  end.

(** * [foldr_sum] *)
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
      (Fmap.single "foldr" foldr)
      "f" uncurried_plus_spec.

(** A re-summarization lemma *)
Definition foldr_sum := forall xs res,
  entails_under foldr_env
    (unk "foldr" (vtup (vstr "f") (vtup (vint 0) (vlist xs))) res)
    (ens_ \[res = vint (sum (to_int_list xs))]).

(** Reasoning semantically *)
Lemma foldr_sum_semantic:
  foldr_sum.
Proof.
  { unfold foldr_sum. intros xs. induction_wf IH: list_sub xs. intros.
    unfold entails_under. introv H.
    funfold foldr_env "foldr" in H. simpl in H.
    inverts H.
    { (* base case *)
      fdestr H5. subst.
      apply ens_void_pure_intro.
      intuition. }
    { (* rec *)
      (* get at all the facts... *)
      fdestr H5.
      fdestr H.
      fdestr H0.
      fdestr H0.
      fdestr H6.
      (* apply induction hypothesis *)
      specialize (IH b0). forward IH. rewrite H. auto.
      rewrite IH in H1.

      fdestr H1. rename H9 into Hf.
      fdestr H1.
      destr H0.

      (* reason about f *)
      funfold foldr_env "f" in Hf.

      simpl in Hf. subst b1.
      fdestr Hf.

      subst.
      apply ens_void_pure_intro.
      intuition. } }
Qed.

(** Proof using entailment rules *)
Lemma foldr_sum_entailment:
  foldr_sum.
Proof.
  { unfold foldr_sum. intros xs. induction_wf IH: list_sub xs. intros.
    funfold foldr_env "foldr". simpl.
    apply ent_disj_l.

    { apply ent_ens_single_pure.
      intuition. subst. reflexivity. }

    { apply ent_ex_l. intros x.
      apply ent_ex_l. intros l1.
      apply ent_seq_ens_l. intros H.
      (* specialize (IH l1). forward IH. rewrite H. auto. *)
      apply ent_ex_l. intros r.
      rewrite IH; [ | subst; auto ].
      funfold foldr_env "f".
      apply ent_seq_ens_l. intros. subst r.
      simpl.
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

(** * [foldr_sum_state] *)
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

Definition foldr_env0 :=
  Fmap.update
    (Fmap.single "foldr" foldr)
      "f" uncurried_plus_closure_spec.

Definition foldr_sum_state := forall xs res,
  entails_under foldr_env0
    (unk "foldr" (vtup (vstr "f") (vtup (vint 0) (vlist xs))) res)
    (∀ x a, req (x~~>vint a)
      (∃ r, ens_ (x~~>vint (a+length (to_int_list xs)) \*
        \[res = vint r /\ r = sum (to_int_list xs)]))).

Lemma foldr_sum_state_entailment:
  foldr_sum_state.
Proof.
  unfold foldr_sum. intros xs. induction_wf IH: list_sub xs. intros.
  funfold foldr_env0 "foldr".
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
    apply ent_ex_l. intros l1.
    apply ent_seq_ens_l. intros H.
    apply ent_ex_l. intros r.
    rewrite IH; [ | subst; auto ].
    funfold foldr_env0 "f".
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
    rewrite norm_seq_forall_distr_l.
    apply ent_all_l. exists x0.
    rewrite norm_seq_forall_distr_l.
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

(** * Problem 1: mutating the list *)
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
Proof. auto. Qed.

Lemma IsList_cons : forall p x L',
  IsList (vint x::L') p =
  \[p <> null] \* \exists q, (p ~~> (vtup (vint x) (vloc q))) \* (IsList L' q).
Proof. auto. Qed.

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

Definition foldr_env1 :=
  Fmap.update
    (Fmap.single "foldr" foldr_mut)
      "f" uncurried_plus_mut_spec.

Lemma foldr_ex1: forall xs res l,
  entails_under foldr_env1
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
    rewrite norm_ens_ens_pure_comm.
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
    rewrite norm_seq_exists_distr_l.
    rewrite norm_seq_exists_distr_r.
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

(** * Problem 2: stronger precondition *)
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
    (Fmap.single "foldr" foldr)
      "f" uncurried_plus_assert_spec.

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
    apply ent_ex_l. intros l1.
    apply ent_seq_ens_l. intros H.
    apply ent_ex_l. intros r.
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

(** * Problem 3: effects outside metalogic *)
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
    (Fmap.single "foldr" foldr)
      "f" uncurried_plus_exc_spec.

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
    apply ent_ex_l. intros l1.
    apply ent_seq_ens_l. intros H.
    apply ent_ex_l. intros r.
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

Module Rev.

(**
  let a = ref [] in
  foldr (fun c t -> a := c :: !a; c + t) xs 0
*)

Definition g : ufun := fun args rr =>
  match args with
  | vtup (vint c) (vint t) => ∀ x a,
      req (x~~>vlist a)
        (ens_ (x~~>vlist (vint c :: a) \* \[rr = vint (c + t)]))
  | _ => empty
  end.

Definition foldr_env :=
  Fmap.update
    (Fmap.single "foldr" foldr)
      "f" g.

Definition foldr_sum_rev := forall xs res,
  entails_under foldr_env
    (unk "foldr" (vtup (vstr "f") (vtup (vint 0) (vlist xs))) res)
    (∀ x a, req (x~~>vlist a)
      (ens_ (x~~>vlist (xs ++ a) \*
        \[res = vint (sum (to_int_list xs))]))).

Lemma foldr_sum_rev_entailment:
  foldr_sum_rev.
Proof.
  unfold foldr_sum_rev. intros xs. induction_wf IH: list_sub xs. intros.
  funfold1 "foldr".
  simpl.
  apply ent_disj_l.
  { fintro x.
    fintro a.
    apply ent_req_r.
    rewrite norm_ens_ens_void_comm.
    fassume (?&?).
    subst.
    simpl.
    apply ent_ens_single.
    xsimpl.
    intuition. }
  { fintro x.
    fintro l1.
    fassume H.
    fintro r.
    rewrite IH; [ | subst; auto ].
    funfold foldr_env "f".
    fintro x0. finst x0.
    fintro a. finst a.
    rewrite norm_reassoc.
    apply ent_req_req. xsimpl.
    (* extract the pure part *)
    rewrite norm_ens_ens_void_split.
    rewrite norm_ens_ens_void_comm.
    rewrite <- norm_seq_assoc.
    fassume H1. subst r.
    simpl.
    finst x0.
    finst (app l1 a).
    rewrite norm_ens_req_transpose.
    2: { apply b_pts_single. }
    rewrite norm_req_pure_l. 2: reflexivity.
    rewrite norm_seq_ens_empty.
    apply ent_ens_single.
    subst.
    xsimpl.
    intuition math. }
Qed.

End Rev.
