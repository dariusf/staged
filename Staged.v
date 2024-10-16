(** A minimal, reference formalization of #<a href="https://dl.acm.org/doi/10.1007/978-3-031-71162-6_26">Staged Specification Logic for Verifying Higher-Order Imperative Programs</a># (FM 2024). *)
From Coq Require Import Classes.RelationClasses.
From Coq Require Morphisms Program.Basics.

From SLF Require LibSepFmap.
Module Fmap := LibSepFmap.

From Staged Require Export Extra Heap Tactics.

Local Open Scope string_scope.
(* Local Open Scope nat_scope. *)
Local Open Scope Z_scope.
Local Open Scope list_scope.

Set Implicit Arguments.

(** * Programs *)
(** The representation of programs and the use of substitution are mostly reused from SLF. *)
Definition var : Type := string.
Definition var_eq := String.string_dec.

Definition loc := nat.

Inductive val :=
  | vunit : val
  | vint : Z -> val
  | vfun : var -> expr -> val
  | vfix : var -> var -> expr -> val
  | vloc : loc -> val
  | vtup : val -> val -> val
  | vstr : string -> val
  | vbool : bool -> val
  | vlist : list val -> val

with expr : Type :=
  | pvar (x: var)
  | pval (v: val)
  | plet (x: var) (e1 e2: expr)
  | pfix (f: var) (x: var) (e: expr)
  | pfun (x: var) (e: expr)
  | padd (x y: expr)
  | pfst (t: expr)
  | psnd (t: expr)
  | pminus (x y: expr)
  | passert (b: val)
  | pref (v: val)
  | pderef (v: val)
  | passign (x: val) (v: val)
  | pif (x: val) (e1: expr) (e2: expr)
  | papp (x: expr) (a: expr).

#[global]
Instance Inhab_val : Inhab val.
Proof.
  constructor.
  exists vunit.
  constructor.
Qed.

Fixpoint subst (y:var) (w:val) (e:expr) : expr :=
  let aux t := subst y w t in
  let if_y_eq x t1 t2 := if var_eq x y then t1 else t2 in
  match e with
  | pval v => pval v
  | padd x y => padd x y
  | pminus x y => pminus x y
  | pfst x => pfst x
  | psnd x => psnd x
  | pvar x => if_y_eq x (pval w) e
  | passert b => passert b
  | pderef r => pderef r
  | passign x y => passign x y
  | pref v => pref v
  | pfun x t1 => pfun x (if_y_eq x t1 (aux t1))
  | pfix f x t1 => pfix f x (if_y_eq f t1 (if_y_eq x t1 (aux t1)))
  | papp e v => papp e v
  | plet x t1 t2 => plet x (aux t1) (if_y_eq x t2 (aux t2))
  | pif t0 t1 t2 => pif t0 (aux t1) (aux t2)
  end.

Module Val.
  Definition value := val.
End Val.

(** SLF's heap theory as a functor. *)
Module Export Heap := Heap.HeapSetup Val.

Definition empty_heap : heap := Fmap.empty.

Definition precond := hprop.
Definition postcond := val -> hprop.

Inductive result : Type :=
  | norm : val -> result.

(** * Staged formulae *)
(** Deeply embedded due to uninterpreted functions, which cannot immediately be given a semantics without an environment. *)
Inductive flow :=
  | req : precond -> flow -> flow
  | ens : postcond -> flow
  | seq : flow -> flow -> flow
  | fex : forall A, (A -> flow) -> flow
  | fall : forall A, (A -> flow) -> flow
  | unk : var -> val -> val -> flow
  | intersect : flow -> flow -> flow
  | disj : flow -> flow -> flow.

(** An [ens] which doesn't have a useful return value.*)
Definition ens_ H := ens (fun r => \[r = vunit] \* H).
(** This carries more information than [ens (fun _ => H)], which has an #<i>arbitrary</i># return value. *)

Definition empty := ens_ \[True].

Notation req_ H := (req H empty).

(** Function environments, for interpreting unknown functions. [ufun] is a HOAS way of substituting into a staged formula, which otherwise doesn't support this due to the shallow embedding that [hprop] uses. *)
Definition ufun := val -> val -> flow.
Definition env := fmap var (option ufun).

Definition empty_env : env := Fmap.empty.

Declare Scope flow_scope.
Open Scope flow_scope.

Infix ";;" := seq (at level 38, right associativity) : flow_scope.

Notation "'∃' x1 .. xn , H" :=
  (fex (fun x1 => .. (fex (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '∃' '/ '  x1  ..  xn , '/ '  H ']'",
   only printing) : flow_scope.

(* Check (fex (fun x => ens_ \[x = vint 1];; empty)). *)
(* Check (fex (fun x => ens_ \[x = vint 1]);; empty). *)

Notation "'∀' x1 .. xn , H" :=
  (fall (fun x1 => .. (fall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '∀' '/ '  x1  ..  xn , '/ '  H ']'",
   only printing) : flow_scope.

Notation "f '$' '(' x ',' r ')'" := (unk f x r)
  (at level 80, format "f '$' '(' x ','  r ')'", only printing) : flow_scope.

(* Notation "'ens' '[' r ']' Q" := (ens (fun r => Q))
  (at level 80, format "'ens' '\[' r '\]' Q" , only printing) : flow_scope. *)
(* square brackets will conflict with format notation for boxes https://coq.inria.fr/doc/V8.20.0/refman/user-extensions/syntax-extensions.html#displaying-symbolic-notations:~:text=well%2Dbracketed%20pairs%20of%20tokens%20of%20the%20form%20%27%5B%20%27%20and%20%27%5D%27 *)

Notation "'ens' r '.' Q" := (ens (fun r => Q))
  (at level 80, format "'ens'  r '.'  Q" , only printing) : flow_scope.

(** * Interpretation of a staged formula *)
(** An [Inductive] definition is used because the rule for unknown functions is not structurally recursive. *)
Inductive satisfies : env -> heap -> heap -> result -> flow -> Prop :=

  | s_req env p (h1 h2:heap) r f
    (H: forall hp hr, (* the heap satisfying p, and the remaining heap *)
      p hp ->
      h1 = Fmap.union hr hp ->
      Fmap.disjoint hr hp ->
      satisfies env hr h2 r f) :
    satisfies env h1 h2 r (req p f)

  | s_ens env q h1 h2 r
    (H: exists v h3,
      r = norm v /\
      q v h3 /\
      h2 = Fmap.union h1 h3 /\
      Fmap.disjoint h1 h3) :
    satisfies env h1 h2 r (ens q)

  | s_seq env f1 f2 h1 h2 r
    (H: exists h3 r1,
      satisfies env h1 h3 r1 f1 /\
      satisfies env h3 h2 r f2) :
    satisfies env h1 h2 r (seq f1 f2)

  | s_fex env h1 h2 r (A:Type) (f:A->flow)
    (H: exists v,
      satisfies env h1 h2 r (f v)) :
    satisfies env h1 h2 r (@fex A f)

  | s_fall env h1 h2 r (A:Type) (f:A->flow)
    (H: forall v,
      satisfies env h1 h2 r (f v)) :
    satisfies env h1 h2 r (@fall A f)

  | s_unk env h1 h2 r fn f x
    (He: Fmap.read env fn = Some f)
    (Hr: satisfies env h1 h2 (norm r) (f x r)) :
    satisfies env h1 h2 (norm r) (unk fn x r)

  | s_intersect env h1 h2 r f1 f2
    (H1: satisfies env h1 h2 r f1)
    (H2: satisfies env h1 h2 r f2) :
    satisfies env h1 h2 r (intersect f1 f2)

  | s_disj_l env h1 h2 r f1 f2
    (H: satisfies env h1 h2 r f1) :
    satisfies env h1 h2 r (disj f1 f2)

  | s_disj_r env h1 h2 r f1 f2
    (H: satisfies env h1 h2 r f2) :
    satisfies env h1 h2 r (disj f1 f2).

Notation "env ','  h1 ','  h2 ','  r  '|=' f" :=
  (satisfies env h1 h2 r f) (at level 30, only printing).

(** The result of a staged formula, written in the paper as [Φ[r]]. Because it relates a formula and a value here (and not a variable, as in the paper), we need a model for the formula to talk about the value. *)
Definition flow_res (f:flow) (v:val) : Prop :=
  forall h1 h2 env v1, satisfies env h1 h2 (norm v1) f -> v1 = v.

Definition flow_res_in_env (f:flow) (v:val) env : Prop :=
  forall h1 h2 v1, satisfies env h1 h2 (norm v1) f -> v1 = v.

Definition has_no_result f :=
  forall env h1 h2 r, satisfies env h1 h2 r f -> r = norm vunit.

(** * Entailment *)
(** This sequent is useful for (interactive) proofs involving functions. *)
Definition entails_under env f1 f2 :=
  forall h1 h2 r,
    satisfies env h1 h2 r f1 -> satisfies env h1 h2 r f2.

(** General entailments which work for arbitrary environments. *)
Definition entails (f1 f2:flow) : Prop :=
  forall env h1 h2 r, satisfies env h1 h2 r f1 -> satisfies env h1 h2 r f2.

Definition bientails (f1 f2:flow) : Prop :=
  forall h1 h2 r env,
    satisfies env h1 h2 r f1 <-> satisfies env h1 h2 r f2.

Infix "⊑" := entails (at level 90, right associativity) : flow_scope.

Notation "env '⊢' f1 '⊑' f2" :=
  (entails_under env f1 f2) (at level 90, only printing) : flow_scope.

(* Unset Printing Notations. Set Printing Coercions. Set Printing Parentheses. *)
(* Check (forall f1 f2 f3, f1 ;; f3 ⊑ f2). *)

(** * Rewriting *)
Instance entails_refl : Reflexive entails.
Proof.
  unfold Reflexive, entails.
  intros.
  exact H.
Qed.

Instance entails_trans : Transitive entails.
Proof.
  unfold Transitive, entails.
  intros.
  auto.
Qed.

Instance entails_preorder : PreOrder entails.
Proof.
  constructor.
  apply entails_refl.
  apply entails_trans.
Qed.

Instance entails_under_refl : forall env, Reflexive (entails_under env).
Proof.
  unfold Reflexive, entails_under.
  intros.
  exact H.
Qed.

Instance entails_under_trans : forall env, Transitive (entails_under env).
Proof.
  unfold Transitive, entails_under.
  intros.
  auto.
Qed.

Instance entails_under_preorder : forall env, PreOrder (entails_under env).
Proof.
  constructor.
  apply entails_under_refl.
  apply entails_under_trans.
Qed.

Instance bientails_equiv : Equivalence bientails.
Proof.
  constructor.
  - unfold Reflexive.
    unfold bientails.
    reflexivity.
  - unfold Symmetric.
    unfold bientails.
    symmetry.
    auto.
  - unfold Transitive.
    unfold bientails.
    intros.
    split.
    + intros. apply H0. apply H. easy.
    + intros. apply H. apply H0. easy.
Qed.

Infix "====>" := Morphisms.respectful (at level 80, right associativity).
Notation Proper := Morphisms.Proper.
Notation respectful := Morphisms.respectful.
Notation impl := Program.Basics.impl.
Notation flip := Basics.flip.

(** Incantations for setoid rewriting *)
Section Proprium.

  (** This reflects how entailment is contravariant in the antecedent and covariant in the consequent *)
  #[global]
  Instance Proper_entails : Proper
    (flip entails ====> entails ====> impl)
    entails.
  Proof.
    unfold entails, Proper, respectful, impl.
    intros.
    auto.
  Qed.

  #[global]
  Instance Proper_entails_under : forall env, Proper
    (flip (entails_under env) ====> entails_under env ====> impl)
    (entails_under env).
  Proof.
    unfold entails_under, Proper, respectful, impl.
    intros.
    auto.
  Qed.

  #[global]
  Instance Proper_bientails : Proper
    (bientails ====> bientails ====> iff)
    entails.
  Proof.
    unfold bientails, entails, Proper, respectful, impl.
    split; intros.
    { apply H0. apply H1. apply H. auto. }
    { apply H0. apply H1. apply H. auto. }
  Qed.

  (** entails is proper wrt satisfies *)
  #[global]
  Instance Proper_satisfies : Proper
    (eq ====> eq ====> eq ====> eq ====> entails ====> impl)
    satisfies.
  Proof.
    unfold entails, Proper, respectful, impl.
    intros. subst.
    auto.
  Qed.

  #[global]
  Instance Proper_satisfies_bi : Proper
    (eq ====> eq ====> eq ====> eq ====> bientails ====> impl)
    satisfies.
  Proof.
    unfold bientails, entails, Proper, respectful, impl.
    intros. subst.
    apply H3.
    auto.
  Qed.

  #[global]
  Instance Proper_satisfies_under : forall env, Proper
    (eq ====> eq ====> eq ====> entails_under env ====> impl)
    (satisfies env).
  Proof.
    unfold entails_under, Proper, respectful, impl.
    intros. subst.
    auto.
  Qed.

  #[global]
  Instance Proper_seq : Proper (entails ====> entails ====> entails) seq.
  Proof.
    unfold Proper, entails, respectful.
    intros.
    inverts H1 as H1; destr H1.
    constructor. exists h3. exists r1.
    eauto.
  Qed.

  #[global]
  Instance Proper_seq_entails_under : forall env,
    Proper (entails_under env ====> entails_under env ====> entails_under env) seq.
  Proof.
    unfold Proper, entails_under, respectful.
    intros.
    inverts H1 as H1; destr H1.
    constructor. exists h3. exists r1.
    split; auto.
  Qed.

  #[global]
  Instance fex_entails_under_morphism (A : Type) : forall env,
    Proper (Morphisms.pointwise_relation A (entails_under env) ====> entails_under env) (@fex A).
  Proof.
    unfold Proper, respectful, Morphisms.pointwise_relation, entails_under.
    intros.
    inverts H0 as H0. destr H0.
    constructor.
    exists v.
    apply H.
    assumption.
  Qed.

  #[global]
  Instance entails_entails_under : forall env,
    Proper (flip entails ====> entails ====> impl) (entails_under env).
  Proof.
    unfold Proper, respectful, entails_under, entails, flip, impl.
    intros.
    eauto.
  Qed.

  (* For rewriting forwad in the goal *)
  #[global]
  Instance entails_entails_under_flip : forall env,
    Proper (entails ====> flip entails ====> flip impl) (entails_under env).
  Proof.
    unfold Proper, respectful, entails_under, entails, flip, impl.
    intros.
    eauto.
  Qed.

  #[global]
  Instance bientails_entails_under : forall env,
    Proper (bientails ====> bientails ====> iff) (entails_under env).
  Proof.
    unfold Proper, respectful, entails_under, bientails, impl.
    intros.
    split; intros.
    apply H0.
    apply H1.
    apply H.
    assumption.
    apply H0.
    apply H1.
    apply H.
    assumption.
  Qed.

  #[global]
  Instance Proper_seq_bi : Proper (bientails ====> bientails ====> bientails) seq.
  Proof.
    unfold Proper, bientails, respectful.
    intros.
    split; intros.
    { inverts H1 as H1; destr H1.
      constructor. exists h3. exists r1.
      split.
      apply H; auto.
      apply H0; auto. }
    { inverts H1 as H1; destr H1.
      constructor. exists h3. exists r1.
      split.
      apply H; auto.
      apply H0; auto. }
  Qed.

  #[global]
  Instance Proper_req_entails : Proper (eq ====> entails ====> entails) req.
  Proof.
    unfold Proper, entails, respectful, flip.
    intros.
    constructor. intros.
    rewrite <- H in H2.
    inverts H1 as H1.
    specializes H1 H3 ___.
  Qed.

  #[global]
  Instance Proper_req_bi : Proper (eq ====> bientails ====> bientails) req.
  Proof.
    unfold Proper, bientails, respectful.
    intros.
    split; intros H1.
    { constructor. intros hp hr H2 H3 H4.
      rewrite <- H in H2.
      inverts H1 as H1.
      specializes H1 H3 ___.
      apply H0. assumption. }
    { constructor. intros hp hr H2 H3 H4.
      rewrite H in H2.
      inverts H1 as H1.
      specializes H1 H3 ___.
      apply H0. assumption. }
  Qed.

End Proprium.

(** * Inversion/introduction lemmas *)
Lemma ens_ret_inv : forall env h1 h2 H r,
  satisfies env h1 h2 r (ens_ H) ->
  r = norm vunit.
Proof.
  intros.
  inverts H0 as H0.
  destruct H0 as (v&h3&H1&H2&H3&H4).
  rewrite hstar_hpure_l in H2.
  destruct H2.
  congruence.
Qed.

Lemma req_pure_ret_inv : forall env h1 h2 P r,
  P ->
  satisfies env h1 h2 r (req_ \[P]) ->
  r = norm vunit.
Proof.
  intros.
  inverts H0 as H0.

  forwards: H0 empty_heap h1.
  apply hpure_intro.
  assumption.
  fmap_eq.
  fmap_disjoint.

  inverts H1 as H1. destr H1.
  rewrite hstar_hpure_l in H1.
  destruct H1.
  congruence.
Qed.

Lemma ens_empty_inv : forall env h1 h2 r,
  satisfies env h1 h2 r (ens (fun r => \[])) -> h1 = h2.
Proof.
  intros.
  inverts H as H.
  destr H.
  apply hempty_inv in H.
  subst.
  fmap_eq.
Qed.

Lemma ens_empty_intro : forall env h1 r,
  satisfies env h1 h1 r (ens (fun r => \[])).
Proof.
  intros.
  constructor.
  destruct r.
  exists v.
  exists empty_heap.
  intuition fmap_eq.
  constructor.
Qed.

Lemma ens_pure_inv : forall P env h1 h2 r,
  satisfies env h1 h2 r (ens (fun _ => \[P])) -> P /\ h1 = h2.
Proof.
  intros.
  inverts H as H.
  destr H.
  inverts H.
  inverts H2.
  intuition.
Qed.

Lemma ens_pure_inv_dep : forall P env h1 h2 v,
  satisfies env h1 h2 (norm v) (ens (fun a => \[P a])) ->
  P v /\ h1 = h2.
Proof.
  intros.
  inverts H as H. destr H.
  inverts H.
  inverts H2.
  inj H0.
  intuition.
Qed.

Lemma ens_pure_intro : forall P env h r,
  P -> satisfies env h h r (ens (fun _ => \[P])).
Proof.
  intros.
  constructor.
  destruct r.
  exists v.
  exists empty_heap.
  intuition.
  apply hpure_intro; easy.
  fmap_eq.
Qed.

Lemma ens_pure_intro_dep : forall P env h r,
  P r -> satisfies env h h (norm r) (ens (fun v => \[P v])).
Proof.
  intros.
  constructor.
  exists r.
  exists empty_heap.
  intuition.
  apply hpure_intro; easy.
  fmap_eq.
Qed.

Lemma ens_void_inv : forall env h1 h2 r H,
  satisfies env h1 h2 r (ens_ H) ->
  r = norm vunit.
Proof.
  unfold empty, ens_.
  intros.
  inverts H0 as H0. destr H0.
  rewrite hstar_hpure_l in H0.
  subst.
  intuition.
  f_equal. assumption.
Qed.

Lemma ens_void_pure_inv : forall P env h1 h2 r,
  satisfies env h1 h2 r (ens_ \[P]) -> P /\ h1 = h2 /\ r = norm vunit.
Proof.
  intros.
  inverts H as H. destr H.
  rewrite hstar_hpure_l in H. destr H.
  apply hpure_inv in H4. destr H4. subst.
  intuition.
Qed.

Lemma ens_void_pure_intro : forall P env h,
  P -> satisfies env h h (norm vunit) (ens_ \[P]).
Proof.
  intros.
  unfold ens_.
  constructor.
  exists vunit.
  exists empty_heap.
  intuition.
  rewrite hstar_hpure_r.
  intuition.
  apply hpure_intro.
  reflexivity.
  fmap_eq.
Qed.

Lemma empty_inv : forall env h1 h2 r,
  satisfies env h1 h2 r empty ->
  h1 = h2 /\ r = norm vunit.
Proof.
  unfold empty.
  intros.
  apply ens_void_pure_inv in H.
  intuition.
Qed.

Lemma empty_intro : forall env h1,
  satisfies env h1 h1 (norm vunit) empty.
Proof.
  intros.
  unfold empty, ens_.
  constructor.
  exists vunit.
  exists empty_heap.
  intuition.
  rewrite hstar_hpure_l.
  intuition.
  apply hpure_intro.
  constructor.
  fmap_eq.
Qed.

Lemma req_pure_intro : forall env h1 P,
  satisfies env h1 h1 (norm vunit) (req \[P] empty).
Proof.
  intros.
  constructor. intros.
  apply hpure_inv in H. destruct H. subst. rew_fmap.
  apply empty_intro.
Qed.

Lemma seq_ens_pure_inv : forall P env h1 h2 r f,
  satisfies env h1 h2 r (ens (fun _ => \[P]);; f) ->
  P /\ satisfies env h1 h2 r f.
Proof.
  intros.
  inverts H as H. destr H.
  apply ens_pure_inv in H0. destr H0. subst.
  intuition.
Qed.

Lemma seq_ens_pure_inv_dep : forall P env h1 h2 v f,
  satisfies env h1 h2 (norm v) (ens (fun a => \[P a]);; f) ->
  exists v1, P v1 /\ satisfies env h1 h2 (norm v) f.
Proof.
  intros.
  inverts H as H. destr H.
  destruct r1.
  lets H2: ens_pure_inv_dep P H0.
  exists v0.
  intuition.
  subst.
  intuition.
Qed.

Lemma seq_ens_void_pure_inv : forall P env h1 h2 r f,
  satisfies env h1 h2 r (ens_ \[P];; f) ->
  P /\ satisfies env h1 h2 r f.
Proof.
  intros.
  inverts H as H. destr H.
  apply ens_void_pure_inv in H0. destr H0. subst.
  intuition.
Qed.

Lemma ens_no_result : forall H,
  has_no_result (ens_ H).
Proof.
  unfold has_no_result.
  intros.
  applys ens_void_inv H0.
Qed.

(** * Tactics for simple introduction/inversion *)

Ltac finv H :=
  match type of H with
  | \[] _ => apply hempty_inv in H
  | \[_] _ => apply hpure_inv in H as (?&?)
  | (_~~>_) _ => apply hsingle_inv in H
  | (_ \* _) _ => apply hstar_inv in H as (?&?&?&?&?&?)
  | (\[_] \* _) _ => rewrite hstar_hpure_l
  | (_ \* \[_]) _ => rewrite hstar_hpure_r
  end.

Ltac fintro :=
  match goal with
  (* | |- satisfies _ _ _ _ (ens (fun _ => \[_])) => apply ens_pure_intro *)
  (* | |- satisfies _ _ _ _ (ens (fun _ => \[])) => apply ens_empty_intro *)
  | |- satisfies _ _ _ _ empty => apply empty_intro
  | |- satisfies _ _ _ _ (ens_ \[_]) => apply ens_void_pure_intro
  | |- \[] _ => apply hempty_intro
  | |- \[_] _ => apply hpure_intro
  | |- (_ \* _) (_ \u _) => apply hstar_intro
  (* | |- (\[_] \* \[_]) _ => idtac "use rewrite hstar_hpure_l or hstar_hpure_r" *)
  | |- (\[_] \* _) _ => rewrite hstar_hpure_l
  | |- (_ \* \[_]) _ => rewrite hstar_hpure_r
  (* | |- satisfies _ (req \[]) _ _ _ => apply req_empty_intro *)
  (* | |- satisfies _ (req \[];; _) _ _ _ => apply seq_req_emp_intro_l *)
  end.

Ltac fexists v :=
  match goal with
  | |- satisfies _ _ _ _ (fex _) => constructor; exists v
  end.

Ltac fdestr_rec H :=
  match type of H with
  | satisfies _ _ _ _ (fex (fun x => _)) => inverts H as H; destr H
  | satisfies _ _ _ _ (_ ;; _) => inverts H as H; destr H
  | satisfies _ _ _ _ (ens_ \[_]) => apply ens_void_pure_inv in H; destr H
  end.

Ltac fdestr_pat H pat :=
  match type of H with
  | satisfies _ _ _ _ (fex (fun x => _)) => inverts H as H; destruct H as pat
  | satisfies _ _ _ _ (_ ;; _) => inverts H as H; destruct H as pat
  | satisfies _ _ _ _ (ens_ \[_]) => apply ens_void_pure_inv in H; destruct H as pat
  end.

(** Use these on product-like things like sequencing, existentials, and ens *)
Tactic Notation "fdestr" constr(H) := fdestr_rec H.
Tactic Notation "fdestr" constr(H) "as" simple_intropattern(pat) := fdestr_pat H pat.

Ltac solve_trivial_not_indom :=
  match goal with
  | |- ~ Fmap.indom _ _ => unfold not; rewrite Fmap.indom_single_eq; intros; false
  end.

Ltac resolve_fn_in_env :=
  match goal with
  | |- Fmap.read (Fmap.update _ ?k (Some _)) ?k = _ =>
    rewrite fmap_read_update; [reflexivity | solve_trivial_not_indom]
  | |- Fmap.read (Fmap.update _ _ _) _ = _ =>
    unfold Fmap.update;
    first [
      rewrite Fmap.read_union_l; [resolve_fn_in_env | apply Fmap.indom_single] |
        rewrite Fmap.read_union_r; [resolve_fn_in_env | solve_trivial_not_indom]
    ]
  | |- Fmap.read (Fmap.single ?k (Some _)) ?k = _ =>
    rewrite Fmap.read_single; reflexivity
  (* | |- ?g => idtac "resolve_fn_in_env could not solve:"; idtac g *)
  end.

(** * Entailment and normalization rules *)
(** Covariance of ens *)
Lemma satisfies_ens : forall Q1 Q2 env h1 h2 r,
  (forall v, Q1 v ==> Q2 v) ->
  satisfies env h1 h2 r (ens Q1)->
  satisfies env h1 h2 r (ens Q2).
Proof.
  intros.
  inverts H0 as H3.
  constructor.
  destruct H3 as (v&h3&?&?&?&?).
  exists v.
  exists h3.
  intuition.
  apply H.
  easy.
Qed.

Lemma entails_ens : forall Q1 Q2,
  (forall v, Q1 v ==> Q2 v) -> entails (ens Q1) (ens Q2).
Proof.
  unfold entails. intros.
  applys* satisfies_ens.
Qed.

Lemma satisfies_ens_void : forall H1 H2 env h1 h2 r,
  H1 ==> H2 ->
  satisfies env h1 h2 r (ens_ H1) ->
  satisfies env h1 h2 r (ens_ H2).
Proof.
  intros.
  inverts H0 as H3. destruct H3 as (v&h3&?&?&?&?).
  constructor. exists v. exists h3.
  intuition.
  rewrite hstar_hpure_l in H3.
  rewrite hstar_hpure_l.
  intuition.
Qed.

Lemma entails_ens_void : forall H1 H2,
  H1 ==> H2 ->
  entails (ens_ H1) (ens_ H2).
Proof.
  unfold entails.
  intros.
  applys* satisfies_ens_void H.
Qed.

(** Contravariance of req *)
Lemma satisfies_req : forall H1 H2 env h1 h2 r f,
  H2 ==> H1 ->
  satisfies env h1 h2 r (req H1 f) ->
  satisfies env h1 h2 r (req H2 f).
Proof.
  intros.
  inverts H0 as H0.
  apply s_req.
  intros hH1 hr H3.
  (* hH1 is the heap that satisfies H1 *)
  (* hr is the starting heap of the continuation *)
  apply H in H3.
  specialize (H0 _ hr H3).
  intuition.
Qed.

Lemma entails_req : forall H1 H2 f,
  (H2 ==> H1) -> entails (req H1 f) (req H2 f).
Proof.
  unfold entails.
  intros.
  applys* satisfies_req H1.
Qed.

Lemma disj_comm : forall env h1 h2 r f1 f2,
  satisfies env h1 h2 r (disj f2 f1) ->
  satisfies env h1 h2 r (disj f1 f2).
Proof.
  intros.
  inverts H as H.
  apply s_disj_r. assumption.
  apply s_disj_l. assumption.
Qed.

(** seq is associative *)
Lemma seq_assoc : forall env h1 h2 r f1 f2 f3,
  satisfies env h1 h2 r (f1;; f2;; f3) <->
  satisfies env h1 h2 r ((f1;; f2);; f3).
Proof.
  intros.
  split; intros H.
  { inverts H as H. destruct H as (h3&r1&H1&H2).
    inverts H2 as H2. destruct H2 as (h0&r0&H3&H4).
    constructor.
    exists h0. exists r0.
    split; auto.
    constructor.
    exists h3. exists r1.
    intuition. }
  { inverts H as H. destruct H as (h3&r1&H1&H2).
    inverts H1 as H1. destruct H1 as (h0&r0&H3&H4).
    constructor.
    exists h0. exists r0.
    split; auto.
    constructor.
    exists h3. exists r1.
    intuition. }
Qed.

Lemma norm_seq_assoc : forall f1 f2 f3,
  bientails (f1;; f2;; f3) ((f1;; f2);; f3).
Proof.
  intros.
  split; intros; now apply seq_assoc.
Qed.

Lemma unk_inv : forall env h1 h2 v x f1 f r,
  Fmap.read env f = Some f1 ->
  satisfies env h1 h2 r (unk f x v) ->
  satisfies env h1 h2 r (f1 x v).
Proof.
  intros.
  inverts H0 as H0.
  rewrite H in H0.
  inj H0.
  assumption.
Qed.

Lemma unk_res_inv : forall env h1 h2 v x f1 f r,
  Fmap.read env f = Some f1 ->
  satisfies env h1 h2 r (unk f x v) ->
  r = norm v.
Proof.
  intros.
  inverts H0 as H0.
  reflexivity.
Qed.

Lemma norm_unk : forall env v f1 f x,
  Fmap.read env f = Some f1 ->
  entails_under env (unk f x v) (f1 x v).
Proof.
  unfold entails_under.
  intros.
  eapply unk_inv.
  exact H.
  assumption.
Qed.

Lemma unk_inv_conv : forall env h1 h2 v f1 f x,
  Fmap.read env f = Some f1 ->
  satisfies env h1 h2 (norm v) (f1 x v) ->
  satisfies env h1 h2 (norm v) (unk f x v).
Proof.
  unfold entails_under.
  intros.
  apply (@s_unk env0 h1 h2 v f f1 x).
  assumption.
  assumption.
Qed.

Lemma norm_forall : forall (A:Type) f1 f2_ctx,
  entails
    (f1;; fall (fun (a:A) => f2_ctx a))
    (fall (fun (a:A) => f1;; f2_ctx a)).
Proof.
  unfold entails.
  intros.
  constructor. intros v.
  inverts H as H. destruct H as (h3&r1&?&?).
  constructor.
  exists h3. exists r1.
  intuition.
  inverts H0 as H0.
  specializes H0 v.
  auto.
Qed.

(** Compaction rule 1 from the paper *)
Lemma norm_ens_false_l : forall f,
  bientails (ens_ \[False]) (ens_ \[False];; f).
Proof.
  unfold bientails.
  iff H.
  { apply ens_void_pure_inv in H.
    intuition. }
  { inverts H as H. destr H.
    apply ens_void_pure_inv in H0.
    intuition. }
Qed.

Lemma norm_ens_false : forall f,
  entails (ens_ \[False]) f.
Proof.
  unfold entails. intros.
  apply ens_void_pure_inv in H.
  intuition.
Qed.

Lemma norm_req_false : forall f f1,
  entails f (req \[False] f1).
Proof.
  unfold entails. intros.
  constructor. intros.
  apply hpure_inv in H0.
  intuition.
Qed.

Lemma norm_req_pure : forall P f,
  P -> entails (req \[P] f) f.
Proof.
  unfold entails. intros.
  inverts H0 as H0.
  specializes H0 empty_heap h1.
  forward H0. fintro. assumption.
  rew_fmap *.
Qed.

(** The converse is not true as the result would change *)
Lemma norm_seq_ens_empty : forall f,
  entails (ens_ \[];; f) f.
Proof.
  unfold entails. intros.
  inverts H as H. destruct H as (h3&r1&?&?).
  inverts H as H.
  destr H.
  rew_heap in H.
  finv H.
  subst.
  rew_fmap *.
Qed.

(** Compaction rule 2 from the paper *)
Lemma norm_empty_l : forall f,
  bientails (empty;; f) f.
Proof.
  unfold bientails, empty.
  iff H.
  { inverts H as H. destr H.
    apply ens_void_pure_inv in H0. destr H0. subst.
    assumption. }
  { constructor.
    exists h1. exists (norm vunit).
    intuition.
    apply ens_void_pure_intro; constructor. }
Qed.

Lemma norm_ens_no_result_r : forall f,
  has_no_result f ->
  bientails (f;; empty) f.
Proof.
  iff H1.
  { inverts H1 as H1. destr H1.
    specializes H H0. subst.
    apply empty_inv in H2. destr H2. subst.
    assumption. }
  { constructor.
    exists h2. exists r.
    intuition.
    specializes H H1. subst.
    apply empty_intro. }
Qed.

Lemma norm_ens_empty_r : forall H,
  bientails (ens_ H;; empty) (ens_ H).
Proof.
  intros.
  apply (@norm_ens_no_result_r (ens_ H)).
  apply ens_no_result.
Qed.

(** Compaction rule 3 from the paper. Stated this way to ensure [f] has no meaningful result. *)
Lemma norm_empty_r : forall f H,
  bientails (f;; ens_ H;; empty) (f;; ens_ H).
Proof.
  unfold bientails, empty.
  iff H1.
  { rewrite norm_ens_empty_r in H1.
    assumption. }
  { rewrite norm_ens_empty_r.
    assumption. }
Qed.

Lemma norm_seq_req_emp : forall f,
  entails (req \[] f) f.
Proof.
  unfold entails. intros.
  inverts H as H.
  specializes H empty_heap h1 ___. fintro.
Qed.

(** Reassociating req *)
Lemma satisfies_reassoc : forall H f1 f2 env h1 h2 r,
  satisfies env h1 h2 r (req H f1;; f2) ->
  satisfies env h1 h2 r (req H (f1;; f2)).
Proof.
  intros.
  inverts H0 as H0. destr H0.

  (* find out about req *)
  constructor. intros hp hr. intros.

  (* prove the req *)
  inverts H1 as H1.
  specialize (H1 hp hr H0).
  forward H1. fmap_eq.
  forward H1. fmap_disjoint.
  
  constructor.
  exists h3.
  exists r1.
  split; auto.
Qed.

Lemma norm_reassoc : forall H f1 f2,
  entails (req H f1;; f2) (req H (f1;; f2)).
Proof.
  unfold entails.
  apply satisfies_reassoc.
Qed.

(** Splitting and combining [req]s *)
Lemma norm_req_sep_combine : forall H1 H2 f,
  entails (req H1 (req H2 f)) (req (H1 \* H2) f).
Proof.
  unfold entails.
  intros.
  (* contravariance means we start reasoning from the assumptions in the goal *)
  apply s_req.
  intros hb hr. intros.
  apply hstar_inv in H0 as (hH1&hH2&?&?&?&?).

  (* start reasoning forward *)
  inverts H as H.
  forwards: (H hH1 (hr \u hH2) H0).
  fmap_eq.
  fmap_disjoint.

  inverts H8 as H8.
  specialize (H8 _ hr H5).
  forward H8. fmap_eq.
  forward H8. fmap_disjoint.

  assumption.
Qed.

Lemma norm_req_sep_split : forall H1 H2 f,
  entails (req (H1 \* H2) f) (req H1 (req H2 f)).
Proof.
  unfold entails.
  intros.

  apply s_req.
  intros hH1 hH2r. intros.
  apply s_req.
  intros hH2 hr. intros.

  inverts H as H.
  specialize (H (hH1 \u hH2) hr ltac:(apply hstar_intro; auto)).
  forward H. fmap_eq.
  forward H. fmap_disjoint.

  auto.
Qed.

(** Compaction rule 4 from the paper *)
Lemma norm_req_req : forall H1 H2 f,
  bientails (req (H1 \* H2) f) (req H1 (req H2 f)).
Proof.
  intros.
  split.
  - apply norm_req_sep_split.
  - apply norm_req_sep_combine.
Qed.

(** Splitting and combining [ens_]s *)
Lemma satisfies_ens_ens_void : forall H1 H2 env h1 h2 r,
  satisfies env h1 h2 r (ens_ (H1 \* H2)) <->
  satisfies env h1 h2 r (ens_ H1;; ens_ H2).
Proof.
  intros.
  split; intros.
  { inverts H as H. destruct H as (v&h3&H3&H4&H5&H6).
    rewrite hstar_hpure_l in H4. destruct H4 as (H4&H7).
    (* h3 is the heap that H1 and H2 together add *)
    (* find the intermediate heap *)
    apply hstar_inv in H7. destruct H7 as (h0&h4&H8&H9&H10&H11).
    (* H1 h0, H2 h4 *)
    constructor.
    exists (h1 \u h0).
    exists (norm vunit).
    split.
    { constructor. exists vunit. exists h0. intuition. rewrite hstar_hpure_l. intuition. }
    { constructor. exists v. exists h4. intuition. rewrite hstar_hpure_l. intuition. fmap_eq. } }
  { inverts H as H.
    destruct H as (h3&r1&H3&H4).
    (* give up on careful reasoning *)
    inverts H3 as H5. destr H5. inverts H4 as H8. destr H8.
    rewrite hstar_hpure_l in H0.
    rewrite hstar_hpure_l in H5.
    intuition.
    constructor.
    exists v0.
    exists (h0 \u h4).
    intuition.
    subst.
    rewrite <- hstar_assoc.
    apply hstar_intro.
    rewrite hstar_hpure_l.
    intuition.
    intuition.
    fmap_disjoint.
    fmap_eq. }
Qed.

Lemma norm_ens_ens_void : forall H1 H2,
  bientails (ens_ (H1 \* H2)) (ens_ H1;; ens_ H2).
Proof.
  intros; split; apply satisfies_ens_ens_void.
Qed.

(** Compaction rule 5 from the paper *)
Lemma norm_ens_ens_void_l : forall H Q,
  bientails (ens_ H;; ens Q) (ens (Q \*+ H)).
Proof.
  unfold entails.
  split; intros.
  { inverts H0 as H0. destr H0.
    inverts H1 as H1. destr H1.
    inverts H2 as H2. destr H2.
    constructor.
    exists v0.
    exists (h0 \u h4).
    intuition.
    rewrite hstar_hpure_l in H1.
    rewrite hstar_comm.
    apply hstar_intro; intuition auto.
    fmap_eq. }
  { inverts H0 as H0. destr H0.
    apply hstar_inv in H0. destr H0.
    constructor.
    exists (h1 \u h4).
    exists (norm vunit).
    split.
    { constructor.
      exists vunit.
      exists h4.
      intuition.
      rewrite hstar_hpure_l.
      intuition. }
    { constructor.
      exists v.
      exists h0.
      intuition.
      fmap_eq. } }
Qed.

(** Splitting and combining [ens] with results is more complex, and there does not seem to be a single equivalence. *)
Lemma satisfies_ens_sep_combine : forall Q1 Q2 env h1 h2 r,
  satisfies env h1 h2 r (ens Q1;; ens Q2) ->
  satisfies env h1 h2 r (ens (fun r0 : val => \exists r1 : val, Q1 r1 \* Q2 r0)).
Proof.
  intros.
  fdestr H as (h3&r1&H1&H2).

  constructor. destruct r.
  exists v.
  inverts H1 as H1. destruct H1 as (v0&h0&?&?&?&?).
  inverts H2 as H2. destruct H2 as (v1&h4&?&?&?&?).
  exists (h0 \u h4).
  intuition.
  apply hexists_intro with (x := v0).

  apply hstar_intro; auto.
  subst. inj H2. assumption.
  subst. fmap_eq.
Qed.

Lemma norm_ens_ens_combine : forall Q1 Q2,
  entails (ens Q1;; ens Q2) (ens (fun r => \exists r1, Q1 r1 \* Q2 r)).
Proof.
  unfold entails.
  apply satisfies_ens_sep_combine.
Qed.

Lemma satisfies_ens_sep_split : forall H Q env h1 h2 r,
  satisfies env h1 h2 r (ens (Q \*+ H)) ->
  satisfies env h1 h2 r (ens (fun _ : val => H);; ens Q).
Proof.
  intros.
  inverts H0 as H0.
  destruct H0 as (v & h3 & H1 & H2 & H3 & H4).
  (* h3 is the part satisfying both *)
  apply hstar_inv in H2.
  destruct H2 as (h0 & h4 & ? & ? & ? & ?).
  (* h0 is the part satisfying Q, h4 H *)

  constructor.
  exists (h1 \u h4).
  exists (norm v). (* anything? *)
  split.

  constructor.
  eexists.
  eexists.
  intuition.
  auto.

  constructor.
  exists v.
  exists h0.
  intuition.
  subst.
  fmap_eq.
Qed.

Lemma norm_ens_split : forall H Q,
  entails (ens (Q \*+ H)) (ens (fun _ => H);; ens Q).
Proof.
  unfold entails.
  apply satisfies_ens_sep_split.
Qed.

(** Rule EntEns from the paper *)
Lemma entails_ens_seq : forall H1 H2 f1 f2,
  H1 ==> H2 ->
  entails f1 f2 ->
  entails (ens_ H1;; f1) (ens_ H2;; f2).
Proof.
  unfold entails.
  intros.
  inverts H3 as H3. destr H3.
  apply (satisfies_ens_void H) in H4.
  constructor. exists h3. exists r1.
  intuition.
Qed.

(** Rule EntReq from the paper *)
Lemma entails_req_seq : forall H1 H2 f1 f2,
  H2 ==> H1 ->
  entails f1 f2 ->
  entails (req H1 f1) (req H2 f2).
Proof.
  unfold entails.
  intros.
  constructor. intros hH2 h3. intros.
  inverts H3 as H3. specializes H3 hH2 h3.
Qed.

(** Rule DisjLeft from the paper *)
Lemma entails_disj_left : forall f1 f2 f3,
  entails f1 f3 ->
  entails f2 f3 ->
  entails (disj f1 f2) f3.
Proof.
  unfold entails.
  intros.
  inverts H1 as H1; auto.
Qed.

(** Half of DisjRight from the paper *)
Lemma entails_disj_right_l : forall f1 f2 f3,
  entails f3 f1 ->
  entails f3 (disj f1 f2).
Proof.
  unfold entails.
  intros.
  apply s_disj_l.
  auto.
Qed.

(** The other half of DisjRight from the paper *)
Lemma entails_disj_right_r : forall f1 f2 f3,
  entails f3 f2 ->
  entails f3 (disj f1 f2).
Proof.
  unfold entails.
  intros.
  apply s_disj_r.
  auto.
Qed.

(** EntFunc *)
Lemma entails_func : forall f x r,
  entails (unk f x r) (unk f x r).
Proof.
  intros.
  apply entails_refl.
Qed.

(** * Biabduction *)
(** Simplified definition following #<a href="http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/popl09.pdf">Compositional Shape Analysis by means of Bi-Abduction</a># (Fig 1). *)
Inductive biab : hprop -> hprop -> hprop -> hprop -> Prop :=

  | b_base_empty : forall Hf,
    biab \[] Hf \[] Hf

  | b_pts_match : forall a b H1 H2 Ha Hf x,
    biab Ha H1 H2 Hf ->
    biab (\[a=b] \* Ha) (x~~>a \* H1) (x~~>b \* H2) Hf

  | b_pts_diff : forall a b H1 H2 Ha Hf x y,
    (* x <> y -> *)
    biab Ha H1 H2 Hf ->
    biab (y~~>b \* Ha) (x~~>a \* H1) (y~~>b \* H2) (x~~>a \* Hf).

Lemma b_pts_single : forall x a b,
  biab \[a=b] (x~~>a) (x~~>b) \[].
Proof.
  intros.
  rewrite <- (hstar_hempty_r (x~~>a)).
  rewrite <- (hstar_hempty_r (x~~>b)).
  applys_eq b_pts_match.
  instantiate (1 := \[]).
  xsimpl.
  intuition.
  intuition.
  apply b_base_empty.
Qed.

Lemma b_pts_diff_single : forall x y a b,
  biab (y~~>b) (x~~>a) (y~~>b) (x~~>a).
Proof.
  intros.
  rewrite <- (hstar_hempty_r (x~~>a)).
  rewrite <- (hstar_hempty_r (y~~>b)).
  applys_eq b_pts_diff.
  apply b_base_empty.
Qed.

Lemma biab_sound : forall Ha H1 H2 Hf,
  biab Ha H1 H2 Hf ->
  Ha \* H1 ==> H2 \* Hf.
Proof.
  intros.
  induction H.
  { xsimpl. }
  { xsimpl; auto. }
  { xsimpl; auto. }
Qed.

(** Biabduction for a single location. *)
Lemma biab_single : forall x a env h1 h2 r H1 H2 f,
  satisfies env h1 h2 r (ens_ (x~~>a \* H1);; req (x~~>a \* H2) f)->
  satisfies env h1 h2 r (ens_ H1;; req H2 f).
Proof.
  intros.
  inverts H as H. destruct H as (h3&r1&H3&H4).
  (* ens adds a location to the heap *)
  inverts H3 as H3.
  (* use that to figure out what is in h3 *)
  destr H3. finv H0. finv H0. finv H5. subst h3 h0 x0 x1. rew_fmap *.

  (* prove just the first part *)
  rewrite norm_req_req in H4.
  inverts H4 as H4.
  specialize (H4 _ (h1 \u x3) H5).
  forward H4. fmap_eq.
  forward H4. fmap_disjoint.

  constructor. exists (h1 \u x3). exists r1.
  split.
  { constructor. eexists. exists x3.
    intuition.
    exact H.
    rewrite hstar_hpure_l. intuition. }
  { assumption. }
Qed.

(** We can remove a framing heap [hf] from both sides of a [satisfies] if it is disjoint from the part of the heap satisfying [ens_ H]. *)
Lemma ens_reduce_frame : forall env h1 h hf r H,
  H h ->
  Fmap.disjoint h (hf \u h1) ->
  satisfies env (hf \u h1) (hf \u h1 \u h) r (ens_ H) ->
  satisfies env h1 (h1 \u h) r (ens_ H).
Proof.
  introv H0 Hd. intros.
  inverts H1 as H1. destr H1.
  rewrite hstar_hpure_l in H1. destr H1.

  constructor. exists v. exists h3.
  intuition.
  rewrite hstar_hpure_l. intuition.
  fmap_eq.

  forwards: Fmap.union_eq_inv_of_disjoint (hf \u h1) h h3.
  fmap_disjoint.
  fmap_disjoint.
  { asserts_rewrite (h \u hf \u h1 = hf \u h1 \u h). fmap_eq.
    asserts_rewrite (h3 \u hf \u h1 = (hf \u h1) \u h3). fmap_eq.
    assumption. }

  assumption.
Qed.

(** The [Float Pre] rule (compaction 6) from the paper. *)
Lemma norm_ens_req_transpose : forall H1 H2 Ha Hf (v:val) f,
  biab Ha (H1 v) H2 (Hf v) ->
  entails (ens_ (H1 v);; (req H2 f))
    (req Ha (ens_ (Hf v);; f)).
Proof.
  unfold entails.
  introv Hbi.
  induction Hbi.

  { (* base case *)
    introv H2.
    constructor. intros. finv H. subst hp. rew_fmap *. subst hr. clear H3.
    inverts H2 as H2. destr H2.
    constructor. exists h3. exists r1.
    intuition.

    inverts H2 as H2.
    specialize (H2 empty_heap h3).
    forward H2. fintro.
    forward H2. fmap_eq.
    forward H2. fmap_disjoint.

    assumption. }

  { (* b_pts_match *)
    intros.

    (* use the req *)
    rewrite norm_req_req.
    constructor. intros. finv H3. subst. rew_fmap.

    apply (IHHbi env0).
    apply (biab_single H). }

  { (* b_pts_diff *)
    introv H3.
    (* the idea of this proof is to demonstrate that we can commute adding x~~>a and removing y~~>b by showing that we can start from a heap without x~~>a (using the lemma ens_reduce_frame), perform the operations, and arrive at the same result. reasoning semantically is quite nasty. maybe we can come up with a way to push y~~>b past H0? *)

    (* h4 -(+h7)-> h3 -(-hyb)-> h5+hxa+h7 -> h2
                  ||
                  h4+h7
                = (h5+hyb+hxa)+h7 *)

    (* extract x~~>a *)
    inverts H3 as H3. destruct H3 as (h3&r0&H3&H4).
    rewrite norm_ens_ens_void in H3.
    inverts H3 as H3. destruct H3 as (h4&r1&H3&H5).
    inverts H3 as H3. destruct H3 as (v0&hxa&?&H6&?&?).
    rewrite hstar_hpure_l in H6. destr H6.

    (* extract y~~>b *)
    rewrite norm_req_req.
    constructor; intros hyb h5. intros.
    constructor; intros hHa h6. intros H13. intros.

    (* supply x~~>a *)
    rewrite norm_ens_ens_void.
    rewrite <- norm_seq_assoc.
    constructor. exists (h6 \u hxa). exists (norm vunit).
    split.
    { constructor. exists vunit. exists hxa.
      intuition. rewrite hstar_hpure_l. intuition. }

    (* need to subtract a heap from both sides of H5 *)
    (* that heap is y~~>2 *)

    (* find out about the heap we need *)
    pose proof H5 as HensH0. (* copy, as we're about to invert and destroy this *)
    inverts H5 as H5; destruct H5 as (v1&h7&?&H16&?&?).
    rewrite hstar_hpure_l in H16. destruct H16 as (?&H20).

    (* reduce ens on the left *)
    pose proof (ens_reduce_frame) as Hreduce.
    specializes Hreduce env0 (h5 \u hxa) h7 hyb.
    specializes Hreduce r0 H20.
    forward Hreduce. fmap_disjoint.
    asserts_rewrite (h4 = hyb \u h5 \u hxa) in HensH0. fmap_eq.
    asserts_rewrite (h3 = hyb \u (h5 \u hxa) \u h7) in HensH0. fmap_eq.
    apply Hreduce in HensH0.

    (* provide the heap for y~~>b *)
    rewrite norm_req_req in H4.
    inverts H4 as H4.
    specializes H4 hyb (h5 \u hxa \u h7) H6 ___.

    lets Hseq: s_seq env0 (ens_ H0) (req H2 f) (h5 \u hxa) h2.
    forwards: Hseq r.
    { exists (h5 \u hxa \u h7).
      exists r0.
      split.
      applys_eq HensH0. fmap_eq.
      assumption. }
    (* got the seq... now we can use the IH *)

    forwards H21: IHHbi env0 (h5 \u hxa) H18.
    inverts H21 as H26.
    applys H26 H13.
    fmap_eq.
    fmap_disjoint. }
Qed.

Module BiabductionExamples.

  (** [(a=3) * x->a*y->b |- x->3 * (y->b)] *)
  Example ex1_biab : forall x y,
    exists Ha Hf a, biab Ha (x~~>vint a \* y~~>vint 2) (x~~>vint 3) Hf.
  Proof.
    intros.
    eexists.
    eexists.
    eexists.
    rewrite <- (hstar_hempty_r (x ~~> vint 3)) at 2.
    apply b_pts_match.
    apply b_base_empty.
  Qed.

  (* we can see from the ex_intro constrs that the frame is y->2, and the abduced contraint is trivial but gives a value to a, which was immediately substituted *)
  (* Print ex1_biab. *)

  Example ex2_biab : forall x y,
    (* x <> y -> *)
    exists Ha Hf, biab Ha (x~~>vint 2) (y~~>vint 3) Hf.
  Proof.
    intros.
    eexists. eexists.
    rewrite <- (hstar_hempty_r (x ~~> vint 2)).
    rewrite <- (hstar_hempty_r (y ~~> vint 3)).
    lets H1: b_pts_diff.
    apply H1.
    apply b_base_empty.
  Qed.

  (* Print ex2_biab. *)

  (** Example from Appendex D of the paper *)
  Example ex3_intersection : forall x y a b,
    entails (ens_ (x~~>a);; req_ (y~~>b))
      (intersect (req_ \[x=y /\ a=b])
        (req (y~~>b) (ens_ (x~~>a)))).
  Proof.
    intros.
    constructor.
    { constructor. intros.
      apply hpure_inv in H0. destr H0. subst.

      rewrite norm_ens_req_transpose in H;
      only 2: apply b_pts_single.

      simpl in H.
      inverts H as H. specializes H empty_heap hr ___.
      apply hpure_intro.
      reflexivity.
      fmap_eq.

      apply norm_seq_ens_empty in H.
      assumption. }
    { rewrite norm_ens_req_transpose in H; only 2: apply b_pts_diff_single.
      pose proof (norm_ens_empty_r (x~~>a)) .
      rewrite (norm_ens_empty_r (x~~>a)) in H.
      assumption. }
  Qed.

End BiabductionExamples.

(** * Lemmas about entailment sequents *)
Lemma ent_ens_l : forall env f P,
  (P -> entails_under env empty f) ->
  entails_under env (ens_ \[P]) f.
Proof.
  unfold entails_under. intros.
  fdestr H0. subst.
  apply H.
  assumption.
  fintro.
Qed.

Lemma ent_seq_ens_l : forall env f f1 P,
  (P -> entails_under env f1 f) ->
  entails_under env (ens_ \[P];; f1) f.
Proof.
  unfold entails_under. intros.
  fdestr H0.
  fdestr H1.
  apply H.
  assumption.
  subst.
  auto.
Qed.

Lemma ent_ens_single : forall env P P1,
  (P1 -> P) ->
  entails_under env (ens_ \[P1]) (ens_ \[P]).
Proof.
  unfold entails_under. intros.
  fdestr H0.
  constructor. exists vunit. exists empty_heap.
  apply H in H1.
  intuition.
  fintro.
  intuition.
  fintro.
  assumption.
  fmap_eq.
Qed.

Lemma ent_seq_unk : forall fn fn1 f1 f2 env x r,
  Fmap.read env fn = Some fn1 ->
  entails_under env (fn1 x r;; f1) f2 ->
  entails_under env (unk fn x r;; f1) f2.
Proof.
  intros.
  rewrites (>> norm_unk env0); [ apply H | ].
  assumption.
Qed.

Lemma ent_disj_left : forall f1 f2 f3 env,
  entails_under env f1 f3 ->
  entails_under env f2 f3 ->
  entails_under env (disj f1 f2) f3.
Proof.
  unfold entails_under. intros.
  inverts H1 as H1; auto.
Qed.

Lemma ent_seq_disj : forall f1 f2 f3 f4 env,
  entails_under env (f1;; f3) f4 ->
  entails_under env (f2;; f3) f4 ->
  entails_under env (disj f1 f2;; f3) f4.
Proof.
  unfold entails_under. intros.
  fdestr H1.
  inverts H2 as H2.
  { apply H.
    constructor. eexists. eexists.
    split. apply H2. apply H3. }
  { apply H0.
    constructor. eexists. eexists.
    split. apply H2. apply H3. }
Qed.

Lemma ent_seq_ex_l : forall A (f1: A -> flow) f2 f3 env,
  (forall x, entails_under env (f1 x;; f2) f3) ->
  entails_under env (fex (fun x => f1 x);; f2) f3.
Proof.
  unfold entails_under. intros.
  fdestr H0.
  fdestr H1.
  applys H v.
  constructor.
  eexists.
  eexists.
  split.
  apply H0.
  apply H2.
Qed.

Lemma ent_ex_l : forall f A (fctx:A -> flow) env,
  (forall x, entails_under env (fctx x) f) ->
  entails_under env (fex (fun x => fctx x)) f.
Proof.
  unfold entails_under. intros.
  fdestr H0.
  specializes H H1.
  auto.
Qed.

Lemma ent_ex_r : forall f A (fctx:A -> flow) env,
  (exists x, entails_under env f (fctx x)) ->
  entails_under env f (fex (fun x => fctx x)).
Proof.
  unfold entails_under. intros.
  destr H.
  constructor. exists x.
  auto.
Qed.

Lemma ent_ex : forall A (fctx fctx1:A -> flow) env,
  (forall x, entails_under env (fctx x) (fctx1 x)) ->
  entails_under env (fex (fun x => fctx x)) (fex (fun y => fctx1 y)).
Proof.
  unfold entails_under. intros.
  fdestr H0.
  constructor. exists v.
  auto.
Qed.

Lemma ent_seq_ex_reassoc : forall A f f1,
  bientails (fex (fun (x:A) => f x);; f1) (fex (fun (x:A) => f x;; f1)).
Proof.
  intros. split; intros.
  { fdestr H. fdestr H0.
    constructor. exists v.
    constructor. exists h3. exists r1. intuition. }
  { fdestr H. fdestr H0.
    constructor. exists h3. exists r1.
    split.
    constructor. exists v. assumption. assumption. }
Qed.

(** * High-level tactics *)
Ltac funfold_hyp H env f :=
  rewrites (>> norm_unk env f) in H; [ unfold env; resolve_fn_in_env | ].

Ltac funfold_ env f :=
  rewrites (>> norm_unk env f); [ unfold env; resolve_fn_in_env | ].

Tactic Notation "funfold" constr(env) constr(f) := funfold_ env f.
Tactic Notation "funfold" constr(env) constr(f) "in" constr(H) := funfold_hyp H env f.

Ltac ent_step :=
  match goal with

  (* assume things on the left side *)
  | |- entails_under _ (disj _ _) _ =>
    simple apply ent_disj_left
  | |- entails_under _ (fex (fun y => _)) _ =>
    let x := fresh y in
    simple apply ent_ex_l; intros x
  | |- entails_under _ (fex (fun _ => _);; _) _ =>
    rewrite ent_seq_ex_reassoc
  | |- entails_under _ (ens_ \[_];; _) _ =>
    let H := fresh "H" in
    simple apply ent_seq_ens_l; intros H

  (* if there is an IH, try to use it *)
  | IH: context[entails_under ?env (unk _ _ _) _] |-
    context[unk ?f _ _] =>

    (* if it fails, try to resolve it from the environment *)
    first [
      (* TODO unfortunately this immediately tries the IH. we need to delay it until we've unfolded at least once *)
        rewrite IH; [ | subst; auto ]
      (* | rewrite (@norm_unk env); [ | unfold env; resolve_fn_in_env ]; simpl *)
      (* | funfold env f *)
    ]

  (* if there is no IH, try to resolve from the environment *)
  | |- entails_under ?env (unk ?f _ _) _ =>
    (* rewrite (@norm_unk env); [ | unfold env; resolve_fn_in_env ]; simpl *)
    funfold env f; simpl

  (* try to work on the right side *)
  | |- entails_under _ _ (fex (fun _ => _)) =>
    simple apply ent_ex_r; eexists
  | |- entails_under _ (ens_ \[_]) (ens_ \[_]) =>
    simple apply ent_ens_single; subst; intuition

    (* if all else fails, try basic tactics to hopefully get other steps to apply *)
    | H: _ /\ _ |- _ =>
      destruct H
    | _: ?v = ?w |- _ =>
      first [subst v | subst w]

    (* after we've tried everything, try to solve *)
    | |- _ = _ =>
      solve [simpl; simple apply eq_refl]
      (* https://coq.inria.fr/doc/master/refman/proofs/writing-proofs/proof-mode.html#coq:flag.Solve-Unification-Constraints *)
      (* solve [solve_constraints; reflexivity] *)

    (* always have a no-match so we can repeat this *)
    | |- ?g => idtac "no match"; idtac g; fail
    end.

  Ltac solve_entailment :=
    repeat ent_step.

(** * Big-step semantics *)
Inductive eresult : Type :=
  | enorm : val -> eresult.

(** Program environment *)
Definition penv := fmap var (option (val -> expr)).
Definition empty_prenv : env := Fmap.empty.

Inductive bigstep : penv -> heap -> expr -> heap -> eresult -> Prop :=
  | eval_pval : forall h v env,
    bigstep env h (pval v) h (enorm v)

  (* there is no var rule *)

  | eval_plet : forall h1 h3 h2 x e1 e2 v r env,
    bigstep env h1 e1 h3 (enorm v) ->
    bigstep env h3 (subst x v e2) h2 r ->
    bigstep env h1 (plet x e1 e2) h2 r

  | eval_padd : forall h x y env,
    bigstep env h (padd (pval (vint x)) (pval (vint y))) h (enorm (vint (x + y)))

  | eval_pminus : forall h x y env,
    bigstep env h (pminus (pval (vint x)) (pval (vint y))) h (enorm (vint (x - y)))

  | eval_pfun : forall h x e env,
    bigstep env h (pfun x e) h (enorm (vfun x e))

  | eval_pfix : forall h x e f env,
    bigstep env h (pfix f x e) h (enorm (vfix f x e))

  | eval_app_fun : forall v1 v2 h x e r env,
    v1 = vfun x e ->
    bigstep env h (subst x v2 e) h r ->
    bigstep env h (papp (pval v1) (pval v2)) h r

  | eval_app_fix : forall v1 v2 h x e r fn env,
    v1 = vfix fn x e ->
    bigstep env h (subst x v2 (subst fn v1 e)) h r ->
    bigstep env h (papp (pval v1) (pval v2)) h r

  | eval_app_unk : forall va h r f fn env,
    Fmap.read env fn = Some f ->
    bigstep env h (f va) h r ->
    bigstep env h (papp (pvar fn) (pval va)) h r

  | eval_pif_true : forall h1 h2 r e1 e2 env,
    bigstep env h1 e1 h2 r ->
    bigstep env h1 (pif (vbool true) e1 e2) h2 r

  | eval_pif_false : forall h1 h2 r e1 e2 env,
    bigstep env h1 e2 h2 r ->
    bigstep env h1 (pif (vbool false) e1 e2) h2 r

  | eval_pref : forall h v p env,
    ~ Fmap.indom h p ->
    bigstep env h (pref v) (Fmap.update h p v) (enorm (vloc p))

  | eval_pderef : forall h p env,
    Fmap.indom h p ->
    bigstep env h (pderef (vloc p)) h (enorm (Fmap.read h p))

  | eval_passign : forall h p v env,
    Fmap.indom h p ->
    bigstep env h (passign (vloc p) v) (Fmap.update h p v) (enorm vunit)

  | eval_passert : forall h env,
    bigstep env h (passert (vbool true)) h (enorm vunit).

(* Definition compatible r1 r2 :=
  match (r1, r2) with
  | (norm r3, enorm r4) => r3 = r4
end. *)

(** * Program logic rules *)
Inductive forward : expr -> flow -> Prop :=
  | fw_val: forall n,
    forward (pval n) (ens (fun res => \[res = n]))

  (* there is no need for fw_var/a store because substitution will take care of it before it is reached *)

  | fw_let: forall x e1 e2 f1 f2 v,
    forward e1 f1 ->
    flow_res f1 v ->
    forward (subst x v e2) f2 ->
    forward (plet x e1 e2) (f1 ;; f2)

  | fw_if: forall b e1 e2 f1 f2,
    forward e1 f1 ->
    forward e2 f2 ->
    forward (pif b e1 e2) (disj f1 f2)

  | fw_deref: forall x,
    forward (pderef (vloc x))
      (fall (fun y => (req (x~~>y)
        (ens (fun res => \[res = y] \* x~~>y)))))

  | fw_ref: forall v,
    forward (pref v) (fex (fun y =>
      (ens (fun r => \[r = vloc y] \* y~~>v))))

  | fw_assign: forall x y v,
    forward (passign (vloc x) y)
      (req (x~~>v) (ens_ (x~~>y)))

  | fw_assert: forall b,
    forward (passert (vbool b)) (req_ \[b = true])

  | fw_app_fun: forall vf x e va f,
    vf = vfun x e ->
    forward (subst x va e) f ->
    forward (papp (pval vf) (pval va)) f

  | fw_app_fix: forall vf x e va f fn,
    vf = vfix fn x e ->
    forward (subst x va (subst fn vf e)) f ->
    forward (papp (pval vf) (pval va)) f

  | fw_app_unk: forall f va,
    forward (papp (pvar f) (pval va)) (fex (fun r => unk f va r)).


Module Soundness.

  (** * Semantic tuples *)
  (** A #<i>semantic tuple</i># is our equivalent of a Hoare triple: a valid one ensures ensures that the given program satisfies the given specification. *)
  (** The use of "tuple" alludes to the fact that we may constrain the program with an arbitrary number of pre- and postconditions. *)
  Definition tuple_valid_under penv env e f : Prop :=
    forall h1 h2 v,
      bigstep penv h1 e h2 (enorm v) -> satisfies env h1 h2 (norm v) f.

  (** Roughly, this says that for every binding in the program environment, we can find a "corresponding" one in the spec environment, where "corresponding" means related by a valid semantic tuple. *)
  Definition env_compatible penv env :=
    forall pfn f x,
      Fmap.read penv f = Some pfn ->
      exists sfn, Fmap.read env f = Some sfn /\
      forall v, tuple_valid_under penv env (pfn x) (sfn x v).

  (** The full definition requires compatible environments. *)
  Definition sem_tuple (e: expr) (f: flow) : Prop :=
    forall penv env,
      env_compatible penv env -> tuple_valid_under penv env e f.

  #[global]
  Instance Proper_sem_tuple : Proper
    (eq ====> entails ====> impl)
    sem_tuple.
  Proof.
    unfold entails, Proper, respectful, impl, sem_tuple, tuple_valid_under.
    intros. subst.
    eauto.
  Qed.

  (** Structural rules *)
  Lemma sem_consequence : forall f1 f2 e,
    entails f2 f1 ->
    sem_tuple e f2 ->
    sem_tuple e f1.
  Proof.
    introv He H.
    unfold sem_tuple. intros.
    rewrite He in H.
    eauto.
  Qed.

  (** Rules for program constructs *)
  Lemma sem_pval: forall n,
    sem_tuple (pval n) (ens (fun res => \[res = n])).
  Proof.
    unfold sem_tuple. introv Hc Hb.
    (* appeal to how e executes to tell us about the heaps *)
    inverts Hb as Hb.
    (* justify that the staged formula describes the heap *)
    apply ens_pure_intro_dep.
    reflexivity.
  Qed.

  Lemma sem_plet: forall x e1 e2 f1 f2 v,
    sem_tuple e1 f1 ->
    flow_res f1 v ->
    sem_tuple (subst x v e2) f2 ->
    sem_tuple (plet x e1 e2) (f1;; f2).
  Proof.
    intros.
    unfold sem_tuple, tuple_valid_under. introv Hc Hb.

    (* reason about how the let executes *)
    inverts Hb as. introv He1 He2.

    (* use the semantic tuple we have about e1 *)
    unfold sem_tuple in H.
    lets H3: H env0 He1. exact Hc. clear H He1. sort.

    (* we need to know that spec value and program value are the same *)
    specializes H0 H3. subst.

    (* know about f2 *)
    specializes H1 env0 h3 h2 v0 He2. clear He2.

    constructor. exists h3. exists (norm v).
    intuition.
  Qed.

  Lemma sem_pif: forall b e1 e2 f1 f2,
    sem_tuple e1 f1 ->
    sem_tuple e2 f2 ->
    sem_tuple (pif b e1 e2) (disj f1 f2).
  Proof.
    introv Ht Hf.
    unfold sem_tuple. introv Hc Hb.
    inverts Hb as Hb.
    { (* true *)
      unfold sem_tuple in Ht.
      specializes Ht env0 Hb.
      now apply s_disj_l. }
    { (* false *)
      unfold sem_tuple in Hf.
      specializes Hf env0 Hb.
      now apply s_disj_r. }
  Qed.

  Lemma sem_pderef: forall x,
    sem_tuple (pderef (vloc x))
      (fall (fun y => (req (x~~>y)
        (ens (fun res => \[res = y] \* x~~>y))))).
  Proof.
    intros. unfold sem_tuple. introv Hc Hb.
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
    sem_tuple (pref v) (fex (fun y =>
      (ens (fun r => \[r = vloc y] \* y~~>v)))).
  Proof.
    intros.
    unfold sem_tuple. introv Hc Hb.
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
    sem_tuple (passign (vloc x) y)
      (req (x~~>v) (ens_ (x~~>y))).
  Proof.
    intros.
    unfold sem_tuple. introv Hc Hb.
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
    sem_tuple (passert (vbool b)) (req_ \[b = true]).
  Proof.
    intros.
    unfold sem_tuple. introv Hc Hb.
    inverts Hb as Hb.
    constructor.
    intros.
    apply hpure_inv in H. destruct H. rewrite H2 in H0. rew_fmap. rewrite H0.
    apply empty_intro.
  Qed.

  Lemma sem_papp_fun: forall vf x e va f,
    vf = vfun x e ->
    sem_tuple (subst x va e) f ->
    sem_tuple (papp (pval vf) (pval va)) f.
  Proof.
    intros. subst.
    unfold sem_tuple. introv Hc Hb.
    inverts Hb as.
    { introv H Hb.
      injection H; intros; subst e0 x0; clear H.
      unfold sem_tuple in H0.
      specializes H0 env0 Hb. }
    { intros. false. }
  Qed.

  Lemma sem_papp_fix: forall vf x e va f fn,
    vf = vfix fn x e ->
    sem_tuple (subst x va (subst fn vf e)) f ->
    sem_tuple (papp (pval vf) (pval va)) f.
  Proof.
    intros. subst.
    unfold sem_tuple. introv Hc Hb.
    inverts Hb as.
    { intros. false. }
    { introv H Hb. injection H; intros; subst e0 x0 fn0; clear H.
      unfold sem_tuple in H0.
      specializes H0 env0 Hb. }
  Qed.

  Lemma sem_papp_unk: forall f va,
    sem_tuple (papp (pvar f) (pval va)) (fex (fun r => unk f va r)).
  Proof.
    intros.
    unfold sem_tuple. introv Hc Hb.
    inverts Hb as. introv Henv Hb.
    constructor. exists v.
    unfold env_compatible in Hc. specializes Hc va Henv. destr Hc.
    eapply s_unk. { exact H0. }
    specializes H1 Hb.
    exact H1.
  Qed.

  Local Notation derivable := forward.
  Local Notation valid := sem_tuple.

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
  Definition hist_triple fh e f :=
    forall penv env h0 h1 h2 v r,
      satisfies env h0 h1 r fh ->
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
    constructor. exists h3. exists r1.
    intuition.
    specializes H H4 H1.
  Qed.

  Lemma hist_sem : forall f e,
    sem_tuple e f <->
    hist_triple empty e f.
  Proof.
    iff H.
    { unfold hist_triple. intros.
      apply empty_inv in H0. destruct H0. subst h0.
      unfold sem_tuple, tuple_valid_under in H.
      specializes H H1 H2. }
    { unfold sem_tuple, tuple_valid_under. intros.
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
    pose proof (@s_seq env0 fh empty h0 h1 (norm vunit)) as Hseq.
    forward Hseq. { exists h1. exists r. intuition.
      apply (empty_intro env0 h1). }
    specializes H Hseq H1 H2.
  Qed.

  (** History triples which only append to history can be derived directly from the history-frame rule. *)
  Lemma hist_frame_sem: forall fh e f,
    sem_tuple e f ->
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
    constructor. exists h1. exists r.
    intuition.
    lets H: sem_pval n Hc.
    unfold tuple_valid_under, sem_tuple in H.
    apply H; auto.
  Qed.

  Remark hist_pval_via_frame: forall n fh,
    hist_triple fh (pval n) (fh;; ens (fun res => \[res = n])).
  Proof.
    intros.
    applys hist_frame_sem (@sem_pval n).
  Qed.

  Lemma hist_pref: forall v fh,
    hist_triple fh (pref v)
      (fh;; fex (fun y =>(ens (fun r => \[r = vloc y] \* y ~~> v)))).
  Proof.
    intros.
    applys hist_frame_sem (@sem_pref v).
  Qed.

  Lemma hist_pderef: forall x fh,
    hist_triple fh (pderef (vloc x))
      (fh;; fall (fun y =>
        req (x ~~> y) (ens (fun res => \[res = y] \* x ~~> y)))).
  Proof.
    intros.
    applys hist_frame_sem (@sem_pderef x).
  Qed.

  Lemma hist_passign: forall x y v fh,
    hist_triple fh (passign (vloc x) y)
      (fh;; req (x ~~> v) (ens_ (x ~~> y))).
  Proof.
    intros.
    applys hist_frame_sem (@sem_passign x).
  Qed.

  Lemma hist_passert: forall fh b,
    hist_triple fh (passert (vbool b)) (fh;; req_ \[b = true]).
  Proof.
    intros.
    applys hist_frame_sem (@sem_passert b).
  Qed.

  Lemma hist_pif: forall fh b e1 e2 f1 f2,
    hist_triple (fh;; ens_ \[b = true]) e1 f1 ->
    hist_triple (fh;; ens_ \[b = false]) e2 f2 ->
    hist_triple fh (pif (vbool b) e1 e2) (disj f1 f2).
  Proof.
    introv He1 He2.
    unfold hist_triple. intros.
    destruct b.
    { forwards: He1.
      { constructor.
        exists h1. exists r.
        split. exact H.
        pose proof (ens_void_pure_intro).
        apply ens_void_pure_intro.
        reflexivity. }
      { exact H0. }
      { inverts H1 as H1. exact H1. }
      apply s_disj_l. assumption. }

    { forwards: He2.
      { constructor.
        exists h1. exists r.
        split. exact H.
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
    { inj H2.
      unfold hist_triple in H0.
      specializes H0 H H1 H9. }
    { false. }
  Qed.

  Lemma hist_papp_fix: forall vf x e va f fn fh,
    vf = vfix fn x e ->
    hist_triple fh (subst x va (subst fn vf e)) f ->
    hist_triple fh (papp (pval vf) (pval va)) f.
  Proof.
    intros. subst.
    unfold hist_triple. intros.
    inverts H2 as H2.
    { false. }
    { inj H2.
      unfold hist_triple in H0.
      specializes H0 H H1 H9. }
  Qed.

  Lemma hist_papp_unk: forall f va fh,
    hist_triple fh (papp (pvar f) (pval va))
      (fh;; fex (fun r => unk f va r)).
  Proof.
    intros.
    applys hist_frame_sem fh (@sem_papp_unk f va).
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

    (* reason about the execution of e2 *)
    unfold hist_triple in He2.
    specializes He2 He1 Hc.
  Qed.

End HistoryTriples.

Module ForwardExamples.

  (* let x = 1 in x *)
  Definition e1_let := (plet "x" (pval (vint 1)) (pvar "x")).
  Definition f1 :=
    ens (fun v => \[v = vint 1]) ;;
    ens (fun r => \[r = vint 1]).

  Example ex1:
    forward e1_let f1.
  Proof.
    eapply fw_let.
    - apply fw_val.
    - unfold flow_res.
      intros.
      apply ens_pure_inv_dep in H.
      destruct H.
      exact H.
    - simpl.
      apply fw_val.
  Qed.

End ForwardExamples.

(** * Correspondence with the paper *)
(** ** Section 3.1. Semantics of staged formulae *)
(** The semantics of staged formulae is given as #<a href="&num;satisfies">satisfies</a>#. *)
(** There are a number of differences from the paper:
- An environment is added to give interpretations for unknown functions (a similar one is added to the #<a href="&num;bigstep">big-step semantics</a>#)
- Stores are removed to sidestep impredicativity problems, and replaced with substitution
- The definition of [req] is different, restoring its contravariance
*)
(** ** Section 3.2. Compaction *)
(** Compaction is really just #<a href="&num;entails">entailment</a>#, so soundness (Theorem 1) is ensured by construction. *)
(** The six rules in Fig 7:
- #<a href="&num;norm_ens_false_l">norm_ens_false_l</a>#
- #<a href="&num;norm_empty_l">norm_empty_l</a>#
- #<a href="&num;norm_empty_r">norm_empty_r</a>#
- #<a href="&num;norm_req_req">norm_req_req</a>#
- #<a href="&num;norm_ens_ens_void_l">norm_ens_ens_void_l</a>#
- #<a href="&num;norm_ens_req_transpose">norm_ens_req_transpose</a># *)
(** A definition of #<a href="&num;biabduction">biabduction</a># is given and proved sound with respect to heap entailment. *)
(** ** Section 4. Forward rules *)
(** The reasoning rules for programs are first presented as a more primitive relation #<a href="&num;forward">forward</a># between programs and staged formulae, without history. The validity of these rules for each program construct is defined as a collection of #<i>semantic tuples</i># #<a href="&num;sem_tuple">sem_tuple</a># (analogous to semantic triples), and soundness (Theorem 2) is #<a href="&num;soundness">explicitly proved</a>#, under a new #<a href="&num;env_compatible">env_compatible</a># condition. *)
(** #<a href="&num;hist_triple"><i>History triples</i></a># (Fig 8) are then defined. Many of the resulting rules can be derived from semantic tuples using the structural #<i>history-frame rule</i># #<a href="&num;hist_frame">hist_frame</a>#. History triples are also defined semantically and are hence sound by construction. *)
(** Other differences from the paper:
- The #<a href="&num;sem_passert">assert</a># rule takes a value (or expression, under ANF), not a heap formula. No expressiveness is lost as it's still possible to assert things about the content of heap locations by first reading them.
- The #<a href="&num;sem_papp_fun">fun</a>#/#<a href="&num;sem_papp_fun">fix</a># rules require function specifications to be given via triples, instead of via annotations in the syntax
- The #<a href="&num;sem_plet">let</a># rule substitutes (a symbolic value) into the program, instead of quantifying free variables
- The value of the location that #<a href="&num;sem_pderef">deref</a># retrieves is universally quantified, to match the new definition for [req] *)
(** ** Section 5. Entailment *)
(** #<a href="&num;entails">Entailment</a># is defined semantically, so soundness (Theorem 3) is ensured by construction. *)
(** The two entailment rules in the main paper
- #<a href="&num;entails_ens_seq">entails_ens_seq</a>#
- #<a href="&num;entails_req_seq">entails_req_seq</a># *)
(** and the additional rules from Appendix G
- #<a href="&num;entails_func">entails_func</a>#
- #<a href="&num;entails_disj_right_l">entails_disj_right_l</a>#
- #<a href="&num;entails_disj_right_r">entails_disj_right_r</a>#
- #<a href="&num;entails_disj_left">entails_disj_left</a># *)
(** are shown to be sound. The separation logic rules are the standard ones from SLF. *)
(** In practice, entailment proofs of interesting (higher-order/recursive) programs involve giving unknown functions specific interpretations using an environment. They will thus involve the #<a href="&num;entails_under">entails_under</a># sequent and use lemmas with the [ent_] prefix instead. *)
(** ** Appendix D. Intersection *)
(** This section is really about the completeness of biabduction. The main paper elides the case where two locations may not be known to be equal. A more complete definition is given as b_pts_diff/#<a href="&num;b_pts_diff_single">b_pts_diff_single</a>#, which works even without a known disquality between [x] and [y]. *)
(** Intersection (conjunction lifted to staged formulae) is an orthogonal concern. The example from the paper is proved correct using it in #<a href="&num;ex3_intersection">ex3_intersection</a>#. *)
