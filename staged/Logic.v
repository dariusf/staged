(** A reference formalization of #<a href="https://dl.acm.org/doi/10.1007/978-3-031-71162-6_26">Staged Specification Logic for Verifying Higher-Order Imperative Programs</a># (FM 2024). *)
From Coq Require Import Classes.RelationClasses.
From Coq Require Morphisms Program.Basics.

(* remove when https://github.com/coq/coq/pull/19673 is merged *)
Set Warnings "-notation-incompatible-prefix".
From Staged Require Export HeapF.
Set Warnings "notation-incompatible-prefix".
From Staged Require Export LibFmap.
From Staged Require Export ExtraTactics.

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
  | passert (b: expr)
  | pref (v: expr)
  | pderef (v: expr)
  | passign (x: expr) (v: expr)
  | pif (b: expr) (e1: expr) (e2: expr)
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
Module Export Heap := HeapF.HeapSetup Val.

Definition empty_heap : heap := Fmap.empty.

Definition precond := hprop.
Definition postcond := val -> hprop.

Inductive result : Type :=
  | norm : val -> result.

(** * Staged formulae *)
(** Deeply embedded due to uninterpreted functions, which cannot immediately be given a semantics without an environment. If we make [flow] a function of an [senv], the type of [flow] will be [flow : (var -> (val -> val -> flow)) -> ... -> Prop], which cannot be defined. *)
Inductive flow :=
  | req : precond -> flow -> flow
  | ens : postcond -> flow
  | seq : flow -> flow -> flow
  | fex : forall A, (A -> flow) -> flow
  | fall : forall A, (A -> flow) -> flow
  | unk : var -> val -> val -> flow
  | intersect : flow -> flow -> flow
  | disj : flow -> flow -> flow.

(** An [ens] which doesn't have a useful return value. This carries more information than [ens (fun _ => H)], which has an #<i>arbitrary</i># return value. *)
(** In practice, it is much easier to use this to talk about results which are universally quantified externally; the result of a staged formula is mainly useful only for defining its semantics and in triples. *)
(** Consequently, key lemmas like [norm_ens_req_transpose] are defined using this. This can to some extent be considered an implementation deficiency around the use of HOAS. *)
Definition ens_ H := ens (fun r => \[r = vunit] \* H).

Definition empty := ens_ \[True].

Notation req_ H := (req H empty).

(** Function environments, for interpreting unknown functions. [ufun] is a HOAS way of substituting into a staged formula, which otherwise doesn't support this due to the shallow embedding that [hprop] uses. *)
Definition ufun := val -> val -> flow.

#[global]
Instance Inhab_ufun : Inhab ufun.
Proof.
  constructor.
  exists (fun (r v:val) => ens_ \[r = v]).
  constructor.
Qed.

Definition senv := Fmap.fmap var ufun.

Definition empty_env : senv := Fmap.empty.

Declare Scope flow_scope.
Open Scope flow_scope.

Infix ";;" := seq (at level 38, right associativity) : flow_scope.

Notation "'∃' x1 .. xn , H" :=
  (fex (fun x1 => .. (fex (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '∃' '/ '  x1  ..  xn , '/ '  H ']'") : flow_scope.

Notation "'∀' x1 .. xn , H" :=
  (fall (fun x1 => .. (fall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '∀' '/ '  x1  ..  xn , '/ '  H ']'") : flow_scope.

Notation "f '$' '(' x ',' r ')'" := (unk f x r)
  (at level 80, format "f '$' '(' x ','  r ')'", only printing) : flow_scope.

(* Notation "'ens' '[' r ']' Q" := (ens (fun r => Q))
  (at level 80, format "'ens' '\[' r '\]' Q" , only printing) : flow_scope. *)
(* square brackets will conflict with format notation for boxes https://coq.inria.fr/doc/V8.20.0/refman/user-extensions/syntax-extensions.html#displaying-symbolic-notations:~:text=well%2Dbracketed%20pairs%20of%20tokens%20of%20the%20form%20%27%5B%20%27%20and%20%27%5D%27 *)

Notation "'ens' r '.' Q" := (ens (fun r => Q))
  (at level 80, format "'ens'  r '.'  Q" , only printing) : flow_scope.

(* Some tests *)

(* Check (fex (fun x => ens_ \[x = vint 1];; empty)).
Check (fex (fun x => ens_ \[x = vint 1]);; empty).
Check (req \[] (ens_ \[];; empty)).
Check (ens_ \[];; req \[] empty). *)

Implicit Types s : senv.
Implicit Types h : heap.
Implicit Types H : hprop.
Implicit Types Q : postcond.
Implicit Types uf fn : ufun.
Implicit Types c : val -> flow.
Implicit Types f : flow.
Implicit Types a v r : val.
Implicit Types R : result.
Implicit Types e : expr.
(* Implicit Types x y z : var. *)

(** * Interpretation of a staged formula *)
(** An [Inductive] definition is used because the rule for unknown functions is not structurally recursive. *)
Inductive satisfies : senv -> heap -> heap -> result -> flow -> Prop :=

  | s_req s p (h1 h2:heap) R f
    (H: forall (hp hr:heap), (* the heap satisfying p, and the remaining heap *)
      p hp ->
      h1 = Fmap.union hr hp ->
      Fmap.disjoint hr hp ->
      satisfies s hr h2 R f) :
    satisfies s h1 h2 R (req p f)

  | s_ens s q h1 h2 R
    (H: exists v h3,
      R = norm v /\
      q v h3 /\
      h2 = Fmap.union h1 h3 /\
      Fmap.disjoint h1 h3) :
    satisfies s h1 h2 R (ens q)

  | s_seq h3 R1 s f1 f2 h1 h2 R :
    satisfies s h1 h3 R1 f1 ->
    satisfies s h3 h2 R f2 ->
    satisfies s h1 h2 R (seq f1 f2)

  | s_fex s h1 h2 R (A:Type) (f:A->flow)
    (H: exists b,
      satisfies s h1 h2 R (f b)) :
    satisfies s h1 h2 R (@fex A f)

  | s_fall s h1 h2 R (A:Type) (f:A->flow)
    (H: forall b,
      satisfies s h1 h2 R (f b)) :
    satisfies s h1 h2 R (@fall A f)

  | s_unk s h1 h2 r xf fn a
    (He: Fmap.read s xf = fn)
    (Hr: satisfies s h1 h2 (norm r) (fn a r)) :
    satisfies s h1 h2 (norm r) (unk xf a r)

  | s_intersect s h1 h2 R f1 f2
    (H1: satisfies s h1 h2 R f1)
    (H2: satisfies s h1 h2 R f2) :
    satisfies s h1 h2 R (intersect f1 f2)

  | s_disj_l s h1 h2 R f1 f2
    (H: satisfies s h1 h2 R f1) :
    satisfies s h1 h2 R (disj f1 f2)

  | s_disj_r s h1 h2 R f1 f2
    (H: satisfies s h1 h2 R f2) :
    satisfies s h1 h2 R (disj f1 f2).

Notation "s ','  h1 ','  h2 ','  R  '|=' f" :=
  (satisfies s h1 h2 R f) (at level 30, only printing).

(** The result of a staged formula, written in the paper as [Φ[r]]. Because it relates a formula and a value here (and not a variable, as in the paper), we need a model for the formula to talk about the value. *)
Definition flow_res (f:flow) (v:val) : Prop :=
  forall h1 h2 env R, satisfies env h1 h2 R f -> R = norm v.

Definition flow_res_in_env (f:flow) (v:val) env : Prop :=
  forall h1 h2 v1, satisfies env h1 h2 (norm v1) f -> v1 = v.

Definition has_no_result f :=
  flow_res f vunit.

(** * Entailment *)
(** This sequent is useful for (interactive) proofs involving functions. *)
Definition entails_under env f1 f2 :=
  forall h1 h2 R,
    satisfies env h1 h2 R f1 -> satisfies env h1 h2 R f2.

(* see [ent_unk_conv] for why there is no bientails_under *)

(** General entailments which work for arbitrary environments. *)
Definition entails (f1 f2:flow) : Prop :=
  forall env h1 h2 R, satisfies env h1 h2 R f1 -> satisfies env h1 h2 R f2.

Definition bientails (f1 f2:flow) : Prop :=
  forall h1 h2 R env,
    satisfies env h1 h2 R f1 <-> satisfies env h1 h2 R f2.

Infix "⊑" := entails (at level 90, right associativity) : flow_scope.

Notation "env '⊢' f1 '⊑' f2" :=
  (entails_under env f1 f2) (at level 90, only printing) : flow_scope.

(** * Top and bottom *)
Definition top := req_ \[False].
Definition bot := ens_ \[False].
Definition error := req \[False] (ens_ \[False]).
Definition post_sat (Q:postcond) := exists v h, Q v h.
Definition flow_sat f := exists s h1 h2 R, satisfies s h1 h2 R f.
Definition okay P Q := ens_ \[post_sat Q];; req P (ens Q).

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
    applys* s_seq.
  Qed.

  #[global]
  Instance Proper_seq_entails_under : forall env,
    Proper (entails_under env ====> entails_under env ====> entails_under env) seq.
  Proof.
    unfold Proper, entails_under, respectful.
    intros.
    inverts H1 as H1; destr H1.
    applys* s_seq.
  Qed.

  #[global]
  Instance fex_entails_under_morphism (A : Type) : forall env,
    Proper (Morphisms.pointwise_relation A (entails_under env) ====> entails_under env) (@fex A).
  Proof.
    unfold Proper, respectful, Morphisms.pointwise_relation, entails_under.
    intros.
    inverts H0 as H0. destr H0.
    constructor.
    exists b.
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

  (* For rewriting in the goal. Some of the flipped instances are for this purpose.
     Without them, we can only rewrite in the Coq or the staged context. *)
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
      econstructor.
      apply* H.
      apply* H0. }
    { inverts H1 as H1; destr H1.
      econstructor.
      apply* H.
      apply* H0. }
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
Lemma flow_res_inv: forall v v1 f h1 h2 env,
  satisfies env h1 h2 (norm v) f ->
  flow_res f v1 ->
  v = v1.
Proof.
  unfold flow_res.
  intros.
  specializes H0 H.
  injects H0.
  reflexivity.
Qed.

Lemma ens_ret_inv : forall env h1 h2 H R,
  satisfies env h1 h2 R (ens_ H) ->
  R = norm vunit.
Proof.
  intros.
  inverts H0 as H0. destr H0.
  rewrite hstar_hpure_l in H0. destruct H0.
  congruence.
Qed.

Lemma ens_void_pure_inv : forall P env h1 h2 R,
  satisfies env h1 h2 R (ens_ \[P]) -> P /\ h1 = h2 /\ R = norm vunit.
Proof.
  intros.
  inverts H as H. destr H.
  rewrite hstar_hpure_l in H. destr H.
  apply hpure_inv in H4. destr H4. subst.
  intuition.
Qed.

Lemma empty_inv : forall env h1 h2 R,
  satisfies env h1 h2 R empty ->
  h1 = h2 /\ R = norm vunit.
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
Qed.

(* We get absolutely no info from top, so there is no top_inv.
  This is not the case for empty, which tells us that the heaps are empty. *)
Lemma top_intro : forall s h1 h2 R,
  satisfies s h1 h2 R top.
Proof.
  unfold bientails. intros.
  unfold top.
  apply s_req. intros.
  hinv H.
  false.
Qed.

(* Conversely, there is no bot_intro because we should never be able to prove it. *)
Lemma bot_inv : forall s h1 h2 R,
  satisfies s h1 h2 R bot -> False.
Proof.
  unfold bientails. intros.
  inverts H as H. destr H. hinv H. hinv H2.
  false.
Qed.

Lemma req_empty_inv : forall env h1 h2 R f,
  satisfies env h1 h2 R (req \[] f) ->
  satisfies env h1 h2 R f.
Proof.
  intros.
  inverts H as H. specializes H empty_heap h1 ___.
  apply hempty_intro.
Qed.

Lemma req_empty_intro : forall env h1 h2 R f,
  satisfies env h1 h2 R f ->
  satisfies env h1 h2 R (req \[] f).
Proof.
  intros.
  apply s_req. intros.
  hinv H0.
  subst. rew_fmap *.
Qed.

Lemma req_void_empty_inv : forall env h1 h2 R,
  satisfies env h1 h2 R (req_ \[]) ->
  h1 = h2 /\ R = norm vunit.
Proof.
  intros.
  inverts H as H. specializes H empty_heap h1 ___.
  apply hempty_intro.
  apply empty_inv in H.
  assumption.
Qed.

Lemma ens_empty_inv : forall env h1 h2 R,
  satisfies env h1 h2 R (ens (fun r => \[])) -> h1 = h2.
Proof.
  intros.
  inverts H as H. destr H.
  apply hempty_inv in H. subst.
  fmap_eq.
Qed.

Lemma ens_empty_intro : forall env h1 R,
  satisfies env h1 h1 R (ens (fun r => \[])).
Proof.
  intros.
  constructor.
  destruct R.
  exists v.
  exists empty_heap.
  intuition fmap_eq.
  constructor.
Qed.

Lemma ens_void_empty_intro : forall env h1,
  satisfies env h1 h1 (norm vunit) (ens_ \[]).
Proof.
  intros.
  constructor.
  exs.
  splits*.
  hintro.
  splits*.
  hintro.
  rew_fmap.
  reflexivity.
Qed.

Lemma ens_void_empty_inv : forall env h1 h2 R,
  satisfies env h1 h2 R (ens_ \[]) ->
  h1 = h2 /\ R = norm vunit.
Proof.
  intros.
  inverts H as H. destr H. hinv H. hinv H. hinv H2.
  subst. rew_fmap *.
Qed.

Lemma ens_pure_inv : forall P env h1 h2 v,
  satisfies env h1 h2 (norm v) (ens (fun a => \[P a])) ->
  P v /\ h1 = h2.
Proof.
  intros.
  inverts H as H. destr H.
  inverts H.
  inverts H2.
  injects H0.
  intuition.
Qed.

Lemma ens_pure_intro : forall P env h r,
  P r -> satisfies env h h (norm r) (ens (fun v => \[P v])).
Proof.
  intros.
  constructor.
  exists r.
  exists empty_heap.
  intuition.
  apply hpure_intro. assumption.
Qed.

Lemma ens_void_inv : forall env h1 h2 R H,
  satisfies env h1 h2 R (ens_ H) ->
  R = norm vunit.
Proof.
  unfold empty, ens_.
  intros.
  inverts H0 as H0. destr H0.
  rewrite hstar_hpure_l in H0.
  subst.
  intuition.
  f_equal. assumption.
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
Qed.

Lemma req_void_pure_intro : forall env h1 P,
  satisfies env h1 h1 (norm vunit) (req_ \[P]).
Proof.
  intros.
  constructor. intros.
  apply hpure_inv in H. destruct H. subst. rew_fmap.
  apply empty_intro.
Qed.

Lemma req_pure_intro : forall env h1 h2 R P f,
  (P -> satisfies env h1 h2 R f) ->
  satisfies env h1 h2 R (req \[P] f).
Proof.
  intros.
  apply s_req. intros.
  hinv H0. subst. rew_fmap.
  apply* H.
Qed.

Lemma req_void_pure_inv: forall env h1 h2 R P,
  P ->
  satisfies env h1 h2 R (req_ \[P]) ->
  h1 = h2 /\ R = norm vunit.
Proof.
  intros env h1 h2 r P HP H. 
  apply empty_inv with (env := env).
  inverts H as H. specialize (H empty_heap h1). apply* H.
  apply hpure_intro. assumption.
Qed.

Lemma req_pure_inv: forall env h1 h2 R P f,
  P ->
  satisfies env h1 h2 R (req \[P] f) ->
  satisfies env h1 h2 R f.
Proof.
  intros.
  inverts H0 as H0.
  specialize (H0 empty_heap h1). apply H0.
  hintro. assumption. fmap_eq. fmap_disjoint.
Qed.

Lemma ens_req_inv : forall env h1 h2 R H f,
  satisfies env h1 h2 R (ens_ H;; req H f) ->
  satisfies env h1 h2 R f.
Proof.
  intros.
  inverts H0 as H0.
  inverts H0 as H0. destr H0. hinv H0. hinv H0.
  inverts H7 as H7.
  specializes H7 H3.
  subst. rew_fmap *.
Qed.

Lemma req_ens_intro : forall env h1 h2 R H f,
  satisfies env h1 h2 R f ->
  satisfies env h1 h2 R (req H (ens_ H;; f)).
Proof.
  intros.
  apply s_req. intros.
  eapply s_seq.
  apply s_ens.
  exists vunit hp.
  splits*.
  hintro. splits*.
  subst. assumption.
Qed.

Lemma seq_ens_pure_inv : forall P env h1 h2 v f,
  satisfies env h1 h2 (norm v) (ens (fun a => \[P a]);; f) ->
  exists v1, P v1 /\ satisfies env h1 h2 (norm v) f.
Proof.
  intros.
  inverts H as H. destr H.
  destruct R1.
  lets H2: ens_pure_inv P H.
  exists v0.
  intuition.
  subst.
  intuition.
Qed.

Lemma seq_ens_void_pure_inv : forall P env h1 h2 R f,
  satisfies env h1 h2 R (ens_ \[P];; f) ->
  P /\ satisfies env h1 h2 R f.
Proof.
  intros.
  inverts H as H. destr H.
  apply ens_void_pure_inv in H. destr H. subst.
  intuition.
Qed.

Lemma ens_no_result : forall H,
  has_no_result (ens_ H).
Proof.
  unfold has_no_result, flow_res.
  intros.
  apply ens_void_inv in H0.
  congruence.
Qed.

Lemma unk_inv : forall s h1 h2 R xf a v fn,
  Fmap.read s xf = fn ->
  satisfies s h1 h2 R (unk xf a v) ->
  satisfies s h1 h2 R (fn a v).
Proof.
  intros.
  inverts H0 as H0.
  rewrite H in H0.
  assumption.
Qed.

Lemma unk_inv_bi : forall s h1 h2 r a fn xf,
  Fmap.read s xf = fn ->
  satisfies s h1 h2 (norm r) (unk xf a r) <->
  satisfies s h1 h2 (norm r) (fn a r).
Proof.
  intros.
  split; intros.
  { inverts H0 as H0.
    rewrite H in H0.
    assumption. }
  { pose proof s_unk.
    lets: s_unk s h1 h2 r xf.
    specializes H2 fn a H. }
Qed.

Lemma unk_res_inv : forall s h1 h2 r a fn xf R,
  Fmap.read s xf = fn ->
  satisfies s h1 h2 R (unk xf a r) ->
  R = norm r.
Proof.
  intros.
  inverts H0 as H0.
  reflexivity.
Qed.

(** * Some tactics *)

Ltac fdestr_rec H :=
  match type of H with
  | satisfies _ _ _ _ (fex (fun _ => _)) => inverts H as H; destr H
  | satisfies _ _ _ _ (_ ;; _) => inverts H as H; destr H
  | satisfies _ _ _ _ (ens_ \[_]) => apply ens_void_pure_inv in H; destr H
  end.

Ltac fdestr_pat H pat :=
  match type of H with
  | satisfies _ _ _ _ (fex (fun _ => _)) => inverts H as H; destruct H as pat
  | satisfies _ _ _ _ (_ ;; _) => inverts H as H; destruct H as pat
  | satisfies _ _ _ _ (ens_ \[_]) => apply ens_void_pure_inv in H; destruct H as pat
  end.

(** Use these on product-like things like sequencing, existentials, and ens *)
Tactic Notation "fdestr" constr(H) := fdestr_rec H.
Tactic Notation "fdestr" constr(H) "as" simple_intropattern(pat) := fdestr_pat H pat.

Ltac finv H :=
  match type of H with
  | satisfies _ _ _ _ (fex (fun _ => _)) => inverts H as H; destr H
  | satisfies _ _ _ _ (_ ;; _) => inverts H as H; destr H
  | satisfies _ _ _ _ (ens_ \[_]) => apply ens_void_pure_inv in H; destr H
  | satisfies _ _ _ _ (ens_ \[]) => apply ens_void_empty_inv in H; destr H; subst
  | satisfies _ _ _ _ (ens_ _) => inverts H as H; destr H
  | satisfies _ _ _ _ (req \[_] _) => inverts H as H
  | satisfies _ _ _ _ (req _ _) => inverts H as H
  | satisfies _ _ _ _ (intersect _ _) => inverts H as H
  | satisfies _ _ _ _ (disj _ _) => inverts H as H
  end.

Ltac fintro :=
  match goal with
  | |- satisfies _ _ _ _ (_ ;; _) => eapply s_seq
  | |- satisfies _ _ _ _ (ens_ \[_]) => apply ens_void_pure_intro
  | |- satisfies _ _ _ _ (ens_ \[]) => apply ens_void_empty_intro
  | |- satisfies _ _ _ _ (ens_ _) => apply s_ens; exists vunit
  | |- satisfies _ _ _ _ (ens_ _) => apply s_ens
  | |- satisfies _ _ _ _ (req \[_] _) => apply req_pure_intro
  | |- satisfies _ _ _ _ (req _ _) => apply s_req; intros
  end.

(** * Entailment and normalization rules *)
Lemma entails_bot: forall f,
  entails bot f.
Proof.
  unfold entails. intros.
  apply bot_inv in H.
  false.
Qed.

Lemma entails_top: forall f,
  entails f top.
Proof.
  unfold entails. intros.
  apply top_intro.
Qed.

Lemma disentails_okay_error: forall P Q,
  entails (okay P Q) error.
Proof.
  unfold entails. intros.
  unfold error.
  constructor. intros. hinv H0. false.
Qed.

Lemma disentails_error_okay: forall P Q,
  entails error (okay P Q).
Proof.
  unfold entails. intros.
  applys s_seq h1 (norm vunit).
  (* we need to prove Q, but error is useless for this *)
Abort.

(** Covariance of ens *)
Lemma entails_ens : forall Q1 Q2,
  (forall v, Q1 v ==> Q2 v) ->
  entails (ens Q1) (ens Q2).
Proof.
  unfold entails. intros.
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

Lemma satisfies_ens_void : forall H1 H2 env h1 h2 R,
  H1 ==> H2 ->
  satisfies env h1 h2 R (ens_ H1) ->
  satisfies env h1 h2 R (ens_ H2).
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
  apply (satisfies_ens_void H).
  assumption.
Qed.

(** Contravariance of req *)
Lemma entails_req : forall H1 H2 f1 f2,
  (H2 ==> H1) ->
  entails f1 f2 ->
  entails (req H1 f1) (req H2 f2).
Proof.
  unfold entails. intros.
  apply s_req. intros.
  apply H in H4.
  inverts H3 as H3.
  specializes H3 hr H4.
Qed.

(** Reassociating req *)
Lemma norm_reassoc : forall H f1 f2,
  entails (req H f1;; f2) (req H (f1;; f2)).
Proof.
  unfold entails.
  intros.
  inverts H0 as H0. destr H0.

  (* find out about req *)
  constructor. intros hp hr. intros.

  (* prove the req *)
  inverts H0 as H0.
  specializes H0 hp hr H1 ___.
  applys~ s_seq h3 R1.
Qed.

(** Properties of disjunction *)
Lemma disj_comm : forall f1 f2,
  bientails (disj f2 f1) (disj f1 f2).
Proof.
  unfold bientails. intros.
  iff H.
  { inverts H as H.
    apply s_disj_r. assumption.
    apply s_disj_l. assumption. }
  { inverts H as H.
    apply s_disj_r. assumption.
    apply s_disj_l. assumption. }
Qed.

Lemma disj_assoc : forall f1 f2 f3,
  bientails (disj f1 (disj f2 f3)) (disj (disj f1 f2) f3).
Proof.
  unfold bientails. intros.
  iff H.
  { inverts H as H.
    apply s_disj_l. apply* s_disj_l.
    inverts H as H.
    apply s_disj_l. apply* s_disj_r.
    apply* s_disj_r. }
  { inverts H as H.
    inverts H as H.
    apply* s_disj_l.
    apply s_disj_r. apply* s_disj_l.
    apply s_disj_r. apply* s_disj_r. }
Qed.

Lemma disj_idem : forall f,
  bientails (disj f f) f.
Proof.
  unfold bientails. intros.
  iff H.
  { inverts H as H; auto. }
  { apply* s_disj_l. }
Qed.

Lemma disj_unit : forall f,
  bientails (disj f bot) f.
Proof.
  unfold bientails. intros.
  iff H.
  { inverts H as H; auto. apply bot_inv in H. false. }
  { apply* s_disj_l. }
Qed.

Lemma disj_dom : forall f,
  bientails (disj f top) top.
Proof.
  unfold bientails. intros.
  iff H.
  { apply top_intro. }
  { apply* s_disj_r. }
Qed.

Lemma conj_comm : forall f1 f2,
  bientails (intersect f2 f1) (intersect f1 f2).
Proof.
  unfold bientails. intros. iff H.
  { inverts H as H.
    apply* s_intersect. }
  { inverts H as H.
    apply* s_intersect. }
Qed.

(** Properties of conjunction *)
Lemma conj_assoc : forall f1 f2 f3,
  bientails
    (intersect f1 (intersect f2 f3))
    (intersect (intersect f1 f2) f3).
Proof.
  unfold bientails. intros.
  iff H.
  { inverts H as H.
    inverts H6 as H6.
    apply* s_intersect.
    apply* s_intersect. }
  { inverts H as H.
    inverts H as H.
    apply* s_intersect.
    apply* s_intersect. }
Qed.

Lemma conj_idem : forall f,
  bientails (intersect f f) f.
Proof.
  unfold bientails. intros.
  iff H.
  { finv H. assumption. }
  { apply* s_intersect. }
Qed.

(* top is the unit or identity element of conjunction. *)
Lemma conj_unit : forall f,
  bientails (intersect f top) f.
Proof.
  unfold bientails. intros.
  iff H.
  { finv H. assumption. }
  { apply* s_intersect. apply top_intro. }
Qed.

(* This property is variously called domination or annihilation, with bot being called the annihilator. *)
Lemma conj_dom : forall f,
  bientails (intersect f bot) bot.
Proof.
  unfold bientails. intros.
  iff H.
  { finv H. assumption. }
  { apply* s_intersect. apply bot_inv in H. false. }
Qed.

(* Properties of sequencing *)
Lemma seq_disj_distr : forall f1 f2 f3,
  bientails ((disj f1 f2) ;; f3) (disj (f1;; f3) (f2;; f3)).
Proof.
  unfold bientails. intros.
  iff H.
  { finv H.
  finv H.
  - apply s_disj_l. econstructor; jauto.
  - apply s_disj_r. econstructor; jauto. }
  { finv H.
    - finv H.
      eapply s_seq.
      apply* s_disj_l. assumption.
    - finv H.
      eapply s_seq.
      apply* s_disj_r. assumption. }
Qed.

Lemma seq_assoc : forall env h1 h2 R f1 f2 f3,
  satisfies env h1 h2 R (f1;; f2;; f3) <->
  satisfies env h1 h2 R ((f1;; f2);; f3).
Proof.
  intros.
  split; intros H.
  { finv H. finv H6.
    econstructor; jauto.
    econstructor; jauto. }
  { finv H. finv H.
    econstructor; jauto.
    econstructor; jauto. }
Qed.

Lemma norm_seq_assoc : forall f1 f2 f3,
  bientails (f1;; f2;; f3) ((f1;; f2);; f3).
Proof.
  intros.
  split; intros; now apply seq_assoc.
Qed.

(** Compaction rule 1 from the paper *)
Lemma norm_ens_false_l : forall f,
  bientails (ens_ \[False]) (ens_ \[False];; f).
Proof.
  unfold bientails.
  iff H.
  { apply ens_void_pure_inv in H. destr H. false. }
  { finv H. apply ens_void_pure_inv in H. destr H.
    false. }
Qed.

Lemma norm_ens_false : forall f,
  entails (ens_ \[False]) f.
Proof.
  intros.
  apply entails_bot.
Qed.

Lemma norm_req_false : forall f f1,
  entails f (req \[False] f1).
Proof.
  unfold entails. intros.
  apply req_pure_intro.
  intros. false.
Qed.

Lemma norm_req_pure_l : forall P f,
  P -> bientails (req \[P] f) f.
Proof.
  unfold bientails. intros.
  iff H0.
  { apply req_pure_inv in H0.
    assumption.
    assumption. }
  { apply req_pure_intro. auto. }
Qed.

Lemma norm_ens_pure_r : forall P f,
  P -> bientails empty (ens_ \[P]).
Proof.
  unfold bientails. intros.
  iff H0.
  { apply empty_inv in H0. destr H0. subst.
    apply ens_void_pure_intro.
    assumption. }
  { apply ens_void_pure_inv in H0. destr H0. subst.
    apply empty_intro. }
Qed.

Lemma norm_ens_pure_seq_r : forall P f,
  P -> bientails f (ens_ \[P];; f).
Proof.
  unfold bientails. intros.
  iff H0.
  { eapply s_seq.
    apply ens_void_pure_intro.
    assumption.
    assumption. }
  { fdestr H0. fdestr H0. subst.
    assumption. }
Qed.

Lemma norm_req_ens_empty : forall P f,
  entails empty (req \[P] (ens_ \[P])).
Proof.
  unfold entails. intros.
  apply empty_inv in H. destr H. subst.
  apply req_pure_intro. intros.
  apply* ens_void_pure_intro.
Qed.

(** The converse is not true as the result would change *)
Lemma norm_seq_ens_empty : forall f,
  bientails (ens_ \[];; f) f.
Proof.
  unfold bientails. intros.
  iff H.
  { finv H.
    finv H.
    assumption. }
  { fintro.
    fintro.
    assumption. }
Qed.

(** Compaction rule 2 from the paper *)
Lemma norm_empty_l : forall f,
  bientails (empty;; f) f.
Proof.
  unfold bientails, empty.
  iff H.
  { finv H. finv H. subst.
    assumption. }
  { applys s_seq h1 (norm vunit).
    apply ens_void_pure_intro; constructor.
    assumption. }
Qed.

Lemma norm_ens_no_result_r : forall f,
  has_no_result f ->
  bientails (f;; empty) f.
Proof.
  iff H1.
  { finv H1.
    unfold has_no_result, flow_res in H.
    specializes H H1. subst.
    apply empty_inv in H7. destr H7. subst.
    assumption. }
  { specializes H H1. subst.
    applys s_seq h2 (norm vunit).
    assumption.
    apply empty_intro. }
Qed.

Lemma norm_ens_empty_r : forall H,
  bientails (ens_ H;; empty) (ens_ H).
Proof.
  intros.
  apply (@norm_ens_no_result_r (ens_ H)).
  apply ens_no_result.
Qed.

(** Compaction rule 3 from the paper. Stated this way to ensure [f] has no meaningful result. See [norm_ens_empty_r] for a better statement. *)
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
  bientails (req \[] f) f.
Proof.
  unfold entails. split; intros.
  { apply req_empty_inv in H. assumption. }
  { apply req_empty_intro. assumption. }
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
Lemma satisfies_ens_ens_void_split : forall H1 H2 env h1 h2 R,
  satisfies env h1 h2 R (ens_ (H1 \* H2)) ->
  satisfies env h1 h2 R (ens_ H1;; ens_ H2).
Proof.
  intros.
  inverts H as H. destruct H as (v&h3&H3&H4&H5&H6).
  rewrite hstar_hpure_l in H4. destruct H4 as (H4&H7).
  (* h3 is the heap that H1 and H2 together add *)
  (* find the intermediate heap *)
  apply hstar_inv in H7. destruct H7 as (h0&h4&H8&H9&H10&H11).
  (* H1 h0, H2 h4 *)
  applys s_seq (h1 \u h0) (norm vunit).
  { constructor. exists vunit. exists h0. intuition. rewrite hstar_hpure_l. intuition. }
  { constructor. exists v. exists h4. intuition. rewrite hstar_hpure_l. intuition. }
Qed.

Lemma satisfies_ens_ens_void_combine : forall H1 H2 env h1 h2 R,
  satisfies env h1 h2 R (ens_ H1;; ens_ H2) ->
  satisfies env h1 h2 R (ens_ (H1 \* H2)).
Proof.
  intros.
  inverts H as H. destr H.
  (* give up on careful reasoning *)
  inverts H as H. destr H.
  inverts H8 as H8. destr H8.
  hinv H. hinv H. hinv H6. hinv H6.
  constructor. exists v0. exists (h0 \u h4).
  splits*.
  rewrite <- hstar_assoc.
  subst. rew_fmap *.
  hintro; jauto.
  hintro; jauto.
Qed.

Lemma satisfies_ens_ens_void : forall H1 H2 env h1 h2 R,
  satisfies env h1 h2 R (ens_ H1;; ens_ H2) <->
  satisfies env h1 h2 R (ens_ (H1 \* H2)).
Proof.
  intros. split.
  - apply satisfies_ens_ens_void_combine.
  - apply satisfies_ens_ens_void_split.
Qed.

Lemma norm_ens_ens_void_split : forall H1 H2,
  entails (ens_ (H1 \* H2)) (ens_ H1;; ens_ H2).
Proof.
  unfold entails. apply satisfies_ens_ens_void_split.
Qed.

Lemma norm_ens_ens_void_combine : forall H1 H2,
  entails (ens_ H1;; ens_ H2) (ens_ (H1 \* H2)).
Proof.
  unfold entails; apply satisfies_ens_ens_void_combine.
Qed.

Lemma norm_ens_ens_void : forall H1 H2,
  bientails (ens_ (H1 \* H2)) (ens_ H1;; ens_ H2).
Proof.
  intros; split.
  - apply norm_ens_ens_void_split.
  - apply norm_ens_ens_void_combine.
Qed.

(** Compaction rule 5 from the paper *)
Lemma norm_ens_ens_void_l : forall H Q,
  bientails (ens_ H;; ens Q) (ens (Q \*+ H)).
Proof.
  unfold entails.
  split; intros.
  { inverts H0 as H0. destr H0.
    inverts H0 as H0. destr H0.
    inverts H7 as H7. destr H7.
    hinv H0. hinv H0.
    constructor. exists v0. exists (h0 \u h4).
    subst.
    splits*.
    rewrite hstar_comm.
    hintro; jauto.
    rew_fmap *. }
  { inverts H0 as H0. destr H0.
    hinv H0.
    applys s_seq (h1 \u x0) (norm vunit).
    { constructor. exists vunit. exists x0.
      splits*.
      hintro; jauto. }
    { constructor. exists v. exists x.
      jauto. } }
Qed.

(** Splitting and combining [ens] with results is more complex, and there does not seem to be a single equivalence. *)
Lemma satisfies_ens_sep_combine : forall Q1 Q2 env h1 h2 R,
  satisfies env h1 h2 R (ens Q1;; ens Q2) ->
  satisfies env h1 h2 R (ens (fun r0 : val => \exists r1 : val, Q1 r1 \* Q2 r0)).
Proof.
  intros.
  fdestr H.

  constructor. destruct R.
  exists v.
  inverts H as H. destr H.
  inverts H6 as H6. destr H6.
  exists (h0 \u h4).
  intuition.
  apply hexists_intro with (x := v0).

  apply hstar_intro; auto.
  subst. injects H2. assumption.
Qed.

Lemma norm_ens_ens_combine : forall Q1 Q2,
  entails (ens Q1;; ens Q2) (ens (fun r => \exists r1, Q1 r1 \* Q2 r)).
Proof.
  unfold entails.
  apply satisfies_ens_sep_combine.
Qed.

Lemma satisfies_ens_sep_split : forall H Q env h1 h2 R,
  satisfies env h1 h2 R (ens (Q \*+ H)) ->
  satisfies env h1 h2 R (ens (fun _ : val => H);; ens Q).
Proof.
  intros.
  inverts H0 as H0.
  destruct H0 as (v & h3 & H1 & H2 & H3 & H4).
  (* h3 is the part satisfying both *)
  apply hstar_inv in H2.
  destruct H2 as (h0 & h4 & ? & ? & ? & ?).
  (* h0 is the part satisfying Q, h4 H *)

  applys s_seq (h1 \u h4) (norm v). (* anything? *)
  econstructor; jauto.
  econstructor; jauto.
Qed.

Lemma norm_ens_split : forall H Q,
  entails (ens (Q \*+ H)) (ens (fun _ => H);; ens Q).
Proof.
  unfold entails.
  apply satisfies_ens_sep_split.
Qed.

Lemma norm_ens_ens_void_comm : forall H1 H2,
  bientails (ens_ H1;; ens_ H2) (ens_ H2;; ens_ H1).
Proof.
  unfold bientails. intros.
  iff H.
  { rewrite <- norm_ens_ens_void in H.
    rewrite <- norm_ens_ens_void.
    rewrite hstar_comm.
    assumption. }
  { rewrite <- norm_ens_ens_void in H.
    rewrite <- norm_ens_ens_void.
    rewrite hstar_comm.
    assumption. }
Qed.

Lemma norm_req_req_comm : forall H1 H2 f,
  bientails (req H1 (req H2 f)) (req H2 (req H1 f)).
Proof.
  unfold bientails. intros.
  iff H.
  { rewrite <- norm_req_req in H.
    rewrite <- norm_req_req.
    rewrite hstar_comm.
    assumption. }
  { rewrite <- norm_req_req in H.
    rewrite <- norm_req_req.
    rewrite hstar_comm.
    assumption. }
Qed.

Lemma norm_seq_forall_distr_r: forall (A:Type) (f:A->flow) f1,
  entails ((∀ x:A, f x);; f1) (∀ x:A, f x;; f1).
Proof.
  unfold entails. intros.
  inverts H as H. destr H.
  inverts H as H.
  constructor. intros v.
  specializes H v.
  applys* s_seq.
Qed.

Lemma norm_seq_forall_distr_l: forall (A:Type) (f:A->flow) f1,
  entails (f1;; (∀ x:A, f x)) (∀ x:A, f1;; f x).
Proof.
  unfold entails. intros.
  inverts H as H. destr H.
  inverts H6 as H6.
  constructor. intros v.
  specialize (H6 v).
  applys* s_seq.
Qed.

Lemma norm_seq_exists_distr_l: forall A (f:A->flow) f1,
  bientails (f1;; (∃ x : A, f x)) (∃ x : A, f1;; f x).
Proof.
  intros. split; intros.
  { inverts H as H. destr H.
    inverts H6 as H6. destr H6.
    constructor. exists b.
    applys~ s_seq h3 R1. }
  { inverts H as H. destr H.
    inverts H0 as H0. destr H0.
    applys~ s_seq h3 R1.
    constructor. now exists b. }
Qed.

Lemma norm_seq_exists_distr_r : forall A p f1,
  bientails (fex (fun (x:A) => p x);; f1) (fex (fun (x:A) => p x;; f1)).
Proof.
  intros. split; intros.
  { fdestr H. fdestr H.
    constructor. exists b.
    applys~ s_seq h3 R1. }
  { fdestr H. fdestr H0.
    applys~ s_seq h3 R1.
    constructor. exists b. assumption. }
Qed.

Lemma norm_ens_ens_pure_comm: forall H P,
  bientails (ens_ H;; ens_ \[P]) (ens_ \[P];; ens_ H).
Proof.
  intros.
  apply norm_ens_ens_void_comm.
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
  (* eapply s_seq. *)
  apply (satisfies_ens_void H) in H3.
  applys* s_seq h3 R1.
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
Lemma entails_func : forall xf a r,
  entails (unk xf a r) (unk xf a r).
Proof.
  intros.
  apply entails_refl.
Qed.

Lemma ens_match : forall s h1 h2 R H f1 f2,
  satisfies s h1 h2 R (ens_ H;; f1) ->
  (forall s h1 h2 R, satisfies s h1 h2 R f1 -> satisfies s h1 h2 R f2) ->
  satisfies s h1 h2 R (ens_ H;; f2).
Proof.
  intros.
  finv H0.
  fintro.
  eassumption.
  apply H1.
  assumption.
Qed.

Lemma norm_ens_req : forall H f,
  entails (ens_ H;; req H f) f.
Proof.
  unfold entails. intros.
  finv H0.
  finv H0. hinv H0. hinv H0.
  inverts H7 as H7.
  forwards: H7 x0 h1 H3.
  fmap_eq.
  fmap_disjoint.
  assumption.
Qed.

Lemma norm_req_assumption : forall H f1 f2,
  entails (ens_ H;; f2) f1 <->
  entails f2 (req H f1).
Proof.
  unfold entails. intros.
  iff H0; intros.
  { fintro.
    apply H0.
    fintro.
    apply s_ens.
    exists vunit hp. splits*. hintro. splits*.
    subst.
    assumption. }
  { finv H1.
    finv H1. hinv H1. hinv H1.
    apply H0 in H8.
    inverts H8 as H8.
    specializes H8 x0 (h1 \u x) H4.
    forwards: H8. fmap_eq. fmap_disjoint.
    subst. rew_fmap*. }
Qed.

Definition heap_inhab H := exists h, H h.

Definition precise H := forall h1 h2,
  H h1 -> H h2 -> h1 = h2.

(* Cancelling [ens; req] on the right requires a lot more assumptions *)
Lemma ens_req_cancel : forall f H,
  heap_inhab H ->
  precise H ->
  entails f (ens_ H;; req H f).
Proof.
  unfold entails. intros.
  unfold heap_inhab in H0. destr H0.
  assert (Fmap.disjoint h1 h) as ?. admit.
  fintro.
  fintro. exists h.
  splits*.
  hintro. splits*.
  fintro.
  specializes H1 H3 H4. subst.
  lets: union_eq_inv_of_disjoint H5.
  fmap_disjoint. fmap_disjoint. subst.
  assumption.
Abort.

(** * Biabduction *)
(** Simplified definition following #<a href="http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/popl09.pdf">Compositional Shape Analysis by means of Bi-Abduction</a># (Fig 1). *)
Inductive biab : hprop -> hprop -> hprop -> hprop -> Prop :=

  | b_trivial : forall H,
    biab \[] H H \[]

  | b_base_empty : forall Hf,
    biab \[] Hf \[] Hf

  | b_pts_match : forall a b H1 H2 Ha Hf x,
    biab Ha H1 H2 Hf ->
    biab (\[a=b] \* Ha) (x~~>a \* H1) (x~~>b \* H2) Hf

  | b_any_match : forall H H1 H2 Ha Hf,
    biab Ha H1 H2 Hf ->
    biab Ha (H \* H1) (H \* H2) Hf

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
  { xsimpl. }
  { xsimpl; auto. }
  { xsimpl. assumption. }
  { xsimpl. assumption. }
Qed.

(* Incomplete because [ens_req_cancel] can't be easily proved *)
Lemma biab_single_h_conv : forall H env h1 h2 R H1 H2 f,
  satisfies env h1 h2 R (ens_ H1;; req H2 f) ->
  satisfies env h1 h2 R (ens_ (H \* H1);; req (H \* H2) f).
Proof.
  intros.
  rewrite (hstar_comm H H1).
  rewrite norm_ens_ens_void.
  rewrite <- seq_assoc.
  apply (ens_match H0). intros.
  rewrite norm_req_req.
  (* apply ens_req_cancel. *)
  (* assumption. *)
  admit.
Abort.

Lemma biab_single_h : forall H env h1 h2 R H1 H2 f,
  satisfies env h1 h2 R (ens_ (H \* H1);; req (H \* H2) f) ->
  satisfies env h1 h2 R (ens_ H1;; req H2 f).
Proof.
  intros.
  inverts H0 as H0. destr H0.
  (* ens adds a location to the heap *)
  inverts H0 as H0.
  (* use that to figure out what is in h3 *)
  destr H0. hinv H0. hinv H0. hinv H5. subst h0 h3 x0 x. rew_fmap *.

  (* prove just the first part *)
  rewrite norm_req_req in H9.
  inverts H9 as H9. specializes H9 x1 (h1 \u x2) ___.

  applys s_seq (h1 \u x2) (norm vunit).
  { constructor. exists vunit. exists x2.
    splits*. hintro; jauto. }
  { assumption. }
Qed.

(** Biabduction for a single location. *)
Lemma biab_single : forall x a env h1 h2 R H1 H2 f,
  satisfies env h1 h2 R (ens_ (x~~>a \* H1);; req (x~~>a \* H2) f)->
  satisfies env h1 h2 R (ens_ H1;; req H2 f).
Proof.
  intros.
  applys* biab_single_h (x~~>a).
Qed.

(** We can remove a framing heap [hf] from both sides of a [satisfies] if it is disjoint from the part of the heap satisfying [ens_ H]. *)
Lemma ens_reduce_frame : forall env h1 h hf R H,
  H h ->
  Fmap.disjoint h (hf \u h1) ->
  satisfies env (hf \u h1) (hf \u h1 \u h) R (ens_ H) ->
  satisfies env h1 (h1 \u h) R (ens_ H).
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
Lemma norm_ens_req_transpose : forall H1 H2 Ha Hf f,
  biab Ha H1 H2 Hf ->
  entails (ens_ H1;; (req H2 f))
    (req Ha (ens_ Hf;; f)).
Proof.
  unfold entails.
  introv Hbi.
  induction Hbi.

  { (* trivial *)
    introv H2.
    apply ens_req_inv in H2.
    rewrite norm_seq_req_emp.
    rewrite norm_seq_ens_empty.
    assumption. }

  { (* base case *)
    introv H2.
    rewrite norm_seq_req_emp.
    rewrite norm_seq_req_emp in H2.
    assumption. }

  { (* b_pts_match *)
    intros.

    (* use the req *)
    rewrite norm_req_req.
    constructor. intros. hinv H0. subst. rew_fmap.

    apply (IHHbi env).
    apply (biab_single H). }

  { (* b_any_match *)
    intros.
    apply IHHbi.
    applys* biab_single_h H. }

  { (* b_pts_diff *)
    introv H3.
    (* the idea of this proof is to demonstrate that we can commute adding x~~>a and removing y~~>b by showing that we can start from a heap without x~~>a (using the lemma ens_reduce_frame), perform the operations, and arrive at the same result. reasoning semantically is quite nasty. maybe we can come up with a way to push y~~>b past H0? *)

    (* h4 -(+h7)-> h3 -(-hyb)-> h5+hxa+h7 -> h2
                  ||
                  h4+h7
                = (h5+hyb+hxa)+h7 *)

    (* extract x~~>a *)
    inverts H3 as H3. rename H8 into H4, R1 into r0.
    rewrite norm_ens_ens_void in H3.
    inverts H3 as H3. rename H9 into H5, h0 into h4.
    inverts H3 as H3. destr H3.
    hinv H0. hinv H0. rename x1 into hxa.

    (* extract y~~>b *)
    rewrite norm_req_req.
    constructor; intros hyb h5. intros.
    constructor; intros hHa h6. intros H14. intros.

    (* supply x~~>a *)
    rewrite norm_ens_ens_void.
    rewrite <- norm_seq_assoc.
    applys s_seq (h6 \u hxa) (norm vunit).
    { constructor. exists vunit. exists hxa.
      intuition. rewrite hstar_hpure_l. intuition. }

    (* need to subtract a heap from both sides of H5 *)
    (* that heap is y~~>2 *)

    (* find out about the heap we need *)
    pose proof H5 as HensH0. (* copy, as we're about to invert and destroy this *)
    inverts H5 as H5. destr H5.
    rewrite hstar_hpure_l in H5. rename H20 into H21. destruct H5 as (?&H20).

    (* reduce ens on the left *)
    pose proof (ens_reduce_frame) as Hreduce.
    specializes Hreduce env (h5 \u hxa) h7 hyb.
    specializes Hreduce r0 H20.
    forward Hreduce. fmap_disjoint.
    asserts_rewrite (h4 = hyb \u h5 \u hxa) in HensH0. fmap_eq.
    asserts_rewrite (h3 = hyb \u (h5 \u hxa) \u h7) in HensH0. fmap_eq.
    apply Hreduce in HensH0.
    clear Hreduce.

    (* provide the heap for y~~>b *)
    rewrite norm_req_req in H4.
    inverts H4 as H4.
    specializes H4 hyb (h5 \u hxa \u h7) H11 ___.

    lets Hseq: s_seq env (ens_ H1) (req H2 f) (h5 \u hxa) h2.
    forwards: Hseq R.
    applys HensH0.
    applys_eq H4. fmap_eq.
    (* got the seq... now we can use the IH *)
    clear Hseq.

    forwards H22: IHHbi env (h5 \u hxa) H19.
    inverts H22 as H26.
    applys H26 H14.
    fmap_eq.
    fmap_disjoint. }
Qed.

Module BiabductionExamples.

  (** [(a=3) * x->a*y->b |- x->3 * (y->b)] *)
  Example ex1_biab : forall x y,
    exists Ha Hf i, biab Ha (x~~>vint i \* y~~>vint 2) (x~~>vint 3) Hf.
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

      rewrite norm_seq_ens_empty in H.
      assumption. }
    { rewrite norm_ens_req_transpose in H; only 2: apply b_pts_diff_single.
      pose proof (norm_ens_empty_r (x~~>a)) .
      rewrite (norm_ens_empty_r (x~~>a)) in H.
      assumption. }
  Qed.

End BiabductionExamples.

(** * Lemmas about pure fact simplification *)
(** This section provides a few lemmas showing that once a pure predicate has
    been proven/ensured, it can be used again later down the specification. This
    can be useful when it comes to simplification of the spec. *)
Lemma req_generates_info: forall  P p f,
  let original_flow := req (p \* \[P]) f in
  let new_flow := req (p \* \[P]) (ens_ \[P] ;; f) in
  entails original_flow new_flow.
Proof.
  intros. unfold original_flow, new_flow, entails. clear original_flow new_flow.
  intros env h1 h2 r H.

  (* Remove prefix req p from both the goal and the hypothesis *)
  apply norm_req_req. apply s_req. intros hp hr H1 H2 H3.
  apply norm_req_req in H. inverts H as H. specialize (H hp hr). specialize(H H1 H2 H3).
  subst. clear H1 H3 p.

  (* Remove req \[P] from goal *)
  apply s_req. intros hp' hr' H1 H2 H3.

  assert (HP: hp' = empty_heap). (* and thus hr = hr' *)
  { inverts H1. inverts H0. reflexivity. }

  inverts H as H. specialize (H hp' hr' H1 H2 H3). subst. 
  
  eapply s_seq.
  apply ens_void_pure_intro. destruct H1. assumption.
  assumption.
Qed.

Lemma req_generates_info_bientails: forall  P p f,
  let original_flow := req (p \* \[P]) f in
  let new_flow := req (p \* \[P]) (ens_ \[P] ;; f) in
  bientails original_flow new_flow.
Proof.
  intros. unfold original_flow, new_flow, entails. clear original_flow new_flow.
  constructor.
  - apply req_generates_info.
  - intros H. 

    (* Remove req p \* \[P] *)
    apply s_req. intros hp hr H1 H2 H3.
    inverts H as H. specialize (H hp hr H1 H2 H3). 

    (* Just prove the ens_ f *)
    apply seq_ens_void_pure_inv in H. destruct H. assumption.
Qed.

Lemma ens_generates_info: forall P q f g, 
  let original_flow := ens_ (q \* \[P]) ;; f ;; g in 
  let new_flow      := ens_ (q \* \[P]) ;; f ;; req_ \[P] ;; g in 
  entails original_flow new_flow.
Proof.
  intros. unfold original_flow, new_flow, entails. clear original_flow new_flow.
  intros env h1 h2 r H.

  fdestr H. 
  eapply s_seq. eassumption.

  fdestr H6.
  eapply s_seq.
  eassumption.

  eapply s_seq.
  apply req_void_pure_intro.
  assumption.
Qed.

Lemma ens_generates_info_bientails: forall P q f g, 
  let original_flow := ens_ (q \* \[P]) ;; f ;; g in 
  let new_flow      := ens_ (q \* \[P]) ;; f ;; req_ \[P] ;; g in 
  bientails original_flow new_flow.
Proof.
  intros. unfold original_flow, new_flow, entails. clear original_flow new_flow.
  constructor.
  - apply ens_generates_info.
  - intro H. 
    
    (* Remove the ens_ q *)
    fdestr H.
    eapply s_seq. eassumption.

    (* Extract proof of P. *)
    rewrite hstar_comm in H. 
    apply norm_ens_ens_void in H. fdestr H. fdestr H.

    (* Proving env, h3, h2, r |= (f;; g) *)
    fdestr H6.
    eapply s_seq.
    eassumption.

    fdestr H10.
    eapply req_void_pure_inv in H10. destr H10.
    subst.
    assumption.
    assumption.
Qed.

(** In ens_generates_info, the final flow g is not within the context of 
    req_ \[P] (i.e. req \[P] g). This is inconsequential as we can bring g in
    and out of the context of the req.
    
    This is important for the normalized form of a specification. *)
Lemma move_seq_into_req: forall P f,
  entails (req_ P ;; f) (req P f).
Proof.
  intros. 
  assert (bientails (req P f) (req P (empty ;; f))) as H.
  { rewrite  (norm_empty_l f). reflexivity. }
  rewrite H.
  apply norm_reassoc with (H := P) (f1 := empty) (f2 := f).
Qed.

(** The converse is true if P is pure and P holds. *)
Lemma move_seq_out_of_req_pure: forall P f,
  P -> entails (req \[P] f) (req_ \[P] ;; f).
Proof.
  intros P f HP. unfold entails. intros env h1 h2 r H.

  eapply s_seq.
  - apply req_void_pure_intro.
  - apply (req_pure_inv HP) in H. assumption.
Qed.

Lemma norm_disj_ens_distr: forall P1 P2 f,
  bientails (ens_ \[P1 \/ P2]) (disj (ens_ \[P1]) (ens_ \[P2])).
Proof.
  unfold bientails. intros.
  iff H.
  { fdestr H. subst.
    destruct H0.
    { apply s_disj_l.
      apply* ens_void_pure_intro. }
    { apply s_disj_r.
      apply* ens_void_pure_intro. } }
  { inverts H as H.
    { fdestr H. subst.
      apply* ens_void_pure_intro. }
    { fdestr H. subst.
      apply* ens_void_pure_intro. } }
  Qed.

Lemma norm_disj_req_distr: forall P1 P2 f,
  entails
    (disj (req \[P1] f) (req \[P2] f))
    (req \[P1 /\ P2] f).
Proof.
  unfold entails. intros.
  apply req_pure_intro. intros [? ?].
  inverts H as H.
  - apply (req_pure_inv H0) in H. assumption.
  - apply (req_pure_inv H1) in H. assumption.
Qed.

Lemma norm_req_disj_distr: forall P1 P2 f,
  entails
    (req \[P1 \/ P2] f)
    (disj (req \[P1] f) (req \[P2] f)).
Proof.
  unfold entails. intros.
  apply s_disj_l.
  apply req_pure_intro. intros.
  apply req_pure_inv in H.
  - assumption.
  - left. assumption.
Qed.

(** * Lemmas about entailment sequents *)
Lemma entails_ent : forall f1 f2 env,
  entails f1 f2 ->
  entails_under env f1 f2.
Proof.
  unfold entails, entails_under. intros.
  apply H.
  assumption.
Qed.

Lemma ent_entails : forall f1 f2,
  (forall env, entails_under env f1 f2) ->
  entails f1 f2.
Proof.
  unfold entails, entails_under. intros.
  apply H.
  assumption.
Qed.

Lemma ent_entails_1 : forall f1 f2 f3 f4,
  (forall env, entails_under env f1 f2 -> entails_under env f3 f4) ->
  entails f1 f2 -> entails f3 f4.
Proof.
  intros.
  apply ent_entails.
  intros.
  apply H.
  apply entails_ent.
  apply H0.
Qed.

Lemma ent_all_r : forall f A (fctx:A -> flow) env,
  (forall x, entails_under env f (fctx x)) ->
  entails_under env f (fall (fun x => fctx x)).
Proof.
  unfold entails_under. intros.
  constructor. intros x.
  auto.
Qed.

Lemma ent_all_l : forall f A (fctx:A -> flow) env,
  (exists x, entails_under env (fctx x) f) ->
  entails_under env (fall (fun x => fctx x)) f.
Proof.
  unfold entails_under. intros.
  destr H.
  apply H1.
  inverts H0 as H0. specializes H0 x.
  assumption.
Qed.

Lemma ent_seq_all_l : forall f f1 A (fctx:A -> flow) env,
  (exists x, entails_under env (fctx x;; f1) f) ->
  entails_under env (fall (fun x => fctx x);; f1) f.
Proof.
  unfold entails_under. intros.
  destr H.
  apply H1.
  inverts H0 as H0.
  inverts H0 as H0. specializes H0 x.
  applys* s_seq.
Qed.

Lemma ent_req_r0 : forall f f1 H env,
  entails_under env (ens_ H;; f) f1 ->
  entails_under env f (req H f1).
Proof.
  unfold entails_under. intros.
  apply s_req. intros.
  apply H0.
  applys s_seq (hr \+ hp) (norm vunit).
  { constructor. exists vunit. exists hp.
    intuition.
    rewrite hstar_hpure_l. intuition. }
  { rewrite <- H3. assumption. }
Qed.

Lemma ent_req_r : forall f f1 H env,
  entails_under env (ens_ H;; f) f1 <->
  entails_under env f (req H f1).
Proof.
  unfold entails_under. intros.
  split.
  { apply ent_req_r0. }
  { intros.
    finv H1.
    specializes H0 H8.
    finv H1. hinv H1. hinv H1.
    subst. rew_fmap *.
    finv H0.
    specializes H0 H4. forwards: H0. reflexivity. fmap_disjoint.
    assumption. }
Qed.

Lemma ent_req_r1 : forall f f1 H,
  entails (ens_ H;; f) f1 ->
  entails f (req H f1).
Proof.
  intros ? ? ?.
  applys ent_entails_1 ent_req_r0.
Qed.

Lemma ent_req_req : forall f1 f2 H1 H2 env,
  H2 ==> H1 ->
  entails_under env f1 f2 ->
  entails_under env (req H1 f1) (req H2 f2).
Proof.
  unfold entails_under. intros.
  constructor. intros.
  inverts H3 as H3. specializes H3 H6; auto.
Qed.

Lemma ent_req_l : forall f f1 P env,
  P ->
  entails_under env f1 f ->
  entails_under env (req \[P] f1) f.
Proof.
  unfold entails_under. intros.
  inverts H1 as H1.
  apply H0.
  specializes H1 empty_heap h1.
  apply H1.
  hintro.
  assumption.
  fmap_eq.
  fmap_disjoint.
Qed.

Lemma ent_ens_l : forall env f P,
  (P -> entails_under env empty f) ->
  entails_under env (ens_ \[P]) f.
Proof.
  unfold entails_under. intros.
  fdestr H0. subst.
  apply H.
  assumption.
  apply empty_intro.
Qed.

Lemma ent_ens_r : forall env f P,
  P -> entails_under env f empty ->
  entails_under env f (ens_ \[P]).
Proof.
  unfold entails_under. intros.
  specializes H0 H1.
  apply empty_inv in H0. destr H0. subst.
  apply ens_void_pure_intro.
  assumption.
Qed.

Lemma ent_seq_ens_l : forall env f f1 P,
  (P -> entails_under env f1 f) ->
  entails_under env (ens_ \[P];; f1) f.
Proof.
  unfold entails_under. intros.
  fdestr H0.
  fdestr H0.
  apply H.
  assumption.
  subst.
  auto.
Qed.

Lemma ent_seq_ens_r : forall env f f1 P,
  P -> entails_under env f f1 ->
  entails_under env f (ens_ \[P];; f1).
Proof.
  unfold entails_under. intros.
  applys s_seq h1 (norm vunit).
  apply ens_void_pure_intro. assumption.
  apply H0. assumption.
Qed.

Lemma ent_ens_single_pure : forall env P P1,
  (P1 -> P) ->
  entails_under env (ens_ \[P1]) (ens_ \[P]).
Proof.
  unfold entails_under. intros.
  fdestr H0.
  constructor. exists vunit. exists empty_heap.
  apply H in H1.
  intuition.
  hintro.
  intuition.
  hintro.
  assumption.
Qed.

Lemma ent_ens_single : forall env H H1,
  (H1 ==> H) ->
  entails_under env (ens_ H1) (ens_ H).
Proof.
  unfold entails_under. intros.
  inverts H2 as H2. destr H2.
  rewrite hstar_hpure_l in H2. destruct H2.
  apply H0 in H5.
  constructor. exists v. exists h3.
  intuition.
  rewrite hstar_hpure_l. intuition.
Qed.

Lemma ent_unk_single : forall env xf x r,
  entails_under env (unk xf x r) (unk xf x r).
Proof.
  intros. apply entails_under_refl.
Qed.

Lemma ent_unk : forall s xf x v fn,
  Fmap.read s xf = fn ->
  entails_under s (unk xf x v) (fn x v).
Proof.
  unfold entails_under.
  intros.
  eapply unk_inv.
  exact H.
  assumption.
Qed.

Lemma ent_unk_conv : forall s v fn xf x,
  Fmap.read s xf = fn ->
  entails_under s (fn x v) (unk xf x v).
Proof.
  unfold entails_under. intros.
  (* the converse is not possible to prove because reduction of a ufun
    returns an arbitrary flow, which isn't guaranteed to have the same
    result as [unk xf]. the other direction is fine because of the semantics
    of unk.

    note that this is an implementation issue due to the use of hoas for ufuns;
    conceptually this is an equivalence.

    at the level of [satisfies], however, it is possible to go
    backwards if we constrain the result; see [unk_inv_bi]. this is also
    the reason we don't have bientails_under, as this is the only rule
    which uses it, and it would have to talk about the result. *)
Abort.

Lemma ent_seq_unk : forall xf fn f1 f2 s x r,
  Fmap.read s xf = fn ->
  entails_under s (fn x r;; f1) f2 ->
  entails_under s (unk xf x r;; f1) f2.
Proof.
  intros.
  rewrites (>> ent_unk s); [ apply H | ].
  assumption.
Qed.

Lemma ent_unk_ex : forall s xf x A (vv:A->val) fn,
  Fmap.read s xf = fn ->
  entails_under s
    (fex (fun (v:A) => unk xf x (vv v)))
    (fex (fun (v:A) => fn x (vv v))).
Proof.
  unfold entails_under. intros.
  inverts H0 as H0. destr H0.
  constructor. exists b.
  lets H0: unk_inv s h1 h2 R.
  specializes H0 xf x (vv b) fn.
Qed.

Lemma ent_ex_seq_unk : forall s xf x A (vv:A->val) fn ctx,
  Fmap.read s xf = fn ->
  entails_under s
    (fex (fun (b:A) => unk xf x (vv b);; ctx b))
    (fex (fun (b:A) => fn x (vv b);; ctx b)).
Proof.
  unfold entails_under. intros.
  inverts H0 as H0. destr H0.
  inverts H1 as H1. destr H1.
  constructor. exists b.
  applys s_seq h3 R1.
  lets H2: unk_inv s h1 h3 R1.
  specializes H2 xf x (vv b) fn.
  assumption.
Qed.

Lemma ent_disj_l : forall f1 f2 f3 env,
  entails_under env f1 f3 ->
  entails_under env f2 f3 ->
  entails_under env (disj f1 f2) f3.
Proof.
  unfold entails_under. intros.
  inverts H1 as H1; auto.
Qed.

Lemma ent_disj_r_l : forall f1 f2 f3 env,
  entails_under env f3 f1 ->
  entails_under env f3 (disj f1 f2).
Proof.
  unfold entails_under. intros.
  apply s_disj_l.
  auto.
Qed.

Lemma ent_disj_r_r : forall f1 f2 f3 env,
  entails_under env f3 f2 ->
  entails_under env f3 (disj f1 f2).
Proof.
  unfold entails_under. intros.
  apply s_disj_r.
  auto.
Qed.

Lemma ent_seq_disj_l : forall f1 f2 f3 f4 env,
  entails_under env (f1;; f3) f4 ->
  entails_under env (f2;; f3) f4 ->
  entails_under env (disj f1 f2;; f3) f4.
Proof.
  unfold entails_under. intros.
  fdestr H1.
  inverts H1 as H1.
  { apply H. applys* s_seq. }
  { apply H0. applys* s_seq. }
Qed.

Lemma ent_seq_ex_l : forall A (f1: A -> flow) f2 f3 env,
  (forall x, entails_under env (f1 x;; f2) f3) ->
  entails_under env (fex (fun x => f1 x);; f2) f3.
Proof.
  unfold entails_under. intros.
  fdestr H0.
  fdestr H0.
  applys H b.
  applys* s_seq.
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
  constructor. exists b.
  auto.
Qed.

Lemma ent_seq_ens_sl_ex: forall env A (c:A->hprop) f,
  entails_under env (ens_ (\exists x, c x);; f)
  (∃ x, ens_ (c x);; f).
Proof.
  unfold entails_under. intros.
  fdestr H.
  inverts H as H. destr H.
  rewrite hstar_hpure_l in H. destr H.
  apply hexists_inv in H4.
  destr H4. (* get x *)
  constructor. exists x.
  applys s_seq h3 (norm vunit).
  - constructor. exists vunit. exists h0.
    splits*.
    rewrite* hstar_hpure_l.
  - assumption.
Qed.

Lemma ent_req_emp_l : forall env f f1,
  entails_under env f f1 ->
  entails_under env (req \[] f) f1.
Proof.
  unfold entails_under. intros.
  inverts H0 as H0. specializes H0 empty_heap h1 ___.
  apply hempty_intro.
Qed.

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
Implicit Types penv : penv.

Inductive bigstep : penv -> heap -> expr -> heap -> eresult -> Prop :=
  | eval_pval : forall h v env,
    bigstep env h (pval v) h (enorm v)

  (* there is no var rule *)

  | eval_plet : forall h1 h3 h2 x e1 e2 v Re env,
    bigstep env h1 e1 h3 (enorm v) ->
    bigstep env h3 (subst x v e2) h2 Re ->
    bigstep env h1 (plet x e1 e2) h2 Re

  | eval_padd : forall h x y env,
    bigstep env h (padd (pval (vint x)) (pval (vint y))) h (enorm (vint (x + y)))

  | eval_pminus : forall h x y env,
    bigstep env h (pminus (pval (vint x)) (pval (vint y))) h (enorm (vint (x - y)))

  | eval_pfun : forall h x e env,
    bigstep env h (pfun x e) h (enorm (vfun x e))

  | eval_pfix : forall h x e xf env,
    bigstep env h (pfix xf x e) h (enorm (vfix xf x e))

  | eval_app_fun : forall v1 v2 h x e Re env,
    v1 = vfun x e ->
    bigstep env h (subst x v2 e) h Re ->
    bigstep env h (papp (pval v1) (pval v2)) h Re

  | eval_app_fix : forall v1 v2 h x e Re xf env,
    v1 = vfix xf x e ->
    bigstep env h (subst x v2 (subst xf v1 e)) h Re ->
    bigstep env h (papp (pval v1) (pval v2)) h Re

  | eval_app_unk : forall va h Re efn xf env,
    Fmap.read env xf = efn ->
    bigstep env h (efn va) h Re ->
    bigstep env h (papp (pvar xf) (pval va)) h Re

  | eval_pif_true : forall h1 h2 Re e1 e2 env,
    bigstep env h1 e1 h2 Re ->
    bigstep env h1 (pif (pval (vbool true)) e1 e2) h2 Re

  | eval_pif_false : forall h1 h2 Re e1 e2 env,
    bigstep env h1 e2 h2 Re ->
    bigstep env h1 (pif (pval (vbool false)) e1 e2) h2 Re

  | eval_pref : forall h v p env,
    ~ Fmap.indom h p ->
    bigstep env h (pref (pval v)) (Fmap.update h p v) (enorm (vloc p))

  | eval_pderef : forall h p env,
    Fmap.indom h p ->
    bigstep env h (pderef (pval (vloc p))) h (enorm (Fmap.read h p))

  | eval_passign : forall h p v env,
    Fmap.indom h p ->
    bigstep env h (passign (pval (vloc p)) (pval v)) (Fmap.update h p v) (enorm vunit)

  | eval_passert : forall h env,
    bigstep env h (passert (pval (vbool true))) h (enorm vunit).

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
    forward (pif (pval (vbool b)) e1 e2)
      (disj
        (ens_ \[b = true];; f1)
        (ens_ \[b = false];; f2))

  | fw_deref: forall x,
    forward (pderef (pval (vloc x)))
      (fall (fun y => (req (x~~>y)
        (ens (fun res => \[res = y] \* x~~>y)))))

  | fw_ref: forall v,
    forward (pref (pval v)) (fex (fun y =>
      (ens (fun r => \[r = vloc y] \* y~~>v))))

  | fw_assign: forall x y v,
    forward (passign (pval (vloc x)) (pval y))
      (req (x~~>v) (ens_ (x~~>y)))

  | fw_assert: forall b,
    forward (passert (pval (vbool b))) (req_ \[b = true])

  | fw_app_fun: forall vf x e va f,
    vf = vfun x e ->
    forward (subst x va e) f ->
    forward (papp (pval vf) (pval va)) f

  | fw_app_fix: forall vf x e va f xf,
    vf = vfix xf x e ->
    forward (subst x va (subst xf vf e)) f ->
    forward (papp (pval vf) (pval va)) f

  | fw_app_unk: forall xf va,
    forward (papp (pvar xf) (pval va)) (fex (fun r => unk xf va r)).


Module Soundness.

  (** * Specification assertions *)
  (** A #<i>specification assertion</i># is our equivalent of a (semantic) Hoare triple: a valid one ensures ensures that the given program satisfies the given specification. *)
  Definition pair_valid_under penv env e f : Prop :=
    forall h1 h2 v,
      bigstep penv h1 e h2 (enorm v) -> satisfies env h1 h2 (norm v) f.

  (** Roughly, this says that for every binding in the program environment, we can find a "corresponding" one in the spec environment, where "corresponding" means related by a valid specification assertion. *)
  Definition env_compatible penv env :=
    forall pfn xf x,
      Fmap.read penv xf = pfn ->
      exists sfn, Fmap.read env xf = sfn /\
      forall v, pair_valid_under penv env (pfn x) (sfn x v).

  (** The full definition requires compatible environments. *)
  Definition spec_assert (e: expr) (f: flow) : Prop :=
    forall penv env,
      env_compatible penv env -> pair_valid_under penv env e f.

  #[global]
  Instance Proper_spec_assert : Proper
    (eq ====> entails ====> impl)
    spec_assert.
  Proof.
    unfold entails, Proper, respectful, impl, spec_assert, pair_valid_under.
    intros. subst.
    eauto.
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
    unfold spec_assert. introv Hc Hb.
    (* appeal to how e executes to tell us about the heaps *)
    inverts Hb as Hb.
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
    unfold spec_assert, pair_valid_under. introv Hc Hb.

    (* reason about how the let executes *)
    inverts Hb as. introv He1 He2.

    (* use the specification assertion we have about e1 *)
    unfold spec_assert in H.
    lets H3: H env He1. exact Hc. clear H He1. sort.

    (* we need to know that spec value and program value are the same *)
    specializes H0 H3. subst.
    injects H0.

    (* know about f2 *)
    specializes H1 env h3 h2 v0 He2. clear He2.

    applys* s_seq h3 (norm v).
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
    - unfold flow_res. intros.
      destruct R.
      apply ens_pure_inv in H.
      destruct H.
      subst. reflexivity.
    - simpl.
      apply fw_val.
  Qed.

End ForwardExamples.

(** * Correspondence with the paper *)
(** ** Section 2.1. A Simple Example *)
(** In the file #<a href="staged.Hello.html">Hello.v</a>#. An additional example, which demonstrates preventing the use of a function argument which captures one of the input pointers, is included. *)
(** ** Section 2.2. [foldr] *)
(** In the file #<a href="staged.Foldr.html">Foldr.v</a>#. Entailments [foldr_sum] and [foldr_sum_state] are both proved, as are those of the three examples which are difficult to handle with the conventional [foldr] specification from the introduction. *)
(** The first one does require a separate heap-manipulating definition of [foldr]; the others can be adapted to use it as well, at the cost of clarity and brevity of proofs. *)
(** The proof of the third one cannot be finished without a semantics for exceptions, which we do not cover in this paper. *)
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
(** The reasoning rules for programs are first presented as a more primitive relation #<a href="&num;forward">forward</a># between programs and staged formulae, without history. The validity of these rules for each program construct is defined as a collection of #<i>specification assertions</i># #<a href="&num;spec_assert">spec_assert</a># (analogous to semantic triples), and soundness (Theorem 2) is #<a href="&num;soundness">explicitly proved</a>#, under a new #<a href="&num;env_compatible">env_compatible</a># condition. *)
(** #<a href="&num;hist_triple"><i>History triples</i></a># (Fig 8) are then defined. Many of the resulting rules can be derived from specification assertions using the structural #<i>history-frame rule</i># #<a href="&num;hist_frame">hist_frame</a>#. History triples are also defined semantically and are hence sound by construction. *)
(** Other differences from the paper:
- The #<a href="&num;sem_passert">assert</a># rule takes a value (or expression, under ANF), not a heap formula. No expressiveness is lost as it's still possible to assert things about the content of heap locations by first reading them.
- The #<a href="&num;sem_papp_fun">fun</a>#/#<a href="&num;sem_papp_fun">fix</a># rules require function specifications to be given via triples, instead of via annotations in the syntax. An annotation can still be given by proving a lemma giving the function body a specification beforehand.
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
(** In practice, entailment proofs of interesting (higher-order/recursive) programs involve giving unknown functions specific interpretations using an environment. They thus involve the #<a href="&num;entails_under">entails_under</a># sequent and use lemmas with the [ent_] prefix instead. Manipulating such sequents neccessitates a significant number of new lemmas. *)
(** ** Appendix D. Intersection *)
(** This section is really about the completeness of biabduction. The main paper elides the case where two locations may not be known to be equal. A more complete definition is given as b_pts_diff/#<a href="&num;b_pts_diff_single">b_pts_diff_single</a>#, which works even without a known disquality between [x] and [y]. *)
(** Intersection (conjunction lifted to staged formulae) is an orthogonal concern. The example from the paper is proved correct using it in #<a href="&num;ex3_intersection">ex3_intersection</a>#. *)
