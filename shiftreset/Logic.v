From Coq Require Import Classes.RelationClasses.
From Coq Require Morphisms Program.Basics.

From Staged Require Export HeapF.
From Staged Require Export LibFmap.
From Staged Require Export ExtraTactics.

Local Open Scope string_scope.
(* Local Open Scope nat_scope. *)
Local Open Scope Z_scope.
Local Open Scope list_scope.

Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
(* Ltac auto_star ::= try solve [ auto | fmap_eq | eauto | intuition eauto ]. *)

(** * Programs *)
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
  | vfptr : var -> val
(** A deeply-embedded function pointer, referring to a [ufun] in the environment. *)

with expr : Type :=
  | pvar (x: var)
  | pval (v: val)
  | plet (x: var) (e1 e2: expr)
  | pfix (xf: var) (x: var) (e: expr)
  | pfun (x: var) (e: expr)
  | padd (e1 e2: expr)
  | pfst (e: expr)
  | psnd (e: expr)
  | pminus (e1 e2: expr)
  | passert (v: val)
  | pref (v: val)
  | pderef (v: val)
  | passign (e1: val) (e2: val)
  | pif (v: val) (e1: expr) (e2: expr)
  | papp (e1: expr) (e2: expr)
  | pshift (k: var) (e: expr)
  | preset (e: expr).

#[global]
Instance Inhab_val : Inhab val.
Proof.
  constructor.
  exists vunit.
  constructor.
Qed.

Fixpoint subst (y:var) (v:val) (e:expr) : expr :=
  let aux t := subst y v t in
  let if_y_eq x t1 t2 := if var_eq x y then t1 else t2 in
  match e with
  | pval v => pval v
  | padd x z => padd x z
  | pminus x z => pminus x z
  | pfst x => pfst x
  | psnd x => psnd x
  | pvar x => if_y_eq x (pval v) e
  | passert b => passert b
  | pderef r => pderef r
  | passign x z => passign x z
  | pref v => pref v
  | pfun x t1 => pfun x (if_y_eq x t1 (aux t1))
  | pfix f x t1 => pfix f x (if_y_eq f t1 (if_y_eq x t1 (aux t1)))
  | papp e v => papp e v
  | plet x t1 t2 => plet x (aux t1) (if_y_eq x t2 (aux t2))
  | pif t0 t1 t2 => pif t0 (aux t1) (aux t2)
  | pshift k e1 => pshift k (aux e1)
  | preset e => preset (aux e)
  end.

Module Val.
  Definition value := val.
End Val.

Module Export Heap := HeapF.HeapSetup Val.

Definition empty_heap : heap := Fmap.empty.

Definition postcond := val -> hprop.

(** * Staged formulae *)
Inductive flow : Type :=
  | req : hprop -> flow -> flow
  | ens : postcond -> flow
  | seq : flow -> flow -> flow
  | fex : forall (A:Type), (A -> flow) -> flow
  | fall : forall (A:Type), (A -> flow) -> flow
  | unk : var -> val -> val -> flow
  | intersect : flow -> flow -> flow
  | disj : flow -> flow -> flow
(** The following are new: *)
  | sh : var -> flow -> val -> flow
(** [sh k fb vr] is a shift with body [fb] and #<i>result</i># [vr]. *)
(** [k] names the continuation delimited by an enclosing [rs], and may occur in [fb] as an [unk] or [vfptr]. *)
(** [vr] is the #<i>result</i># of the shift, which is the value a shift appears to evaluate to when a continuation is taken. [vr] will be equal to the value that the continuation will be resumed with, and can be depended on in anything sequenced after a [sh]. *)
  | shc : var -> flow -> val -> (val -> flow) -> flow
(** [shc k fb vr fc] is a [sh] in CPS form, or the syntactic counterpart of [shft]. It carries a continuation whose argument is the equivalent of [sh]'s [r]. This continuation has a mixed first-/higher-order representation and has a [rs] as its topmost form. *)
(** Example: the continuation [(λ vr. < fc >)] is represented as a tuple [(vr, fun r => rs fc r)]. *)
  | rs : flow -> val -> flow
(** [rs f vr] is a reset with body [f] and return value [vr]. *)
  | defun : var -> (val -> val -> flow) -> flow
(** [defun x uf] is equivalent to [ens_ (x=(λ x r. uf x r))], where [x] can reside in the environment (which regular [ens_] cannot access).
  Should defun be scoped? We don't think so, because the resulting continuation is first-class and does not have a well-defined lifetime. *)
  | discard : flow -> var -> flow.

Definition ens_ H := ens (fun r => \[r = vunit] \* H).

Definition empty := ens_ \[True].

Notation req_ H := (req H empty).

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

(* shft's continuation could have a more general [A -> flow] type, but it can't be used in the semantics as long as it has to pass through ufun *)
Inductive result : Type :=
  | norm : val -> result
  | shft : var -> flow -> val -> (val -> flow) -> result.
  (** See [shc] for what the arguments mean. *)

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

(* Notation "'⟨' f '→' r '⟩'" := (rs f r) *)
  (* (at level 40, format "'⟨' f  '→'  r '⟩'", only printing) : flow_scope. *)

(* Check (rs (∃ x, empty) vunit;; empty). *)
(* Check (∃ x, rs empty vunit;; empty). *)

Notation "'sh' '(' k '.' fb '),' vr" := (sh k fb vr)
  (at level 80, format "'sh'  '(' k '.'  fb '),'  vr", only printing) : flow_scope.

Notation "'shc' '(' k '.' fb ')' '(' vr '.' '⟨' fk '⟩' ')'" := (shc k fb vr (fun r => rs fk r))
  (at level 80, format "'shc'  '(' k '.'  fb ')'  '(' vr '.'  '⟨' fk '⟩' ')'", only printing) : flow_scope.

Notation "'ens' r '.' Q" := (ens (fun r => Q))
  (at level 80, format "'ens'  r '.'  Q" , only printing) : flow_scope.

Implicit Types s : senv.
Implicit Types h : heap.
Implicit Types H : hprop.
Implicit Types Q : postcond.
Implicit Types uf fn : ufun.
(* Implicit Types c : val -> flow. *)
Implicit Types f : flow.
Implicit Types x y z k : var.
Implicit Types a v r : val.
Implicit Types R : result.
Implicit Types e : expr.

(** * Interpretation of a staged formula *)
Inductive satisfies : senv -> senv -> heap -> heap -> result -> flow -> Prop :=

  | s_req (s1 s2:senv) p (h1 h2:heap) R f
    (H: forall (hp hr:heap),
      p hp ->
      h1 = Fmap.union hr hp ->
      Fmap.disjoint hr hp ->
      satisfies s1 s2 hr h2 R f) :
    satisfies s1 s2 h1 h2 R (req p f)

  | s_ens s1 q h1 h2 R
    (H: exists v h3,
      R = norm v /\
      q v h3 /\
      h2 = Fmap.union h1 h3 /\
      Fmap.disjoint h1 h3) :
    satisfies s1 s1 h1 h2 R (ens q)

  | s_seq s3 h3 r1 s1 s2 f1 f2 h1 h2 R :
    satisfies s1 s3 h1 h3 (norm r1) f1 ->
    satisfies s3 s2 h3 h2 R f2 ->
    satisfies s1 s2 h1 h2 R (seq f1 f2)
  (** seq is changed to require a value from the first flow *)

  | s_fex s1 s2 h1 h2 R (A:Type) (f:A->flow)
    (H: exists b,
      satisfies s1 s2 h1 h2 R (f b)) :
    satisfies s1 s2 h1 h2 R (@fex A f)

  | s_fall s1 s2 h1 h2 R (A:Type) (f:A->flow)
    (H: forall b,
      satisfies s1 s2 h1 h2 R (f b)) :
    satisfies s1 s2 h1 h2 R (@fall A f)

  | s_unk s1 s2 h1 h2 r xf uf a
    (He: Fmap.read s1 xf = uf)
    (Hr: satisfies s1 s2 h1 h2 (norm r) (uf a r)) :
    satisfies s1 s2 h1 h2 (norm r) (unk xf a r)

  | s_intersect s1 s2 h1 h2 R f1 f2
    (H1: satisfies s1 s2 h1 h2 R f1)
    (H2: satisfies s1 s2 h1 h2 R f2) :
    satisfies s1 s2 h1 h2 R (intersect f1 f2)

  | s_disj_l s1 s2 h1 h2 R f1 f2
    (H: satisfies s1 s2 h1 h2 R f1) :
    satisfies s1 s2 h1 h2 R (disj f1 f2)

  | s_disj_r s1 s2 h1 h2 R f1 f2
    (H: satisfies s1 s2 h1 h2 R f2) :
    satisfies s1 s2 h1 h2 R (disj f1 f2)

    (** The new rules for shift/reset are as follows. *)

  | s_sh s1 h1 x shb (v:val) :
    satisfies s1 s1 h1 h1
      (shft x shb v (fun r1 => rs (ens (fun r => \[r = v])) r1))
      (sh x shb v)
    (** A [sh] on its own reduces to a [shft] containing an identity continuation. *)

  | s_shc s1 h1 x shb fk v :
    satisfies s1 s1 h1 h1
      (shft x shb v (fun r2 => rs fk r2))
      (shc x shb v (fun r2 => rs fk r2))
    (** [shc] corresponds directly to [shft]. *)

  | s_seq_sh s1 s2 f1 f2 fk h1 h2 shb k (v:val) :
    satisfies s1 s2 h1 h2 (shft k shb v (fun r1 => rs fk r1)) f1 ->
    satisfies s1 s2 h1 h2 (shft k shb v (fun r1 => rs (fk;; f2) r1)) (f1;; f2)
    (** This rule extends the continuation in a [shft] on the left side of a [seq]. Notably, it moves whatever comes next #<i>under the reset</i>#, preserving shift-freedom by constructon. *)

  | s_rs_sh s1 s2 f h1 h2 r rf s3 h3 fb fk k v1
    (H: satisfies s1 s3 h1 h3 (shft k fb v1 (fun r2 => rs fk r2)) f)
    (H1: satisfies (* TODO k is fresh/not already in s3? *)
        (Fmap.update s3 k (fun a r =>
          rs (ens_ \[v1 = a];; fk) r)) s2
      h3 h2 rf (rs fb r)) :
    satisfies s1 s2 h1 h2 rf (rs f r)

    (** This rule applies when the body of a [rs] #<i>evaluates to</i># a [shft] (not when a [sh] is directly inside a [rs]; that happens in reduction). The continuation carried by the [shft] is known, so it is bound in (the environment of) the [sh]ift body before that is run. *)
    (** The two resets in the semantics are accounted for: one is around the shift body, and one is already the topmost form in the continuation. *)
    (** Note: because staged formulae are turned into values (via [shft] and being added to the [senv]), rewriting can no longer be done to weaken them. Environment entailment was an attempt at solving this problem; the Proper instances might have to be tweaked to allow rewriting too. Another possible solution is a syntactic entailment relation in the relevant rules to allow weakening. *)

  | s_rs_val s1 s2 h1 h2 v f
    (H: satisfies s1 s2 h1 h2 (norm v) f) :
    satisfies s1 s2 h1 h2 (norm v) (rs f v)

  | s_defun s1 s2 h1 x uf :
    (* ~ Fmap.indom s1 x -> *)
    s2 = Fmap.update s1 x uf ->
    satisfies s1 s2 h1 h1 (norm vunit) (defun x uf)

  | s_discard s1 s2 h x R f :
    satisfies s1 s2 h h R f ->
    s2 = Fmap.remove s1 x ->
    satisfies s1 s2 h h R (discard f x).

Notation "s1 ',' s2 ','  h1 ','  h2 ','  r  '|=' f" :=
  (satisfies s1 s2 h1 h2 r f) (at level 30, only printing).

(** A specialization of [equal_f] for exposing the equalities in continuations after inversion. *)
Lemma cont_inj : forall fk1 fk2,
  (fun r1 => rs fk1 r1) = (fun r2 => rs fk2 r2) ->
  fk1 = fk2.
Proof.
  intros.
  apply equal_f with (x := arbitrary) in H.
  injects H.
  reflexivity.
Qed.

Ltac cont_eq :=
  lazymatch goal with
  | H: (fun _ => rs _ _) = (fun _ => rs _ _) |- _ =>
    lets ?: cont_inj H; subst; clear H; cont_eq
  | _ => idtac
  end.

(** * Entailment *)
Definition entails_under s1 f1 f2 :=
  forall h1 h2 s2 R,
    satisfies s1 s2 h1 h2 R f1 -> satisfies s1 s2 h1 h2 R f2.

Definition entails (f1 f2:flow) : Prop :=
  forall s1 s2 h1 h2 R,
    satisfies s1 s2 h1 h2 R f1 -> satisfies s1 s2 h1 h2 R f2.

Definition bientails (f1 f2:flow) : Prop :=
  forall h1 h2 R s1 s2,
    satisfies s1 s2 h1 h2 R f1 <-> satisfies s1 s2 h1 h2 R f2.

Infix "⊑" := entails (at level 90, right associativity) : flow_scope.

Notation "env '⊢' f1 '⊑' f2" :=
  (entails_under env f1 f2) (at level 90, only printing) : flow_scope.

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
  auto.
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
Section Propriety.

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
  Instance Proper_entails_under_flip : forall env, Proper
    (entails_under env ====> flip (entails_under env) ====> flip impl)
    (entails_under env).
  Proof.
    unfold entails_under, Proper, respectful, impl, flip.
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
    (eq ====> eq ====> eq ====> eq ====> eq ====> entails ====> impl)
    satisfies.
  Proof.
    unfold entails, Proper, respectful, impl.
    intros. subst.
    auto.
  Qed.

  #[global]
  Instance Proper_satisfies_bi : Proper
    (eq ====> eq ====> eq ====> eq ====> eq ====> bientails ====> impl)
    satisfies.
  Proof.
    unfold bientails, entails, Proper, respectful, impl.
    intros. subst.
    apply H4.
    auto.
  Qed.

  #[global]
  Instance Proper_satisfies_under : forall env, Proper
    (eq ====> eq ====> eq ====> eq ====> entails_under env ====> impl)
    (satisfies env).
  Proof.
    unfold entails_under, Proper, respectful, impl.
    intros. subst.
    auto.
  Qed.

  (* A weaker Proper instance that only allows rewriting in the left
     side of a seq. Intuitively, we can no longer rely on the right side
     being weaker because it may change entirely, if we rewrite to a
     [shft] on the left which then consumes the right side into its
     continuation. *)
  #[global]
  Instance Proper_seq_left : Proper (entails ====> eq ====> entails) seq.
  Proof.
    unfold Proper, entails, respectful.
    intros.
    subst.
    inverts H1 as H1; destr H1.
    { applys* s_seq. }
    { apply s_seq_sh.
      apply H. assumption. }
  Qed.

  #[global]
  Instance Proper_seq : Proper (entails ====> entails ====> entails) seq.
  Proof.
    unfold Proper, entails, respectful.
    intros.
    inverts H1 as H1; destr H1.
    { eapply s_seq; eauto. }
    { apply H in H1.
      pose proof s_seq_sh.
      specializes H2 H1.
      applys_eq H2. clear H2.
      f_equal.
      (* the proof is stuck here because y0 and x0 are related by
         something weaker than equality, but the rule in the semantics
         requires them to be equal *)
      admit.
      (* TODO what if we can assume shift-freedom to get rid of this case? *)
    }
  Abort.

  #[global]
  Instance Proper_seq_entails_under_left : forall env,
    Proper (entails_under env ====> eq ====> entails_under env) seq.
  Proof.
    unfold Proper, entails_under, respectful.
    intros.
    subst.
    inverts H1 as H1; destr H1.
    { applys* s_seq. }
    { eapply s_seq_sh. jauto. }
  Qed.

  #[global]
  Instance Proper_rs : Proper (entails ====> eq ====> entails) rs.
  Proof.
    unfold Proper, entails, respectful.
    intros. subst.
    inverts H1 as H1; destr H1.
    { eapply s_rs_sh.
      apply H. exact H1.
      apply H8. }
    { apply s_rs_val. eauto. }
  Qed.

  #[global]
  Instance Proper_bientails_rs : Proper
    (bientails ====> eq ====> bientails)
    rs.
  Proof.
    unfold bientails, Proper, respectful, impl.
    split; subst; intros.
    { inverts H0 as H0.
      { eapply s_rs_sh. apply H. exact H0. exact H8. }
      { apply H in H0. apply s_rs_val. assumption. } }
    { inverts H0 as H0.
      { eapply s_rs_sh. apply H. exact H0. exact H8. }
      { apply H in H0. apply s_rs_val. assumption. } }
  Qed.

  #[global]
  Instance Proper_rs_under : forall s,
    Proper (entails_under s ====> eq ====> entails_under s) rs.
  Proof.
    unfold Proper, entails_under, respectful.
    intros. subst.
    inverts H1 as H1; destr H1.
    { eapply s_rs_sh.
      apply H. exact H1.
      apply H8. }
    { apply s_rs_val. eauto. }
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
  Instance Proper_seq_bi_left : Proper (bientails ====> eq ====> bientails) seq.
  Proof.
    unfold Proper, bientails, respectful.
    intros.
    split; intros.

    { pose proof Proper_seq_left.
      unfold Proper, entails, respectful in H2.
      applys H2 H1; auto.
      intros.
      apply~ H. }

    { pose proof Proper_seq_left.
      unfold Proper, entails, respectful in H2.
      applys H2 H1; auto.
      intros.
      apply~ H. }
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

End Propriety.

(** * Environment entailment *)
Module EnvEntailment.
(** A weakening of [agree], allowing only entailment between [senv] values.
  Not currently used, just for posterity. *)
Definition env_entails (s1 s2:senv) : Prop :=
forall k,
  forall uf1 uf2,
    Fmap.indom s1 k -> Fmap.indom s2 k ->
    Fmap.read s1 k = uf1 ->
    Fmap.read s2 k = uf2 ->
    forall a v,
    entails (uf1 a v) (uf2 a v).

Lemma entails_ens_void : forall H1 H2,
  H1 ==> H2 ->
  entails (ens_ H1) (ens_ H2).
Proof.
  unfold entails.
  intros.
  inverts H0 as H3. destruct H3 as (v&h3&?&?&?&?).
  constructor. exists v. exists h3.
  intuition.
  rewrite hstar_hpure_l in H3.
  rewrite hstar_hpure_l.
  intuition.
Qed.

Example e1: env_entails
  (Fmap.single "x" (fun a r => ens_ \[r = vint 0]))
  (Fmap.single "x" (fun a r => ens_ \[r = vint 0 \/ r = vint 1])).
Proof.
  unfold env_entails.
  intros.

  rewrite Fmap.indom_single_eq in H.
  rewrite Fmap.indom_single_eq in H0.
  subst.

  rewrite Fmap.read_single.
  rewrite Fmap.read_single.

  apply entails_ens_void.
  xsimpl.
  intuition.
Qed.

Definition entails1 (f1 f2:flow) : Prop :=
  forall s1 s1' s2 s2' h1 h2 R,
    env_entails s1 s1' ->
    env_entails s2 s2' ->
  satisfies s1 s2 h1 h2 R f1 -> satisfies s1' s2' h1 h2 R f2.

Instance env_entails_refl : Reflexive env_entails.
Proof.
  unfold Reflexive, env_entails, entails. intros.
  subst.
  assumption.
Qed.

(** Like [agree], environment entailment is not transitive, which severely limits the utility of [entails1]. *)
Instance env_entails_trans : Transitive env_entails.
Proof.
  unfold Transitive, env_entails. intros.
  specializes H k uf1.
  specializes H0 k.
  apply H0.
  admit.
Abort.

End EnvEntailment.

(** * Lemmas about satisfies *)
Lemma empty_intro : forall s1 h1,
  satisfies s1 s1 h1 h1 (norm vunit) empty.
Proof.
  intros.
  unfold empty, ens_.
  constructor.
  exists vunit.
  exists empty_heap.
  splits*.
  { rewrite hstar_hpure_l.
    intuition.
    apply hpure_intro.
    constructor. }
Qed.

Lemma ens_void_pure_intro : forall P s h,
  P -> satisfies s s h h (norm vunit) (ens_ \[P]).
Proof.
  intros.
  unfold ens_.
  constructor.
  exists vunit.
  exists empty_heap.
  splits*.
  { rewrite hstar_hpure_r.
    intuition.
    apply hpure_intro.
    reflexivity. }
Qed.

Lemma ens_pure_intro : forall P s h r,
  P r -> satisfies s s h h (norm r) (ens (fun v => \[P v])).
Proof.
  intros.
  constructor.
  exists r.
  exists empty_heap.
  hint hpure_intro.
  splits*.
Qed.

Lemma ens_void_pure_inv : forall P s1 s2 h1 h2 R,
  satisfies s1 s2 h1 h2 R (ens_ \[P]) ->
  P /\ h1 = h2 /\ s1 = s2 /\ R = norm vunit.
Proof.
  intros.
  inverts H as H. destr H.
  rewrite hstar_hpure_l in H. destr H.
  apply hpure_inv in H4. destr H4. subst.
  intuition.
Qed.

Lemma ens_store_frame : forall s1 s2 h1 h2 R x uf Q,
  satisfies s1 s2 h1 h2 R (ens Q) ->
  satisfies (Fmap.update s1 x uf) (Fmap.update s2 x uf) h1 h2 R (ens Q).
Proof.
  intros.
  inverts H as H. destr H.
  subst.
  apply s_ens. exs.
  intuition eauto.
Qed.

(** * Examples for semantics *)
Module Examples.

Example e1_undelimited : forall x, exists R,
  satisfies empty_env empty_env empty_heap empty_heap R
    (sh x (ens (fun r2 => \[r2 = vint 1])) (vint 1)).
Proof.
  intros.
  eexists.
  apply s_sh.
  (* result of continuation can be anything because it's never used *)
Qed.

Example e2_reset_value :
  satisfies empty_env empty_env empty_heap empty_heap (norm (vint 1))
    (rs (ens (fun r => \[r = vint 1])) (vint 1)).
Proof.
  intros.
  apply s_rs_val.
  apply ens_pure_intro.
  reflexivity.
Qed.

Example e3_rs_sh_no_k : forall x, exists s,
  satisfies empty_env s empty_heap empty_heap (norm (vint 1))
    (rs (sh x (ens (fun r => \[r = vint 1])) (vint 2)) (vint 1)).
Proof.
  intros.
  eexists.
  (* the ret of the shift can be anything because the cont is never taken *)
  eapply s_rs_sh.
  { constructor. }
  { apply s_rs_val.
    (* produced by eapply, never instantiated because continuation is never taken *)
    apply ens_pure_intro.
    reflexivity. }
Qed.

Definition vplus (a b:val) : val :=
  match a, b with
  | vint a, vint b => vint (a + b)
  | _, _ => vunit
  end.

(** [reset (1 + shift k (k 2))]. *)
Example e4_rs_sh_k : forall k, exists s,
satisfies empty_env s empty_heap empty_heap (norm (vint 3))
  (rs (sh k (unk k (vint 2) (vint 3)) (vint 2);; ens (fun r => \[r = vint (1 + 2)]))
      (vint 3)).
Proof.
intros.
eexists. (* this is okay because it's an output *)
eapply s_rs_sh.
(* put the ens into the cont *)
{
  (* show that the body produces a shift *)
  apply s_seq_sh.
  apply s_sh. }
{ apply s_rs_val. (* handle reset *)

  eapply s_unk. resolve_fn_in_env. (* reset body *)
  simpl.

  apply s_rs_val.

  eapply s_seq.

  { apply ens_void_pure_intro. jauto. }

  { eapply s_seq.
    apply ens_pure_intro. intuition reflexivity.
    apply ens_pure_intro. reflexivity. }
}
Qed.

(** [(reset (shift k (fun a -> k a))) 4 ==> 4]
- The whole thing returns what the application of f/k returns
- The result of the shift is 4 due to the identity k
- The result of the reset is a function; 4 is the result of an inner reset that appears in the course of reduction *)
Example e5_shift_k : forall k xf, k <> xf -> exists s,
  satisfies empty_env s empty_heap empty_heap (norm (vint 4))
    (rs (sh k (defun xf (fun a r => unk k a r);;
                ens (fun r => \[r = vfptr xf]))
            (vint 4))
        (vfptr xf);;
      unk xf (vint 4) (vint 4)).
Proof.
  intros.
  eexists.
  eapply s_seq.
  { (* show that reset produces a function *)
    eapply s_rs_sh.
    (* handle the shift *)
    apply s_sh.
    (* show how the shift body goes through the reset to produce the function *)
    { apply s_rs_val.
      eapply s_seq.
      apply s_defun. reflexivity.
      apply ens_pure_intro. reflexivity. }
  }
  { (* show that applying the function returns 4 *)
    eapply s_unk. resolve_fn_in_env.
    simpl.
    (* applying the function amounts to applying the continuation *)
    eapply s_unk.
    (* TODO resolve_fn_in_env should solve this *)
    { unfold Fmap.update.
      rewrite Fmap.read_union_r.
      rewrite Fmap.read_union_l.
      apply Fmap.read_single.
      apply Fmap.indom_single.
      apply fmap_not_indom_of_neq.
      easy. }
    simpl.
    
    apply s_rs_val.
    eapply s_seq.
    apply~ ens_void_pure_intro.
    apply~ ens_pure_intro.
  }
Qed.

(** [(reset 1 + (shift k (fun a -> k a))) 4 ==> 5]
- res of shift = arg of k = 4
- res of reset = res of shift body = fptr
- final res is that of the inner reset, which doesn't occur syntacically in the code as it is produced by the "handling" of the shift. *)
Example e6_shift_k : forall k xf, k <> xf -> exists s,
  satisfies empty_env s empty_heap empty_heap (norm (vint 5))
    (rs (∃ sr, sh k (defun xf (fun a r => unk k a r);;
                ens (fun r => \[r = vfptr xf]))
            sr;; ens (fun r => \[r = vplus (vint 1) sr]))
        (vfptr xf);;
      ∃ fr, unk xf (vint 4) (vint fr)).
Proof.
  intros.
  eexists.
  eapply s_seq.
  { (* reset *)
    (* the shift is still "handled", but produces a lambda without
      applying the continuation *)
    eapply s_rs_sh.
    {
      apply s_fex. eexists.
      (* eta-expand the right side to make it clear what the continuation is *)
      change (ens (fun r => \[r = vplus (vint 1) ?sr])) with
        ((fun a => ens (fun r => \[r = vplus (vint 1) a])) sr).
      apply s_seq_sh. (* this moves the ens into the continuation *)

      apply s_sh. }
    { apply s_rs_val.
      eapply s_seq.
      apply s_defun. reflexivity.
      apply ens_pure_intro. reflexivity. }
  }
  { (* app *)
    apply s_fex. eexists.
    eapply s_unk. resolve_fn_in_env.
    simpl.
    eapply s_unk.
    (* TODO resolve should solve this *)
    { unfold Fmap.update.
      rewrite Fmap.read_union_r.
      rewrite Fmap.read_union_l.
      apply Fmap.read_single.
      apply Fmap.indom_single.
      apply fmap_not_indom_of_neq.
      easy. }
    simpl.

    apply s_rs_val.

    eapply s_seq.
    apply ens_void_pure_intro.
    jauto.

    eapply s_seq.
    (* TODO ens_pure_info has more info, empty heaps? *)
    apply ens_pure_intro. intuition reflexivity.
    apply ens_pure_intro. reflexivity.
  }
Qed.

End Examples.

(** * Shift-freedom *)
(** Syntactic definition. This is not strong enough to prove the reduction rules, particularly that executions do not end in a [shft]. A stronger definition likely is [Inductive] and enumerates the cases which return [norm], so we can do induction on it. This should entail the semantic definition. With how we do things, the semantic definition is both sufficient and more convenient, so this is mostly left here for posterity. *)
Fixpoint syn_shift_free (f:flow) : Prop :=
  match f with
  | req _ f => syn_shift_free f
  | ens q => True
  | seq f1 f2 => syn_shift_free f1 /\ syn_shift_free f2
  | fex f => exists b, syn_shift_free (f b)
  | fall f => forall b, syn_shift_free (f b)
  | unk _ _ r => False
  | intersect f1 f2 => syn_shift_free f1 /\ syn_shift_free f2
  | disj f1 f2 => syn_shift_free f1 /\ syn_shift_free f2
  | sh _ _ _ => False
  | shc _ _ _ _ => False
  | rs _ r => True
  | defun _ _ => True
  | discard f _ => syn_shift_free f
  end.

(* This counterexample shows that the same stores, heaps, and [f] do not necessarily give rise to the same result. This is what makes proving shift-freedom annoying: knowing that the result is [norm] is not enough to know that the result cannot be [shft], given an arbitrary [f]. *)
Example cex_same_store_heap_f : forall s1 h1,
  exists f,
    satisfies s1 s1 h1 h1 (norm (vint 1)) f /\
    satisfies s1 s1 h1 h1
      (shft "x" empty vunit (fun r2 => rs (ens (fun r => \[r = vunit])) r2)) f.
Proof.
  intros.
  exists (disj (ens (fun r => \[r = vint 1])) (sh "x" empty vunit)).
  subst.
  split.
  { apply s_disj_l.
    apply ens_pure_intro. reflexivity. }
  { apply s_disj_r.
    unfold empty, ens_.
    applys_eq s_sh. }
Qed.

(** Semantic definition of shift-freedom. *)
Definition shift_free (f:flow) : Prop :=
  forall s1 s2 h1 h2 k fk r b,
  (* exists v, *)
    (* satisfies s1 s2 h1 h2 (norm v) f /\ *)
      not (satisfies s1 s2 h1 h2 (shft k fk r (fun r2 => rs b r2)) f).

(** [Sh#], the syntactic analogue of [shft], or a CPS version of [Sh], where the continuation is shift-free. *)
Definition shs x fb vr c : flow :=
  ens_ \[forall r, shift_free (c r)];; shc x fb vr c.

Notation "'shs' '(' k '.' fb ')' '(' vr '.' '⟨' fk '⟩' ')'" := (shs k fb vr (fun r => rs fk r))
  (at level 80, format "'shs'  '(' k '.'  fb ')'  '(' vr '.'  '⟨'  fk  '⟩' ')'", only printing) : flow_scope.

Lemma sf_ens : forall Q,
  shift_free (ens Q).
Proof.
  unfold shift_free, not. intros.
  inverts H as H. destr H.
  false.
Qed.
(* #[local] Hint Resolve sf_ens : core. *)

Lemma sf_defun : forall x uf,
  shift_free (defun x uf).
Proof.
  unfold shift_free, not. intros.
  inverts H as H.
Qed.

Lemma sf_req : forall H f,
  shift_free f ->
  shift_free (req H f).
Proof.
  unfold shift_free, not. intros.
  inverts H1 as H1.
  (* TODO we need to know that the req is provable *)
Abort.

Lemma sf_req_pure : forall P f,
  P ->
  shift_free f ->
  shift_free (req \[P] f).
Proof.
  unfold shift_free, not. intros.
  inverts H1 as H1.
  specializes H1 empty_heap h1 ___.
  hintro.
  assumption.
Qed.

Lemma sf_rs_val : forall f r,
  shift_free f ->
  shift_free (rs f r).
Proof.
  unfold shift_free, not; intros.
  inverts H0 as H0. destr H0.
  applys~ H H0.
Qed.

Lemma sf_rs : forall f r,
  shift_free (rs f r).
Proof.
  unfold shift_free, not; intros.
  (* TODO try this again without dependent induction? *)
  (* remember (rs f r) as e eqn:He.
  remember (shft x k r0 b) as r1 eqn:Hr.
  induction H; try inversion He; try inversion Hr.
  injects He. subst. clear TEMP TEMP0 H1. *)
  dependent induction H.
  eapply IHsatisfies2.
  reflexivity.
  reflexivity.
Qed.

Lemma sf_seq : forall f1 f2,
  shift_free f1 ->
  shift_free f2 ->
  shift_free (f1;; f2).
Proof.
  unfold shift_free, not. intros.
  inverts H1 as H1; destr H1.
  { specializes~ H0 H9. }
  { specializes~ H H1. }
Qed.

Lemma sf_fex : forall A (p:A->flow),
  (forall b, shift_free (p b)) ->
  shift_free (@fex A p).
Proof.
  unfold shift_free, not. intros.
  inverts H0 as H0. destr H0.
  eapply H.
  exact H1.
Qed.

Lemma sf_seq_inv : forall f1 f2,
  shift_free (f1;; f2) ->
  shift_free f1 /\ shift_free f2.
Proof.
  unfold shift_free, not. intros.
  split; intros.
  { eapply H.
    apply s_seq_sh.
    eassumption. }
  { eapply H.
    eapply s_seq.
    2: eassumption.
    (* TODO need to know that shift-free means
      f1 goes to norm, possible to add *)
    admit.
  }
Abort.

Lemma sf_seq_inv1 : forall f1 f2,
  shift_free (f1;; f2) ->
  shift_free f1.
Proof.
  unfold shift_free, not. intros.
  eapply H.
  apply s_seq_sh.
  eassumption.
Qed.

Ltac shiftfree :=
  lazymatch goal with
  | |- shift_free (rs _ _) => apply sf_rs
  | |- shift_free (defun _ _) => apply sf_defun
  | |- shift_free (ens _) => apply sf_ens
  | |- shift_free (ens_ _) => unfold ens_; apply sf_ens
  | |- shift_free (_ ;; _) => apply sf_seq; shiftfree
  | |- shift_free (fex _) => apply sf_fex; intros; shiftfree
  | _ => auto
  end.

(* Immediately dispatch goals where we have an assumption that a shift-free thing produces a shift *)
Ltac no_shift :=
  lazymatch goal with
  | H: satisfies _ _ _ _ (shft _ _ _ _) (ens _) |- _ =>
    apply sf_ens in H; false
  | H: satisfies _ _ _ _ (shft _ _ _ _) (ens_ _) |- _ =>
    unfold ens_ in H; apply sf_ens in H; false
  | H: satisfies _ _ _ _ (shft _ _ _ _) (rs _ _) |- _ =>
    apply sf_rs in H; false
  | H: satisfies _ _ _ _ (shft _ _ _ _) (defun _ _) |- _ =>
    apply sf_defun in H; false
  | _ => idtac
  end.

Ltac vacuity ::= false; no_shift.

(* Given a [satisfies ... (shs ... k)] hypothesis,
  produces [satisfies ... (shc ... k)] and an assumption
  that k is shift-free *)
Ltac elim_shs H :=
  lazymatch type of H with
  | satisfies _ _ _ _ _ (shs _ _ _ _) =>
    inverts H as H; no_shift; destr H;
    apply ens_void_pure_inv in H; destr H;
    lazymatch goal with
    | H: norm _ = norm _ |- _ => injects H
    end;
    subst
  | _ => fail
  end.

(* Given a [satisfies ... (shs ... k)] goal,
  we have to prove [k] is shift-free before we can reduce
  it into a [satisfies ... (shc ... k)] goal. *)
Ltac intro_shs :=
  lazymatch goal with
  | |- satisfies _ _ _ _ _ (shs _ _ _ _) =>
    eapply s_seq; [ apply ens_void_pure_intro | ]
  | _ => fail
  end.

(** * Reduction rules *)
Lemma red_normal : forall f r,
  shift_free f ->
  entails (rs f r) f.
Proof.
  introv Hsf.
  unfold entails. intros.
  inverts H as H; destr H.
  { (* this case cannot be as f is shift-free *)
    apply Hsf in H.
    false. }
  { assumption. }
Qed.

Lemma red_skip : forall f1 f2 r,
    shift_free f1 ->
    entails (rs (f1;; f2) r) (f1;; rs f2 r).
Proof.
  introv Hsf.
  unfold entails. intros.
  inverts H as H; destr H.
  { (* if either f1 or f2 produce a shift *)
    inverts H as H. destr H.
    { (* f2 produces a shift *)
      eapply s_seq.
      exact H.
      eapply s_rs_sh.
      exact H8.
      exact H7. }
    { (* f1 cannot produce a shift as it is shift-free *)
      apply Hsf in H.
      false. } }
  { (* if f1 returns *)
    inverts H as H. destr H.
    eapply s_seq.
    exact H.
    apply s_rs_val.
    assumption. }
Qed.

Lemma red_init : forall x b r,
  entails (sh x b r)
    (shs x b r (fun r2 => rs (ens (fun r1 => \[r1 = r])) r2)).
Proof.
  unfold entails. intros.
  inverts H as H.
  (* note that the application of this rule is very sensitive
    to the precise terms appearing in the equality... *)
    (* Unset Printing Notations. Set Printing Coercions. Set Printing Parentheses. *)
  intro_shs. intros. shiftfree.
  apply s_shc. 
Qed.

Lemma red_extend : forall f2 x b fk v,
  shift_free f2 ->
  entails (shs x b v (fun r2 => rs fk r2);; f2)
    (shs x b v (fun r2 => rs (fk;; f2) r2)).
Proof.
  unfold entails. introv Hsf. introv H.
  inverts H as H.
  { destr H. elim_shs H. vacuous. }
  { elim_shs H.
    intro_shs. intros r2. specializes H0 r2. apply~ sf_rs.
    inverts H7 as H7.
    cont_eq.
    apply s_shc. }
Qed.

Lemma red_acc : forall f2 x v r fk fb,
  entails (rs (shs x fb v (fun r2 => rs fk r2);; f2) r)
    (rs (shs x fb v (fun r2 => rs (fk;; f2) r2)) r).
Proof.
  intros.
  unfold entails. intros.
  (* invert the rs *)
  inverts H as H.
  2: {
    (* the body of the reset doesn't produce a value *)
    (* s_rs_val case *)
    inverts H as H. destr H.
    (* TODO extend vacuous to elim shs *)
    elim_shs H. vacuous. }
  {
    (* the body produces a shift *)
    (* s_rs_sh case *)
    (* invert the seq *)
    inverts H as H. { destr H. elim_shs H. vacuous. }
    cont_eq.
    elim_shs H.
    (* we know that the shs is what produces a shift *)
    (* f2 goes in the continuation and under a reset *)
    (* now start reasoning backwards *)
    inverts H8 as H8.
    cont_eq.
    eapply s_rs_sh.
    intro_shs. apply sf_rs.
    apply s_shc.
    applys_eq H7.
  }
Qed.

Lemma red_shift_elim : forall x v r fk fb,
  entails (rs (shs x fb v (fun r2 => rs fk r2)) r)
    (defun x (fun a r =>
      rs (ens_ \[v = a];; fk) r);; rs fb r).
Proof.
  unfold entails. intros.
  inverts H as H. 2: { inverts H as H. destr H. vacuous. }
  elim_shs H. clear H0.
  inverts H8 as H8.
  cont_eq.
  eapply s_seq.
  apply s_defun. reflexivity.
  applys_eq H7.
Qed.

(** * Entailment, entailment sequent, normalization *)
Lemma norm_reassoc : forall H f1 f2,
  shift_free f1 ->
  entails (req H f1;; f2) (req H (f1;; f2)).
Proof.
  unfold entails.
  intros.
  inverts H1 as H1.
  2: { (* handle shift. it may be possible to relax this *)
    apply s_req. intros.
    inverts H1 as H1.
    specializes H1 H2 H3 H4.
    apply H0 in H1.
    false.
  }
  destr H1.

  (* find out about req *)
  constructor. intros hp hr. intros.

  (* prove the req *)
  inverts H1 as H1.
  specializes H1 hp hr H2 ___.
  applys* s_seq h3 r1.
Qed.

Lemma norm_discard : forall f1 f2 x,
  entails f1 f2 ->
  entails (discard f1 x) (discard f2 x).
Proof.
  unfold entails. intros.
  inverts H0 as H0.
  apply s_discard.
  eauto.
  reflexivity.
Qed.

Lemma norm_defun : forall x uf a r,
  entails (defun x uf;; unk x a r) (defun x uf;; uf a r).
Proof.
  unfold entails. intros.
  inverts H as H; [ | vacuous ]. destr H.
  pose proof H.
  inverts H as H.
  inverts H7 as H7. destr H7.
  rewrite fmap_read_update in H7.
  (* injects H7. *)
  applys* s_seq.
Qed.

Lemma ent_seq_defun : forall s x uf f2 f1,
  entails_under (Fmap.update s x uf) f1 f2 ->
  entails_under s (defun x uf;; f1) (defun x uf;; f2).
Proof.
  unfold entails_under. intros.
  inverts H0 as H0; [ | vacuous ].
  pose proof H0.
  inverts H0 as H0.
  apply H in H8.
  applys* s_seq.
Qed.

(* Check Fmap.update. *)
Definition env_independent1 k f := forall u s1 s2 h1 h2 R,
  satisfies s1 s2 h1 h2 R f ->
    satisfies (Fmap.update s1 k u) (Fmap.update s2 k u) h1 h2 R f.

(* Lemma independent_weaken : forall f x u,
  env_independent1 x f ->
  entails (defun x u;; f;; discard x) f.
  (* entails f (defun x u;; f;; discard x). *)
Proof.
  unfold entails. intros.

  inverts H0 as H0.
  inverts H0 as H0.
  inverts H8 as H8.
  inverts H0 as H0.

  (* specializes H H8.
  applys_eq H. *)

  (* eapply s_seq.
  apply s_defun. reflexivity.
  eapply s_seq. *)

  admit.

  (* specializes H H0.
  applys_eq H. *)

  (* inverts H as H. destr H.
  apply s_ens.
  exists v h3.
  splits*. *)
Qed. *)

Lemma independent_ens1 : forall Q k,
  env_independent1 k (ens Q).
Proof.
  unfold env_independent1.
  intros.
  inverts H as H. destr H.
  apply s_ens.
  exists v h3.
  splits*.
Qed.


Definition env_invariant x f := forall u s1 s2 h1 h2 R,
  ~ Fmap.indom s1 x ->
  (*
  ~ Fmap.indom s2 x -> *)
  satisfies (Fmap.update s1 x u) s2 h1 h2 R f ->
  satisfies s1 (Fmap.remove s2 x) h1 h2 R f.

Lemma env_invariant_ens : forall Q x,
  env_invariant x (ens Q).
Proof.
  unfold env_invariant. intros.
  inverts H0 as H0. destr H0.

  pose proof (Fmap.disjoint_single_of_not_indom u H).
  unfold Fmap.update.
  rewrite Fmap.remove_union_single_l.
  apply s_ens.
  exists v h3.
  splits*.
  assumption.
Qed.

(* Definition flow_res (f:flow) (v:val) : Prop :=
  forall s1 s2 h1 h2 R, satisfies s1 s2 h1 h2 R f -> R = norm v. *)

Lemma ent_seq_defun_discard : forall x uf f s,
  (* flow_res f vunit -> *)
  shift_free f ->
  env_invariant x f ->
  ~ Fmap.indom s x ->
  entails_under s (defun x uf;; discard f x) f.
Proof.
(* Hres  *)
  unfold entails_under. introv Hsf He Hid H. intros.
  inverts H as H; no_shift.
  inverts H as H.
  inverts H7 as H7.

  (* inverts H0 as H0. *)
  unfold env_invariant in He.
  specializes He Hid H7.
  clear H7.

  unfold Fmap.update in *.
  rewrite Fmap.remove_union_single_l in He.
  2: { assumption. }
  rewrite Fmap.remove_union_single_l.
  2: { assumption. }

  rewrite remove_not_indom in He.

  assumption.
  assumption.
Qed.

(* Definition env_independent k f := forall u s1 s2 h1 h2 R,
  ~ Fmap.indom s1 k ->
  ~ Fmap.indom s2 k ->
  satisfies (Fmap.update s1 k u) (Fmap.update s2 k u) h1 h2 R f ->
  satisfies s1 s2 h1 h2 R f.
*)

Lemma ens_inv : forall s1 s2 h1 h2 R Q,
  satisfies s1 s2 h1 h2 R (ens Q) ->
  s1 = s2.
Proof.
  intros.
  inverts H as H. destr H.
  reflexivity.
Qed.

(* Lemma independent_weaken : forall f x u,
  env_independent x f ->
  entails (defun x u;; f;; discard x) f.
Proof.
  unfold entails. intros.
  inverts H0 as H0; no_shift.
  inverts H0 as H0.
  inverts H8 as H8.
  - inverts H0 as H0.

    admit.
  - admit.

Qed. *)

(* Lemma independent_ens : forall Q k,
  env_independent k (ens Q).
Proof.
  unfold env_independent.
  intros.
  (* inverts H as H. destr H. *)

  pose proof (Fmap.disjoint_single_of_not_indom u H) as H2.
  rewrite Fmap.disjoint_comm in H2.
  pose proof (Fmap.disjoint_single_of_not_indom u H0) as H3.
  rewrite Fmap.disjoint_comm in H3.
  (* specializes Hi H0.
  forward Hi by fmap_disjoint. *)


  pose proof (ens_inv H1) as H4.
  (* apply ens_inv in H1. *)
  unfold Fmap.update in H4.
  pose proof (union_eq_inv_of_disjoint) as H5.
  specializes H5 H2 H3.

  forward H5.
  fmap_eq.
  rewrite Fmap.union_comm_of_disjoint.
  rewrite H4.
  fmap_eq.

  fmap_disjoint.
  subst.
  apply s_ens.

  (* destruct R. *)
  inverts H1 as H1. destr H1.

  exists v h3.
  splits*.
Qed. *)

  (* exists s3 s4, *)
  (* Fmap.disjoint s1 s3 -> *)
  (* Fmap.disjoint s2 s4 -> *)
    (* satisfies (s1 \u s3) (s2 \u s4) h1 h2 R f. *)

(* does not depend on anything vs does not depend on anything ELSE *)
(* ens does not depend on anything *)

(* Lemma ent_discard_indep : forall k u f s1 s2 h1 h2 R,
  env_independent k f ->
  (* not (Fmap.indom s1 k) -> *)
  satisfies s1 s2 h1 h2 R (defun k u;; f) ->
  satisfies s1 s2 h1 h2 R f.
Proof.
  (* introv Hi Hf H. *)
  intros.
  inverts H0 as H0. 2: { no_shift. }
  inverts H0 as H0.
  


  (* inverts H as H. 2: { no_shift. } *)
  (* inverts H as H. *)
  (* unfold env_independent in Hi. *)

  (* specializes Hi H7. *)
  (* destr Hi. *)




  inverts H1 as H1.


Lemma ent_discard_indep : forall k u f s1 s2 h1 h2 R,
 env_independent f ->
  not (Fmap.indom s1 k) ->
  satisfies s1 s2 h1 h2 R f <->
  satisfies s1 s2 h1 h2 R (defun k u;; f).
Proof.
  unfold entails_under. introv Hi Hd.
  iff H; intros.
  {
    eapply s_seq.
    apply s_defun. reflexivity.
    unfold env_independent in Hi.
    specializes Hi H.
    (* (Fmap.single k u) empty_env. *)

    pose proof (Fmap.disjoint_single_of_not_indom u Hd).
    rewrite Fmap.disjoint_comm in H0.
    specializes Hi H0.
    forward Hi by fmap_disjoint.

    unfold Fmap.update.
    rew_fmap *.
    rewrite Fmap.union_comm_of_disjoint; auto.
  }
  {
    admit.
    (* inverts H as H; [ | vacuous ].
    inverts H as H.


    unfold env_independent in Hi.
    specializes Hi H7.

    (Fmap.single k u) empty_env.

    pose proof (Fmap.disjoint_single_of_not_indom u Hd).
    rewrite Fmap.disjoint_comm in H0.
    specializes Hi H0.
    forward Hi by fmap_disjoint.


    specializes Hi (Fmap.update s1 k u) s2 s1. *)
    (* apply* Hi. *)
  }
  (* Qed. *)
  Admitted.



Lemma ent_discard_intro1 : forall k u f1 f2 s,
  env_independent f2 ->
  entails_under s f1 f2 <->
  entails_under s f1 (defun k u;; f2).
Proof.
  unfold entails_under. introv Hi.
  iff H; intros.
  { apply H in H0.
    apply* ent_discard_indep. }
  { apply H in H0.
    apply* ent_discard_indep. }
  Qed.


Lemma independent_ens_void : forall k u H f,
  independent k u f ->
  independent k u (ens_ H f).
Proof.


Lemma independent_req : forall k u H f,
  independent k u f ->
  independent k u (req H f).
Proof.
  unfold independent.
  intros.
  iff H1.
  {
    apply s_req. intros.
    inverts H1 as H1.
    specializes H1 H2 H3 H4.
    rewrite <- H0. 
    assumption.
  }
  {
    apply s_req. intros.
    inverts H1 as H1.
    specializes H1 H2 H3 H4.
    rewrite H0. 
    assumption.
    }
    Qed.


Lemma independent_seq : forall k u H f1 f2,
    shift_free f1 ->
  independent k u f1 ->
  independent k u f2 ->
  independent k u (seq f1 f2).
Proof.
  unfold independent.
  intros.
  iff Hseq.
  {
    inverts Hseq as Hseq; [ | apply H0 in Hseq; false ].
    eapply s_seq.
    rewrite <- H1.
    eassumption.
    assumption.
  }
  {
    inverts Hseq as Hseq; [ | apply H0 in Hseq; false ].
    eapply s_seq.
    rewrite H1.
    eassumption.
    assumption.
}
    Qed. *)

(* Lemma ent_seq_defun_discard :
forall x uf f2 f1,
(* forall x, *)
  (* ~ Fmap.indom s x -> *)
  (* entails_under (Fmap.update s x uf) (discard f1 x) (discard f2 x) -> *)
  (* entails_under s (defun x uf;; f1) f2. *)
  (* entails_under s f1 f2 -> *)
  (* entails_under s (defun x uf;; discard f1 x) f2 -> *)
  (* entails_under s f1 f2 *)
  entails (defun x uf;; discard f2 x) f2.
   (* -> *)
  (* entails f1 f2 *)
  (* entails f1 f2 ->
  entails (defun x uf;; discard f1 x) f2 *)
  (* entails_under empty_env (defun x arbitrary;; discard empty x) empty. *)
Proof.
  (* intros. *)
  (* unfold entails_under. intros. *)
  unfold entails. intros.
  (* apply H.
  applys s_seq.
  constructor. reflexivity. *)

Abort. *)

Lemma unk_inv : forall s1 s2 h1 h2 R x a v uf,
  Fmap.read s1 x = uf ->
  satisfies s1 s2 h1 h2 R (unk x a v) ->
  satisfies s1 s2 h1 h2 R (uf a v).
Proof.
  intros.
  inverts H0 as H0.
  rewrite H in H0.
  assumption.
Qed.

Lemma ent_unk : forall s (x:var) a v uf,
  Fmap.read s x = uf ->
  entails_under s (unk x a v) (uf a v).
Proof.
  unfold entails_under. intros.
  eapply unk_inv.
  exact H.
  assumption.
Qed.

Lemma norm_rs_rs : forall f r r1,
  entails (rs (rs f r1) r) (rs f r1).
Proof.
  unfold entails. intros.
  inverts H as H.
  { no_shift. }
  { assumption. }
Qed.

Lemma seq_assoc : forall s1 s2 h1 h2 R f1 f2 f3,
  shift_free f1 ->
  shift_free f2 ->
  satisfies s1 s2 h1 h2 R (f1;; f2;; f3) <->
  satisfies s1 s2 h1 h2 R ((f1;; f2);; f3).
Proof.
  intros.
  split; intros.
  { inverts H1 as H1. 2: { apply H in H1; false. } destr H1.
    inverts H9 as H9. 2: { apply H0 in H9; false. } destr H9.
    applys* s_seq.
    applys* s_seq. }
  { inverts H1 as H1.
    { destr H1.
      inverts H1 as H1.
      destr H1.
      applys* s_seq.
      applys* s_seq. }
    inverts H1 as H1. destr H1.
    apply H0 in H9. false.
    apply H in H1. false. }
Qed.

Lemma norm_seq_assoc : forall f1 f2 f3,
  shift_free f1 ->
  shift_free f2 ->
  bientails (f1;; f2;; f3) ((f1;; f2);; f3).
Proof.
  intros.
  split; intros; now apply seq_assoc.
Qed.

(* A pure fact about a result on the left of a seq doesn't contribute anything *)
Lemma norm_seq_pure_l : forall p f,
  entails (ens (fun r => \[p r]);; f) f.
Proof.
  unfold entails. intros.
  inverts H as H; [ | vacuous ]. destr H.
  inverts H as H. destr H. hinv H. injects H0. subst.
  rew_fmap *.
Qed.

Lemma norm_ens_true : forall f,
  entails (ens_ \[True];; f) f.
Proof.
  unfold entails. intros.
  inverts H as H; [ | no_shift ]. destr H.
  inverts H as H. destr H. hinv H. hinv H. hinv H2. injects H0. subst.
  rew_fmap *.
Qed.

Lemma norm_ens_eq : forall f (a:val),
  entails (ens_ \[a = a];; f) f.
Proof.
  unfold entails. intros.
  inverts H as H; [ | no_shift ]. destr H.
  inverts H as H. destr H. hinv H. hinv H. hinv H2. injects H0. subst.
  rew_fmap *.
Qed.

Lemma ent_seq_ens_l : forall env f f1 P,
  (P -> entails_under env f1 f) ->
  entails_under env (ens_ \[P];; f1) f.
Proof.
  unfold entails_under. intros.
  inverts H0 as H0; no_shift. destr H0.
  inverts H0 as H0. destr H0.
  hinv H0. hinv H3. hinv H0. subst. injects H1.
  rew_fmap *.
Qed.

Lemma ent_seq_ens_dep_l : forall env f f1 p,
  (forall r1, p r1 -> entails_under env f1 f) ->
  entails_under env (ens (fun r => \[p r]);; f1) f.
Proof.
  unfold entails_under. intros.
  inverts H0 as H0; no_shift. destr H0.
  inverts H0 as H0. destr H0.
  hinv H0. injects H1. subst.
  rew_fmap *.
Qed.

Lemma norm_ens_ens_void_l : forall H Q,
  bientails (ens_ H;; ens Q) (ens (Q \*+ H)).
Proof.
  unfold entails.
  iff H0.
  { inverts H0 as H1; destr H1; no_shift.
    inverts H1 as H1; destr H1; no_shift. injects H0. hinv H1. hinv H0.
    inverts H8 as H8; destr H8; no_shift.
    constructor.
    exists v0 (h4 \u x0).
    splits*.
    subst. rew_fmap *.
    apply* hstar_intro. }
  { inverts H0 as H0. destr H0. hinv H0.
    eapply s_seq.
    constructor.
    exists vunit.
    exists x0.
    splits*.
    { hintro. jauto. }
    { constructor. exists v x. jauto. } }
Qed.

Lemma ent_seq_ens_sl_ex: forall env A (c:A->hprop) f,
  entails_under env (ens_ (\exists b, c b);; f)
  (∃ b, ens_ (c b);; f).
Proof.
  unfold entails_under. intros.
  inverts H as H. 2: vacuous.
  inverts H as H. destr H.
  hinv H. hinv H.
  apply hexists_inv in H2. destr H2.
  constructor. exists x1.
  applys* s_seq s3 (h1 \u x0) vunit.
  - constructor. exs. splits*. hintro; jauto.
  - subst. rew_fmap *.
Qed.

Lemma ent_all_r : forall f A (fctx:A -> flow) env,
  (forall b, entails_under env f (fctx b)) ->
  entails_under env f (fall (fun b => fctx b)).
Proof.
  unfold entails_under. intros.
  constructor. intros b.
  auto.
Qed.

Lemma ent_all_l : forall f A (fctx:A -> flow) env,
  (exists b, entails_under env (fctx b) f) ->
  entails_under env (fall (fun b => fctx b)) f.
Proof.
  unfold entails_under. intros.
  destr H.
  apply H1.
  inverts H0 as H0. specializes H0 b.
  assumption.
Qed.

Lemma ent_ex_l : forall f A (fctx:A -> flow) env,
  (forall b, entails_under env (fctx b) f) ->
  entails_under env (fex (fun b => fctx b)) f.
Proof.
  unfold entails_under. intros.
  inverts H0 as H0. destr H0.
  specializes H H1.
  auto.
Qed.

Lemma ent_ex_r : forall f A (fctx:A -> flow) env,
  (exists b, entails_under env f (fctx b)) ->
  entails_under env f (fex (fun b => fctx b)).
Proof.
  unfold entails_under. intros.
  destr H.
  constructor. exists b.
  auto.
Qed.

Lemma ent_seq_all_l : forall f f1 A (fctx:A -> flow) env,
  (exists b, entails_under env (fctx b;; f1) f) ->
  entails_under env (fall (fun b => fctx b);; f1) f.
Proof.
  unfold entails_under. intros.
  destr H.
  apply H1.
  inverts H0 as H0.
  { inverts H0 as H0. specializes H0 b.
    applys* s_seq. }
  { inverts H0 as H0. specializes H0 b.
    apply* s_seq_sh. }
Qed.

Lemma ent_req_r : forall f f1 H env,
  entails_under env (ens_ H;; f) f1 ->
  entails_under env f (req H f1).
Proof.
  unfold entails_under. intros.
  constructor. intros.
  apply H0.
  applys s_seq (hr \+ hp) (vunit).
  { constructor. exists vunit. exists hp.
    intuition.
    rewrite hstar_hpure_l. intuition. }
  { rewrite <- H3. assumption. }
Qed.

Lemma ent_ens_l : forall env f P,
  (P -> entails_under env empty f) ->
  entails_under env (ens_ \[P]) f.
Proof.
  unfold entails_under. intros.
  inverts H0 as H0. destr H0.
  hinv H0. hinv H0. hinv H3.
  apply H.
  assumption.
  subst. rew_fmap. apply empty_intro.
Qed.

Lemma ent_ens_single_pure : forall env P P1,
  (P1 -> P) ->
  entails_under env (ens_ \[P1]) (ens_ \[P]).
Proof.
  unfold entails_under. intros.
  inverts H0 as H0. destr H0. hinv H0. hinv H3. hinv H0.
  constructor. exists vunit. exists empty_heap.
  splits*.
  subst*.
  hintro.
  split*.
  hintro. auto.
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

Lemma ent_disj_l : forall f1 f2 f3 env,
  entails_under env f1 f3 ->
  entails_under env f2 f3 ->
  entails_under env (disj f1 f2) f3.
Proof.
  unfold entails_under. intros.
  inverts H1 as H1; auto.
Qed.

Lemma norm_seq_ens_empty : forall f,
  entails (ens_ \[];; f) f.
Proof.
  unfold entails. intros.
  inverts H as H. 2: vacuous. destr H.
  inverts H as H.
  destr H.
  rew_heap in H.
  hinv H.
  subst.
  rew_fmap *.
Qed.

Lemma norm_rs_ex : forall A ctx r,
  entails (rs (∃ (x:A), ctx x) r) (∃ (x:A), rs (ctx x) r).
Proof.
  unfold entails. intros.
  inverts H as H.
  {
    inverts H as H. destr H.
    constructor. exists b.
    eapply s_rs_sh; jauto. }
  { inverts H as H. destr H.
    constructor. exists b.
    apply s_rs_val.
    assumption. }
Qed.

Lemma norm_rs_all : forall A ctx r,
  entails (rs (∀ (x:A), ctx x) r) (∀ (x:A), rs (ctx x) r).
Proof.
  unfold entails. intros.
  inverts H as H.
  {
    constructor. intros b.
    inverts H as H. specializes H b.
    eapply s_rs_sh; jauto. }
  { constructor. intros b.
    inverts H as H. specializes H b.
    apply s_rs_val.
    assumption. }
Qed.

(** * Reduction example *)
(**
  < (shift k. k i1) + (shift k1. k1 i2) >
  assuming left-to-right evaluation
  k1 takes i1, result is i1 + i2
  k2 takes i2, result is also i1 + i2
*)
Example e1_red : forall x1 x2 i1 i2 r3, exists f,
  entails_under empty_env
    (rs
      (sh x1 (unk x1 (vint i1) (vint (i1 + i2))) (vint i1);;
        sh x2 (unk x2 (vint i2) (vint (i1 + i2))) (vint i2);;
        ens (fun r => \[r = vint (i1 + i2)])) r3) f.
Proof.
  intros.
  eexists.

  rewrite red_init.
  rewrite red_acc.
  rewrite red_shift_elim.
  apply ent_seq_defun.

  (* TODO funfold1 *)
  rewrites (>> ent_unk x1); [ resolve_fn_in_env | ].
  simpl.

  rewrite norm_ens_eq.
  rewrite (norm_seq_pure_l (fun r0 => r0 = vint i1)).

  rewrite red_init.
  rewrite red_acc.
  rewrite red_shift_elim.
  rewrites (>> red_skip sf_defun).
  apply ent_seq_defun.

  rewrites (>> ent_unk x2); [ resolve_fn_in_env | ].
  simpl.

  rewrite norm_ens_eq.

  rewrite red_normal; shiftfree.
  rewrite red_normal; shiftfree.
  rewrite red_normal; shiftfree.

  rewrite (norm_seq_pure_l (fun r4 => r4 = vint i2)).
  apply entails_under_refl.
Qed.

(** * Correspondence with the paper *)
(** ** Differences *)
(** #<!-- this space is needed!!-->#
- Function pointer values [vfptr] enable arbitrary higher-order staged formulae. A [defun] staged formula (conceptually just an [ens] which binds a function value) and an output [senv] added to [satisfies] complete this, allowing shift bodies to return continuations.
- The semantics guarantees that [shft]/[Sh#] continuations are #<i>shift-free by construction</i>#, by having a [rs] as their topmost form. This significantly simplifies the proofs of the reduction rules. *)
(** ** Section 4.3. Shift/Reset Reduction *)
(** The reduction rules are proved as lemmas.
- #<a href="&num;red_skip">red_skip</a>#
- #<a href="&num;red_normal">red_normal</a>#
- #<a href="&num;red_init">red_init</a>#
- #<a href="&num;red_extend">red_extend</a>#
- #<a href="&num;red_acc">red_acc</a>#
- #<a href="&num;red_shift_elim">red_shift_elim</a># *)
