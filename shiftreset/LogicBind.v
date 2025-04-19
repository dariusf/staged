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
Notation var_eq := String.string_dec.

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
  | passert (v: expr)
  | pref (v: expr)
  | pderef (v: expr)
  | passign (e1: expr) (e2: expr)
  | pif (v: expr) (e1: expr) (e2: expr)
  | papp (e1: expr) (e2: expr)
  | pshift (eb: var -> expr)
  | preset (e: expr).

Definition vadd (v1 v2 : val) : val :=
  match v1, v2 with
  | vint i1, vint i2 => vint (i1 + i2)
  | _, _ => vunit
  end.

Definition vand (v1 v2 : val) : val :=
  match v1, v2 with
  | vbool b1, vbool b2 => vbool (andb b1 b2)
  | _, _ => vunit
  end.

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
  | padd e1 e2 => padd (aux e1) (aux e2)
  | pminus x z => pminus x z
  | pfst x => pfst x
  | psnd x => psnd x
  | pvar x => if_y_eq x (pval v) e
  | passert b => passert (aux b)
  | pderef r => pderef (aux r)
  | passign x z => passign (aux x) (aux z)
  | pref v => pref (aux v)
  | pfun x t1 => pfun x (if_y_eq x t1 (aux t1))
  | pfix f x t1 => pfix f x (if_y_eq f t1 (if_y_eq x t1 (aux t1)))
  | papp e1 e2 => papp (aux e1) (aux e2)
  | plet x t1 t2 => plet x (aux t1) (if_y_eq x t2 (aux t2))
  | pif t0 t1 t2 => pif (aux t0) (aux t1) (aux t2)
  | pshift e => pshift (fun k => aux (e k))
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
  (* | seq : flow -> flow -> flow *)
  | bind : flow -> (val -> flow) -> flow
  | fex : forall (A:Type), (A -> flow) -> flow
  | fall : forall (A:Type), (A -> flow) -> flow
  | unk : var -> val -> flow
  | intersect : flow -> flow -> flow
  | disj : flow -> flow -> flow
(** The following are new: *)
  (* | sh : (var -> flow) -> flow *)
  | shc : (var -> flow) -> (val -> flow) -> flow
(** [sh k fb vr] is a shift with body [fb] and #<i>result</i># [vr]. *)
(** [k] names the continuation delimited by an enclosing [rs], and may occur in [fb] as an [unk] or [vfptr]. *)
(** [vr] is the #<i>result</i># of the shift, which is the value a shift appears to evaluate to when a continuation is taken. [vr] will be equal to the value that the continuation will be resumed with, and can be depended on in anything sequenced after a [sh]. *)
  (* | shc : var -> flow -> val -> (val -> flow) -> flow *)
(** [shc k fb vr fc] is a [sh] in CPS form, or the syntactic counterpart of [shft]. It carries a continuation whose argument is the equivalent of [sh]'s [r]. This continuation has a mixed first-/higher-order representation and has a [rs] as its topmost form. *)
(** Examples:
- the formula [Sh#(k. fb, vr, Rs(fc, r))] is represented as
  [shc "k" fb vr (fun r => rs fc r)]
- the continuation [(λ vr. < fc >)] is represented as
  a tuple [(vr, fun r => rs fc r)]. *)
  | rs : flow -> flow
(** [rs f vr] is a reset with body [f] and return value [vr]. *)
  | defun : var -> (val -> flow) -> flow
(** [defun x uf] is equivalent to [ens_ (x=(λ x r. uf x r))], where [x] can reside in the environment (which regular [ens_] cannot access).
  Should defun be scoped? We don't think so, because the resulting continuation is first-class and does not have a well-defined lifetime. *)
  (* | discard : flow -> var -> flow *)
  .

Definition seq (f1 f2:flow) := bind f1 (fun _ => f2).

Definition sh fb := shc fb (fun v => ens (fun r => \[r = v])).

Definition ens_ H := ens (fun r => \[r = vunit] \* H).

Definition empty := ens_ \[True].

Notation req_ H := (req H empty).

Definition ufun := val -> flow.

#[global]
Instance Inhab_ufun : Inhab ufun.
Proof.
  constructor.
  exists (fun (v:val) => ens_ \[]).
  constructor.
Qed.

Definition senv := Fmap.fmap var ufun.

Definition empty_env : senv := Fmap.empty.

(* shft's continuation could have a more general [A -> flow] type, but it can't be used in the semantics as long as it has to pass through ufun *)
Inductive result : Type :=
  | norm : val -> result
  | shft : (var -> flow) -> (val -> flow) -> result.
  (** See [shc] for what the arguments mean. *)

Declare Scope flow_scope.
Open Scope flow_scope.

Infix ";;" := seq (at level 38, right associativity) : flow_scope.

Notation "'let' x '=' f1 'in' f2" :=
  (bind f1 (fun x => f2))
  (at level 38, x binder, right associativity, only printing) : flow_scope.
    (* format "'[' 'let'  x  '='  f1  'in' ']' '/' '[' f2 ']'") : flow_scope. *)
    (* format "'[v' '[' 'let'  x  '='  f1  'in' ']' '/' '[' f2 ']' ']'") : flow_scope. *)

(* Definition ex_bind :=
  bind (ens (fun r => \[r = vint 1])) (fun x => ens (fun r => \[r = x])).
Definition ex_bind1 :=
  bind (ex_bind) (fun x => ens (fun r => \[r = x])).

Example e : True.
Proof.
  pose ex_bind1.
  unfold ex_bind1 in f.
  unfold ex_bind in f. *)

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

(* Notation "'shc' '(' k '.' fb ')' '(' vr '.' '⟨' fk '⟩' ')'" := (shc k fb vr (fun r => rs fk r))
  (at level 80, format "'shc'  '(' k '.'  fb ')'  '(' vr '.'  '⟨' fk '⟩' ')'", only printing) : flow_scope. *)

Notation "'ens' r '.' Q" := (ens (fun r => Q))
  (at level 80, format "'ens'  r '.'  Q" , only printing) : flow_scope.

Implicit Types s : senv.
Implicit Types h : heap.
Implicit Types H : hprop.
Implicit Types Q : postcond.
Implicit Types u : ufun.
(* Implicit Types c : val -> flow. *)
Implicit Types f : flow.
Implicit Types fb : var -> flow.
Implicit Types fk : val -> flow.
Implicit Types x y z k : var.
Implicit Types a v r : val.
Implicit Types R : result.
Implicit Types e : expr.

(** * Interpretation of a staged formula *)
Inductive satisfies : senv -> senv -> heap -> heap -> result -> flow -> Prop :=

  | s_req : forall (s1 s2:senv) H (h1 h2:heap) R f,
    (forall (hp hr:heap),
      H hp ->
      h1 = Fmap.union hr hp ->
      Fmap.disjoint hr hp ->
      satisfies s1 s2 hr h2 R f) ->
    satisfies s1 s2 h1 h2 R (req H f)

  | s_ens : forall s1 Q h1 h2 R,
    (exists v h3,
      R = norm v /\
      Q v h3 /\
      h2 = Fmap.union h1 h3 /\
      Fmap.disjoint h1 h3) ->
    satisfies s1 s1 h1 h2 R (ens Q)

  | s_bind : forall s3 h3 v s1 s2 f1 (f2:val->flow) h1 h2 R,
    satisfies s1 s3 h1 h3 (norm v) f1 ->
    satisfies s3 s2 h3 h2 R (f2 v) ->
    satisfies s1 s2 h1 h2 R (bind f1 f2)

  | s_fex s1 s2 h1 h2 R (A:Type) (f:A->flow)
    (H: exists b,
      satisfies s1 s2 h1 h2 R (f b)) :
    satisfies s1 s2 h1 h2 R (@fex A f)

  | s_fall s1 s2 h1 h2 R (A:Type) (f:A->flow)
    (H: forall b,
      satisfies s1 s2 h1 h2 R (f b)) :
    satisfies s1 s2 h1 h2 R (@fall A f)

  | s_unk : forall s1 s2 h1 h2 R xf uf a,
    Fmap.read s1 xf = uf ->
    satisfies s1 s2 h1 h2 R (uf a) ->
    satisfies s1 s2 h1 h2 R (unk xf a)

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

  | s_shc : forall s1 h1 fb fk,
    satisfies s1 s1 h1 h1
      (* (shft x shb v (fun r1 => rs (ens (fun r => \[r = v])) r1)) *)
      (shft fb fk)
      (shc fb fk)

    (** A [sh] on its own reduces to a [shft] containing an identity continuation. *)

  (* | s_shc s1 h1 x shb fk v :
    satisfies s1 s1 h1 h1
      (shft x shb v (fun r2 => rs fk r2))
      (shc x shb v (fun r2 => rs fk r2)) *)
    (** [shc] corresponds directly to [shft]. *)

  (* | s_seq_sh s1 s2 f1 f2 fk h1 h2 shb k (v:val) :
    satisfies s1 s2 h1 h2 (shft k shb v (fun r1 => rs fk r1)) f1 ->
    satisfies s1 s2 h1 h2 (shft k shb v (fun r1 => rs (fk;; f2) r1)) (f1;; f2) *)

  | s_bind_sh : forall s1 s2 f1 (f2:val->flow) fk h1 h2 (fb:var->flow),
    satisfies s1 s2 h1 h2 (shft fb fk) f1 ->
    satisfies s1 s2 h1 h2 (shft fb (fun r1 => bind (fk r1) f2))
      (bind f1 f2)

    (** This rule extends the continuation in a [shft] on the left side of a [seq]. Notably, it moves whatever comes next #<i>under the reset</i>#, preserving shift-freedom by constructon. *)

  | s_rs_sh : forall k s1 s2 fr h1 h2 rf s3 h3 (fb:var->flow) fk,
    satisfies s1 s3 h1 h3 (shft fb fk) fr ->
    satisfies (Fmap.update s3 k (fun a => rs (fk a))) s2
      h3 h2 rf (rs (fb k)) ->
    satisfies s1 s2 h1 h2 rf (rs fr)

    (** This rule applies when the body of a [rs] #<i>evaluates to</i># a [shft] (not when a [sh] is directly inside a [rs]; that happens in reduction). The continuation carried by the [shft] is known, so it is bound in (the environment of) the [sh]ift body before that is run. *)
    (** The two resets in the semantics are accounted for: one is around the shift body, and one is already the topmost form in the continuation. *)
    (** Note: because staged formulae are turned into values (via [shft] and being added to the [senv]), rewriting can no longer be done to weaken them. Environment entailment was an attempt at solving this problem; the Proper instances might have to be tweaked to allow rewriting too. Another possible solution is a syntactic entailment relation in the relevant rules to allow weakening. *)

  | s_rs_val : forall s1 s2 h1 h2 v f,
    satisfies s1 s2 h1 h2 (norm v) f ->
    satisfies s1 s2 h1 h2 (norm v) (rs f)

  | s_defun s1 s2 h1 x uf :
    (* ~ Fmap.indom s1 x -> *)
    s2 = Fmap.update s1 x uf ->
    satisfies s1 s2 h1 h1 (norm vunit) (defun x uf)

  (* | s_discard s1 s2 h x R f :
    satisfies s1 s2 h h R f ->
    s2 = Fmap.remove s1 x ->
    satisfies s1 s2 h h R (discard f x) *)

  .

Notation "s1 ',' s2 ','  h1 ','  h2 ','  r  '|=' f" :=
  (satisfies s1 s2 h1 h2 r f) (at level 30, only printing).

Lemma s_sh : forall s1 h1 (fb:var->flow),
  satisfies s1 s1 h1 h1
    (shft fb (fun r1 => ens (fun r => \[r = r1])))
    (sh fb).
Proof.
  unfold sh. intros.
  applys* s_shc.
Qed.

Lemma s_seq : forall s3 h3 r1 s1 s2 f1 f2 h1 h2 R,
  satisfies s1 s3 h1 h3 (norm r1) f1 ->
  satisfies s3 s2 h3 h2 R f2 ->
  satisfies s1 s2 h1 h2 R (seq f1 f2).
Proof.
  unfold seq. intros.
  applys* s_bind.
Qed.

Lemma s_ens_ : forall H h1 h2 s1,
  (exists h3,
    H h3 /\
    h2 = Fmap.union h1 h3 /\
    Fmap.disjoint h1 h3) ->
  satisfies s1 s1 h1 h2 (norm vunit) (ens_ H).
Proof.
  unfold ens_. intros.
  applys* s_ens.
  destr H0. exs. intuition. hintro. jauto.
Qed.

(** A specialization of [equal_f] for exposing the equalities in continuations after inversion. *)
(* Lemma cont_inj : forall fk1 fk2,
  (fun r1 => rs fk1 r1) = (fun r2 => rs fk2 r2) ->
  fk1 = fk2.
Proof.
  intros.
  apply equal_f with (x := arbitrary) in H.
  injects H.
  reflexivity.
Qed. *)

(* Ltac cont_eq :=
  lazymatch goal with
  | H: (fun _ => rs _ _) = (fun _ => rs _ _) |- _ =>
    lets ?: cont_inj H; subst; clear H; cont_eq
  | _ => idtac
  end. *)

(* Lemma cont_inj1 : forall fk1 fk2,
  (fun r1 => fk1) = (fun r2 => fk2) ->
  fk1 = fk2.
Proof.
  intros.
  apply equal_f with (x := arbitrary) in H.
  injects H.
  reflexivity.
Qed.

Ltac cont_eq1 :=
  lazymatch goal with
  | H: (fun _ => rs _ _) = (fun _ => rs _ _) |- _ =>
    lets ?: cont_inj1 H; subst; clear H; cont_eq
  | _ => idtac
  end. *)

(** * Entailment *)
Definition entails (f1 f2:flow) : Prop :=
  forall s1 s2 h1 h2 R,
    satisfies s1 s2 h1 h2 R f1 -> satisfies s1 s2 h1 h2 R f2.

Infix "⊑" := entails (at level 90, right associativity) : flow_scope.

Definition entails_under s1 f1 f2 :=
  forall h1 h2 s2 R,
    satisfies s1 s2 h1 h2 R f1 -> satisfies s1 s2 h1 h2 R f2.

(* Notation "env '⊢' f1 '⊑' f2" :=
  (entails_under env f1 f2) (at level 90, only printing) : flow_scope. *)

Definition bientails (f1 f2:flow) : Prop :=
  forall h1 h2 R s1 s2,
    satisfies s1 s2 h1 h2 R f1 <-> satisfies s1 s2 h1 h2 R f2.

Definition entails_sequent s1 s2 s3 s4 f1 f2 :=
  forall h1 h2 R,
    satisfies s1 s2 h1 h2 R f1 -> satisfies s3 s4 h1 h2 R f2.

Notation "s1 '⊢' f1 '⊑' f2" :=
  (entails_sequent s1 _ _ _ f1 f2) (at level 90, only printing) : flow_scope.

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
  eauto.
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

Instance entails_sequent_refl : forall env, Reflexive (entails_sequent env env env env).
Proof.
  unfold Reflexive, entails_sequent.
  intros.
  eauto.
Qed.

Instance entails_sequent_trans : forall env, Transitive (entails_sequent env env env env).
Proof.
  unfold Transitive, entails_sequent.
  intros.
  specializes H H1. destr H.
  specializes H0 H.
  auto.
Qed.

Instance entails_sequent_preorder : forall env, PreOrder (entails_sequent env env env env).
Proof.
  constructor.
  apply entails_sequent_refl.
  apply entails_sequent_trans.
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

(* Section ShiftFreedom. *)

(** * Shift-freedom *)
(** Semantic definition of shift-freedom. *)
Definition shift_free (f:flow) : Prop :=
  forall s1 s2 h1 h2 fb fk,
  (* exists v, *)
    (* satisfies s1 s2 h1 h2 (norm v) f /\ *)
      not (satisfies s1 s2 h1 h2 (shft fb fk) f).

(** [Sh#], the syntactic analogue of [shft], or a CPS version of [Sh], where the continuation is shift-free. *)
(* Definition shs x fb vr c : flow :=
  ens_ \[forall r, shift_free (c r)];; shc x fb vr c. *)

(* Notation "'shs' '(' k '.' fb ')' '(' vr '.' '⟨' fk '⟩' ')'" := (shs k fb vr (fun r => rs fk r))
  (at level 80, format "'shs'  '(' k '.'  fb ')'  '(' vr '.'  '⟨'  fk  '⟩' ')'", only printing) : flow_scope. *)

Class ShiftFree (f:flow) : Prop :=
  { shift_free_pf: shift_free f }.

Lemma sf_ens : forall Q,
  shift_free (ens Q).
Proof.
  unfold shift_free, not. intros.
  inverts H as H. destr H.
  false.
Qed.
(* this works, but relies on typeclass internals *)
(* #[local] Hint Resolve sf_ens : typeclass_instances. *)

(* previous attempt at automation *)
(* #[local] Hint Resolve sf_ens : core. *)

Lemma sf_ens_ : forall H,
  shift_free (ens_ H).
Proof.
  unfold shift_free, not. intros.
  inverts H0. destr H7.
  false.
Qed.

Instance ShiftFreeEns : forall Q,
  ShiftFree (ens Q).
Proof.
  intros. constructor. apply sf_ens.
Qed.

Instance ShiftFreeEnsVoid : forall H,
  ShiftFree (ens_ H).
Proof.
  intros. constructor. apply sf_ens_.
Qed.

Lemma sf_defun : forall x uf,
  shift_free (defun x uf).
Proof.
  unfold shift_free, not. intros.
  inverts H as H.
Qed.

Instance ShiftFreeDefun : forall x uf,
  ShiftFree (defun x uf).
Proof.
  intros. constructor. apply sf_defun.
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
  inverts H1 as H2.
  specializes H2 empty_heap h1 ___.
  hintro.
  assumption.
Qed.

Lemma sf_rs_val : forall f,
  shift_free f ->
  shift_free (rs f).
Proof.
  unfold shift_free, not; intros.
  inverts H0 as H0. destr H0.
  applys~ H H0.
Qed.

Lemma sf_rs : forall f,
  shift_free (rs f).
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

Instance ShiftFreeRs : forall f,
  ShiftFree (rs f).
Proof.
  intros.
  constructor. apply* sf_rs.
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

Instance ShiftFreeSeq : forall f1 f2,
  ShiftFree f1 ->
  ShiftFree f2 ->
  ShiftFree (f1;; f2).
Proof.
  intros.
  inverts H as H.
  inverts H0 as H0.
  constructor. apply* sf_seq.
Qed.

Lemma sf_bind : forall f fk,
  shift_free f ->
  (forall v, shift_free (fk v)) ->
  shift_free (bind f fk).
Proof.
  unfold shift_free, not; intros.
  inverts H1.
  - false H0 H10.
  - false H H7.
Qed.

Instance ShiftFreeBind : forall f fk,
  ShiftFree f ->
  (forall v, ShiftFree (fk v)) ->
  ShiftFree (bind f fk).
Proof.
  intros.
  inverts H.
  constructor. apply* sf_bind.
  intros. specializes H0 v. inverts* H0.
Qed.

(* Definition returns_value (f:flow) : Prop :=
  forall s1 s2 h1 h2 v, satisfies s1 s2 h1 h2 (norm v) f.

Lemma sf_seq_inv : forall f1 f2,
  shift_free (f1;; f2) ->
  shift_free f1 /\ (returns_value f1 -> shift_free f2).
Proof.
  unfold shift_free, not. intros.
  split; intros.
  { eapply H.
    eapply s_seq_sh.
    exact H0. }
  { unfold returns_value in H0.
  (* destr H0. *)
    eapply H.
    eapply s_seq.
    2: eassumption.
    apply H0.

    }
Qed. *)

Lemma sf_fex : forall A (p:A->flow),
  (forall b, shift_free (p b)) ->
  shift_free (@fex A p).
Proof.
  unfold shift_free, not. intros.
  inverts H0 as H0. destr H0.
  eapply H.
  exact H1.
Qed.

Lemma sf_fall : forall A (p:A->flow) b,
  shift_free (p b) ->
  shift_free (@fall A p).
Proof.
  unfold shift_free, not. intros.
  inverts H0 as H0. destr H0.
  specializes H0 b.
  eapply H.
  eassumption.
Qed.

Lemma sf_seq_inv : forall f1 f2,
  shift_free (f1;; f2) ->
  shift_free f1 /\ shift_free f2.
Proof.
  unfold shift_free, not. intros.
  split; intros.
  { eapply H.
    apply s_bind_sh.
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
  apply s_bind_sh.
  eassumption.
Qed.

Ltac shiftfree :=
  lazymatch goal with
  | |- shift_free (rs _) => apply sf_rs
  | |- shift_free (defun _ _) => apply sf_defun
  | |- shift_free (ens _) => apply sf_ens
  (* | |- shift_free (req _ _) => apply sf_req *)
  | |- shift_free (ens_ _) => unfold ens_; apply sf_ens
  | |- shift_free (_ ;; _) => apply sf_seq; shiftfree
  | |- shift_free (bind _ _) => apply sf_bind; shiftfree
  | |- shift_free (fex _) => apply sf_fex; intros; shiftfree
  | _ => auto
  end.

(* Immediately dispatch goals where we have an assumption that
  a shift-free thing produces a shift *)
Ltac no_shift :=
  lazymatch goal with
  | H: satisfies _ _ _ _ (shft _ _) (ens _) |- _ =>
    apply sf_ens in H; false
  | H: satisfies _ _ _ _ (shft _ _) (ens_ _) |- _ =>
    unfold ens_ in H; apply sf_ens in H; false
  | H: satisfies _ _ _ _ (shft _ _) (rs _ _) |- _ =>
    apply sf_rs in H; false
  | H: satisfies _ _ _ _ (shft _ _) (defun _ _) |- _ =>
    apply sf_defun in H; false
  | _ => idtac
  end.

Ltac vacuity ::= false; no_shift.

(* knowing that there is one norm execution does not mean
  that there are no shift executions *)
Lemma norm_sf_attempt : forall s1 s2 h1 h2 v f,
  satisfies s1 s2 h1 h2 (norm v) f ->
  shift_free f.
Proof.
  intros * Hf.
  unfold shift_free. intros * H.
Abort.

Definition det f := forall s1 s2 h1 h2 R1 R2,
  satisfies s1 s2 h1 h2 R1 f ->
  satisfies s1 s2 h1 h2 R2 f ->
  R1 = R2.

(* if all executions end in norm and f is deterministic,
  then f is shift-free. *)
Lemma norm_sf : forall f,
  det f ->
  (forall s1 s2 h1 h2, exists v, satisfies s1 s2 h1 h2 (norm v) f) ->
  shift_free f.
Proof.
  intros * Hd Hf.
  unfold shift_free. intros * H.
  specializes Hf s1 s2 h1 h2.
  destr Hf.
  specializes Hd H H0.
  discriminate.
Qed.


(* End ShiftFreedom. *)

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
  Instance Proper_ent : forall env, Proper
    (flip (entails_sequent env env env env) ====> entails_sequent env env env env ====> impl)
    (entails_sequent env env env env).
  Proof.
    unfold entails_sequent, Proper, respectful, impl, flip. intros.
    specializes H H2.
    specializes H1 H.
    specializes H0 H1.
    auto.
  Qed.

  #[global]
  Instance Proper_entails_under : forall env, Proper
    (flip (entails_under env) ====> entails_under env ====> impl)
    (entails_under env).
  Proof.
    unfold entails_under, Proper, respectful, impl, flip.
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

  #[global]
  Instance Proper_bind_left : Proper (entails ====> eq ====> entails) bind.
  Proof.
    (* unfold Proper, cont_eq, entails, respectful. intros. *)
    unfold Proper, entails, respectful. intros.
    inverts H1.
    {
      (* specializes H0 v. *)
      applys* s_bind.
      rewrite* <- H0. }
    { specializes H H8.
      applys_eq s_bind_sh.
      2: { applys H. }
      (* f_equal. *)
      congruence.
      (* applys fun_ext_dep. *)
      (* eauto. *)
      }
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
    {
      (* apply equal_f with (x := arbitrary) in H0. subst. *)

      (* injects H. *)

    (* lets ?: cont_inj H0. *)
    (* subst; clear H; cont_eq *)
    (* cont_inj H0. subst; clear H; cont_eq *)
      (* cont_eq. *)
      applys* s_bind. }
    { applys s_bind_sh.
      eauto. }
  Qed.

  #[global]
  Instance Proper_seq_fail : Proper (entails ====> entails ====> entails) seq.
  Proof.
    unfold Proper, entails, respectful.
    intros.
    inverts H1 as H1; destr H1.
    { apply* s_bind. }
    { apply H in H1.
      pose proof s_bind_sh.
      specializes H2 H1.
      applys_eq H2. clear H2.
      f_equal.
      (* the proof is stuck here because we want y0 and x0 to be related by
         something weaker than equality (entailment), but the relation
         between results in the semantics is equality *)
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
    { applys* s_bind. }
    { eapply s_bind_sh. jauto. }
  Qed.

  #[global]
  Instance Proper_bind_entails_under_left : forall env,
    Proper (entails_under env ====> eq ====> entails_under env) bind.
  Proof.
    unfold Proper, entails_under, respectful. intros.
    inverts H1.
    { applys* s_bind.
      rewrite* <- H0. }
    { specializes H H8.
      applys_eq s_bind_sh.
      2: { applys H. }
      congruence. }
  Qed.

  #[global]
  Instance Proper_rs : Proper (entails ====> entails) rs.
  Proof.
    unfold Proper, entails, respectful.
    intros. subst.
    inverts H0 as H0; destr H0.
    { eapply s_rs_sh.
      eauto.
      eassumption. }
    { apply s_rs_val. eauto. }
  Qed.

  #[global]
  Instance Proper_bientails_rs : Proper
    (bientails ====> bientails)
    rs.
  Proof.
    unfold bientails, Proper, respectful, impl.
    split; subst; intros.
    { inverts H0 as H0.
      { eapply s_rs_sh. apply H. exact H0. exact H7. }
      { apply H in H0. apply s_rs_val. assumption. } }
    { inverts H0 as H0.
      { eapply s_rs_sh. apply H. eauto. eauto. }
      { apply H in H0. apply s_rs_val. assumption. } }
  Qed.

  #[global]
  Instance Proper_rs_under : forall s,
    Proper (entails_under s ====> entails_under s) rs.
  Proof.
    unfold Proper, entails_under, respectful.
    intros. subst.
    inverts H0 as H0; destr H0.
    { eapply s_rs_sh.
      apply H. eauto. eauto. }
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
  Instance entails_ent : forall env,
    Proper (flip entails ====> entails ====> impl)
      (entails_sequent env env env env).
  Proof.
    unfold Proper, respectful, entails_sequent, entails, flip, impl.
    intros.
    specializes H H2.
    specializes H1 H.
    destr H1. exs.
    eauto.
  Qed.

  #[global]
  Instance entails_under_ent : forall s1 s2 s3,
    Proper (flip (entails_under s1) ====> (entails_under s1) ====> impl) (entails_sequent s1 s2 s1 s3).
  Proof.
    unfold Proper, respectful, entails_sequent, flip, impl.
    (* unfold Proper, respectful, entails_sequent, entails_under, flip, impl. *)
    intros.
    specializes H H2.
    specializes H1 H.
    specializes H0 H1.
    eauto.
  Qed.

  Example rewrite : forall s1 s2 s3 (f:var) v,
    entails_under s1 (unk f v) (Fmap.read s1 f v) ->
    entails_sequent s1 s2 s1 s3 (unk f v) empty.
  Proof.
    intros.
    rewrite H.
  Abort.

  (* #[global]
  Instance entails_entails_under : forall env,
    Proper (flip entails ====> entails ====> impl) (entails_under env).
  Proof.
    unfold Proper, respectful, entails_under, entails, flip, impl.
    intros.
    eauto.
  Qed. *)

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
  Instance Proper_bind_bi_left : Proper (bientails ====> eq ====> bientails) bind.
  Proof.
    unfold Proper, bientails, respectful.
    intros.
    split; intros.

    { pose proof Proper_bind_left.
      unfold Proper, entails, respectful in H2.
      applys H2 H1; auto.
      intros.
      apply~ H. }

    { pose proof Proper_bind_left.
      unfold Proper, entails, respectful in H2.
      applys H2 H1; auto.
      intros.
      apply~ H. }
  Qed.

  Example rewrite :
    bientails (rs (ens_ \[1 = 1])) (rs (ens_ \[2 = 2])) ->
    entails (rs (bind (rs (ens_ \[1 = 1])) (fun v => empty))) empty.
  Proof.
    intros H.
    rewrite H.
  Abort.

  #[global]
  Instance Proper_req_entails : Proper (eq ====> entails ====> entails) req.
  Proof.
    unfold Proper, entails, respectful, flip.
    intros.
    constructor. intros.
    rewrite <- H in H2.
    inverts H1 as H5.
    specializes H5 H3 ___.
  Qed.

  #[global]
  Instance Proper_req_entails_under : forall env,
    Proper (eq ====> entails_under env ====> entails_under env) req.
  Proof.
    unfold Proper, entails_under, respectful, flip.
    intros.
    constructor. intros.
    rewrite <- H in H2.
    inverts H1 as H5.
    specializes H5 H3 ___.
  Qed.

  #[global]
  Instance Proper_req_bi : Proper (eq ====> bientails ====> bientails) req.
  Proof.
    unfold Proper, bientails, respectful.
    intros.
    split; intros H1.
    { constructor. intros hp hr H2 H3 H4.
      rewrite <- H in H2.
      inverts H1 as H5.
      specializes H5 H3 ___.
      apply H0. assumption. }
    { constructor. intros hp hr H2 H3 H4.
      rewrite H in H2.
      inverts H1 as H5.
      specializes H5 H3 ___.
      apply H0. assumption. }
  Qed.

  Definition cont_entails fk1 fk2 := forall v, entails (fk1 v) (fk2 v).

  #[global]
  Instance Proper_bind_sf : forall f1,
    ShiftFree f1 ->
    Proper (cont_entails ====> entails) (bind f1).
  Proof.
    unfold Proper, cont_entails, entails, respectful.
    intros.
    inverts H1 as H1; destr H1.
    { apply* s_bind. }
    { apply H in H1. false. }
  Qed.

  #[global]
  Instance Proper_bind_sf2 : forall f1,
    ShiftFree f1 ->
    Proper ((fun fk2 fk3 =>
        forall v env, entails_under env (fk2 v) (fk3 v)) ====>
      (fun f2 f3 => forall env, entails_under env f2 f3)) (bind f1).
  Proof.
    unfold Proper, entails_under, entails, respectful.
    intros.
    inverts H1. 2: { apply H in H8. false. }
    applys* s_bind.
  Qed.

  #[global]
  Instance bind_entails_under_morphism1 f1 :
    Proper (Morphisms.pointwise_relation val eq ====> bientails)
      (@bind f1).
  Proof.
    unfold Proper, respectful, Morphisms.pointwise_relation, bientails. intros.
    iff H0.
    { inverts H0.
      { applys* s_bind. rewrite* H in H9. }
      { applys_eq s_bind_sh. 2: { eassumption. }
        f_equal.
        applys fun_ext_dep.
        eauto. } }
    { inverts H0.
      { applys* s_bind. rewrite* H. }
      { applys_eq s_bind_sh. 2: { eassumption. }
        f_equal.
        applys fun_ext_dep.
        eauto. } }
  Qed.

  #[global]
  Instance bind_entails_under_morphism f1 :
    Proper (Morphisms.pointwise_relation val eq ====> entails)
      (@bind f1).
  Proof.
    unfold Proper, respectful, Morphisms.pointwise_relation, entails.
    intros.
    inverts H0.
    { applys* s_bind. rewrite* H in H9. }
    { applys_eq s_bind_sh. 2: { eassumption. }
      f_equal.
      applys fun_ext_dep.
      eauto. }
  Qed.

  #[global]
  Instance bind_entails_under_morphism_sf f1 :
    ShiftFree f1 ->
    Proper (Morphisms.pointwise_relation val entails ====> entails)
      (@bind f1).
  Proof.
    unfold Proper, respectful, Morphisms.pointwise_relation, entails.
    intros * Hsf **.
    inverts H0.
    2: { destruct Hsf as (Hsf). false Hsf H7. }
    applys* s_bind.
  Qed.

  Example rewrite :
    entails (ens_ \[1 = 1]) (ens_ \[2 = 2]) ->
    entails
      (ens_ \[1 = 1])
      empty.
  Proof.
    intros H.
    rewrite H.
  Abort.

  Example rewrite :
    entails (ens_ \[1 = 1]) (ens_ \[2 = 2]) ->
    entails
      (bind (ens_ \[1 = 1]) (fun v => empty))
      empty.
  Proof.
    intros H.
    rewrite H.
  Abort.

  Example rewrite :
    entails (ens_ \[1 = 1]) (ens_ \[2 = 2]) ->
    entails
      (bind empty (fun v => ens_ \[1 = 1]))
      empty.
  Proof.
    intros H.
    setoid_rewrite H.
  Abort.

  #[global]
  Instance Proper_seq_sf : forall f1,
    (* shift_free f1 -> *)
    ShiftFree f1 ->
    Proper (entails ====> entails) (seq f1).
  Proof.
    unfold Proper, entails, respectful.
    intros.
    inverts H1 as H1; destr H1.
    { apply* s_seq. }
    { apply H in H1. false. }
  Qed.

  #[global]
  Instance Proper_seq_sf1 : forall f1,
    (* shift_free f1 -> *)
    ShiftFree f1 ->
    Proper (bientails ====> bientails) (seq f1).
  Proof.
    unfold Proper, bientails, respectful.
    intros.
    iff H1.
    { inverts H1 as H1. 2: { apply H in H1. false. }
      apply* s_seq.
      rewrite* <- H0. }
    { inverts H1 as H1. 2: { apply H in H1. false. }
      apply* s_seq.
      rewrite* H0. }
  Qed.

  (* this is essentially the same as entails *)
  #[global]
  Instance Proper_seq_sf2 :
  (* forall env f1, *)
  forall f1,
    ShiftFree f1 ->
    (* Proper (entails_under env ====> entails_under env) (seq f1). *)
    Proper ((fun f2 f3 => forall env, entails_under env f2 f3) ====> (fun f2 f3 => forall env, entails_under env f2 f3)) (seq f1).
  Proof.
  (* Check respectful. *)
    unfold Proper, entails_under, respectful.
    (* unfold Proper, entails_under. *)
    intros.
    inverts H1 as H1. 2: { apply H in H1. false. }
    applys s_seq.
    eassumption.

    (* apply* s_seq. *)
    applys_eq H0.
    assumption.

    (* admit.
    applys_eq H9.
    admit. *)
    (* applys_eq H0. *)
    (* admit. *)

    (* apply* H0.  *)
  Qed.

  Definition env_constant f :=
    (* forall s h1 h2 R, satisfies s s h1 h2 R f. *)
    forall s1 s2 h1 h2 R, satisfies s1 s2 h1 h2 R f -> s1 = s2.

  Lemma env_constant_ens : forall Q,
    env_constant (ens Q).
  Proof.
    unfold env_constant. intros.
    inverts H as H. destr H.
    reflexivity.
  Qed.

  Lemma env_constant_seq : forall f1 f2,
    shift_free f1 ->
    env_constant f1 ->
    env_constant f2 ->
    env_constant (f1;; f2).
  Proof.
    unfold env_constant. intros.
    inverts H2 as H2. 2: { apply H in H2. false. }
    specializes H0 H2.
    specializes H1 H10.
    congruence.
  Qed.

  Class EnvConstant f : Prop :=
    { env_constant_pf :
      forall s1 s2 h1 h2 R, satisfies s1 s2 h1 h2 R f -> s1 = s2 }.

  #[global]
  Instance EnvConstantEns : forall Q,
    EnvConstant (ens Q).
  Proof.
    intros. constructor.
    apply env_constant_ens.
  Qed.

  #[global]
  Instance EnvConstantSeq : forall f1 f2,
    ShiftFree f1 ->
    EnvConstant f1 ->
    EnvConstant f2 ->
    EnvConstant (f1;; f2).
  Proof.
    constructor. apply env_constant_seq.
    destruct* H.
    destruct* H0.
    destruct* H1.
  Qed.

  #[global]
  Instance Proper_seq_sf3 : forall env f1,
    ShiftFree f1 ->
    EnvConstant f1 ->
    Proper (entails_under env ====> entails_under env) (seq f1).
  Proof.
    unfold Proper, entails_under, respectful.
    intros.
    inverts H2 as H2. 2: { apply H in H2. false. }
    destruct H0 as [H0]. specializes H0 H2. subst.
    apply* s_seq.
  Qed.

  Example rewrite : forall l,
    entails_under empty_env (ens_ \[1 = 1]) (ens_ \[2 = 2]) ->
    entails_under empty_env
      (rs (bind (req (l~~>vint 1) (ens_ (l~~>vint 1);; ens_ \[1 = 1]))
        (fun _ => empty))) empty.
  Proof.
    intros.
    rewrite H.
  Abort.

End Propriety.

(** * Lemmas about satisfies *)
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

Lemma empty_inv : forall s1 s2 h1 h2 R,
  satisfies s1 s2 h1 h2 R empty ->
  s1 = s2 /\ h1 = h2 /\ R = norm vunit.
Proof.
  unfold empty.
  intros.
  apply ens_void_pure_inv in H.
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

  Example e1_undelimited : exists R,
    satisfies empty_env empty_env empty_heap empty_heap R
      (sh (fun k => ens (fun r2 => \[r2 = vint 1]))).
  Proof.
    intros.
    eexists.
    apply s_sh.
    (* Show Proof. *)
    (* result of continuation can be anything because it's never used *)
  Qed.

  Example e2_reset_value :
    satisfies empty_env empty_env empty_heap empty_heap (norm (vint 1))
      (rs (ens (fun r => \[r = vint 1]))).
  Proof.
    intros.
    apply s_rs_val.
    apply ens_pure_intro.
    reflexivity.
  Qed.

  Example e3_rs_sh_no_k : forall k1, exists s,
    satisfies empty_env s empty_heap empty_heap (norm (vint 1))
      (rs (sh (fun k => ens (fun r => \[r = vint 1])))).
  Proof.
    intros.
    eexists.
    (* the ret of the shift can be anything because the cont is never taken *)
    applys s_rs_sh k1.
    { apply s_sh. }
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
  Example e4_rs_sh_k : forall k1, exists s,
  satisfies empty_env s empty_heap empty_heap (norm (vint 3))
    (rs (sh (fun k => unk k (vint 2));; ens (fun r => \[r = vint (1 + 2)]))).
  Proof.
    intros.
    eexists. (* this is okay because it's an output *)
    applys s_rs_sh k1.
    (* put the ens into the cont *)
    {
      (* show that the body produces a shift *)
      apply s_bind_sh.
      apply s_sh. }
    { apply s_rs_val. (* handle reset *)

      eapply s_unk. resolve_fn_in_env. (* reset body *)
      simpl.
      apply s_rs_val.
      eapply s_bind.
      { apply ens_pure_intro. jauto. }
      { apply ens_pure_intro. jauto. }
    }
  Qed.

  (** [(reset (shift k (fun a -> k a))) 4 ==> 4]
  - The whole thing returns what the application of f/k returns
  - The result of the shift is 4 due to the identity k
  - The result of the reset is a function; 4 is the result of an inner reset that appears in the course of reduction *)
  Example e5_shift_k : forall k1 xf, k1 <> xf -> exists s,
    satisfies empty_env s empty_heap empty_heap (norm (vint 4))
      (rs (sh (fun k => defun xf (unk k);;
        ens (fun r => \[r = vfptr xf])));; unk xf (vint 4)).
  Proof.
    intros.
    eexists.
    eapply s_bind.
    { (* show that reset produces a function *)
      applys s_rs_sh k1.
      (* handle the shift *)
      apply s_sh.
      (* show how the shift body goes through the reset to produce the function *)
      { apply s_rs_val.
        eapply s_bind.
        apply s_defun.
        (* { apply not_indom_update.
          apply not_indom_empty.
          symmetry. assumption. } *)
        reflexivity.
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
      apply~ ens_pure_intro.
    }
  Qed.

  (** [(reset 1 + (shift k (fun a -> k a))) 4 ==> 5]
  - res of shift = arg of k = 4
  - res of reset = res of shift body = fptr
  - final res is that of the inner reset, which doesn't occur syntacically in the code as it is produced by the "handling" of the shift. *)
  Example e6_shift_k : forall k1 xf, k1 <> xf -> exists s,
    satisfies empty_env s empty_heap empty_heap (norm (vint 5))
      (rs (bind (sh (fun k => defun xf (unk k);; ens (fun r => \[r = vfptr xf])))
              (fun sr => ens (fun r => \[r = vplus (vint 1) sr])));;
        unk xf (vint 4)).
  Proof.
    intros.
    eexists.
    eapply s_bind.
    { (* reset *)
      (* the shift is still "handled", but produces a lambda without
        applying the continuation *)
      applys s_rs_sh k1.
      { apply s_bind_sh. (* this moves the ens into the continuation *)
        apply s_sh. }
      { apply s_rs_val.
        eapply s_seq.
        apply* s_defun.
        apply* ens_pure_intro. }
    }
    { (* app *)
      eapply s_unk. resolve_fn_in_env. simpl.
      eapply s_unk.
      (* TODO resolve should solve this *)
      { unfold Fmap.update.
        rewrite Fmap.read_union_r.
        rewrite Fmap.read_union_l.
        apply Fmap.read_single.
        apply Fmap.indom_single.
        apply* fmap_not_indom_of_neq. }
      simpl.
      apply s_rs_val.
      eapply s_bind. apply* ens_pure_intro.
      simpl.
      apply* ens_pure_intro.
    }
  Qed.

End Examples.

(* Given a [satisfies ... (shs ... k)] hypothesis,
  produces [satisfies ... (shc ... k)] and an assumption
  that k is shift-free *)
(* Ltac elim_shs H :=
  lazymatch type of H with
  | satisfies _ _ _ _ _ (shs _ _ _ _) =>
    inverts H as H; no_shift; destr H;
    apply ens_void_pure_inv in H; destr H;
    lazymatch goal with
    | H: norm _ = norm _ |- _ => injects H
    end;
    subst
  | _ => fail
  end. *)

(* Given a [satisfies ... (shs ... k)] goal,
  we have to prove [k] is shift-free before we can reduce
  it into a [satisfies ... (shc ... k)] goal. *)
(* Ltac intro_shs :=
  lazymatch goal with
  | |- satisfies _ _ _ _ _ (shs _ _ _ _) =>
    eapply s_seq; [ apply ens_void_pure_intro | ]
  | _ => fail
  end. *)

(** * New reduction rules *)

Lemma red_init : forall fb,
  entails (sh fb) (shc fb (fun v => ens (fun r => \[r = v]))).
Proof.
  unfold sh.
  intros. applys entails_refl.
Qed.

Lemma red_extend : forall fb fk fk1,
  entails (bind (shc fb fk) fk1)
    (shc fb (fun v => bind (fk v) fk1)).
Proof.
  unfold entails. intros.
  inverts H.
  inverts H7.
  inverts H6.
  applys s_shc.
Qed.

(* RNorm1 is seq_assoc *)
(* RNorm2 is ?? *)

(* aka red_skip *)
Lemma red_rs_float1 : forall f1 f2,
  shift_free f1 ->
  entails (rs (f1;; f2)) (f1;; rs f2).
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
      exact H8. eassumption. }
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

(* TODO <-? *)
Lemma red_rs_float2 : forall f1 f2,
  entails (rs (disj f1 f2)) (disj (rs f1) (rs f2)).
Proof.
  introv H.
  unfold entails. intros.
  inverts H.
  { inverts H1.
    { applys s_disj_l.
      applys* s_rs_sh. }
    { applys s_disj_r.
      applys* s_rs_sh. } }
  { inverts H6.
    { applys s_disj_l. applys* s_rs_val. }
    { applys s_disj_r. applys* s_rs_val. } }
Qed.


Lemma red_rs_elim : forall f,
  shift_free f ->
  bientails (rs f) f.
Proof.
  introv Hsf. iff H.
  { inverts H.
    { false Hsf H1. }
    { assumption. } }
  { destruct R.
    2: { false Hsf H. }
    applys* s_rs_val. }
Qed.

(* this one is slightly easier to use *)
Lemma red_rs_ens : forall Q,
  bientails (rs (ens Q)) (ens Q).
Proof.
  iff H.
  { applys red_rs_elim. shiftfree. assumption. }
  { applys red_rs_elim. shiftfree. assumption. }
Qed.

Lemma red_rs_sh_elim : forall fb fk,
  entails (rs (shc fb fk))
    (∃ k, defun k (fun v => rs (fk v));; rs (fb k)).
Proof.
  unfold entails. intros.
  inverts H. 2: { false_invert H6. }
  inverts H1.
  inverts H7.
  { (* body has shift *)
    applys s_fex. exists k.
    applys s_seq. { applys s_defun. reflexivity. }
    applys* s_rs_sh. }
  { (* body has no shift *)
    applys s_fex. exists k.
    applys s_seq. { applys s_defun. reflexivity. }
    applys s_rs_val.
    applys H5. }
Qed.

(** * Reduction rules *)
Lemma red_normal : forall f,
  shift_free f ->
  entails (rs f) f.
Proof.
  introv Hsf.
  unfold entails. intros.
  inverts H as H; destr H.
  { (* this case cannot be as f is shift-free *)
    apply Hsf in H.
    false. }
  { assumption. }
Qed.

Lemma red_skip : forall f1 f2,
    shift_free f1 ->
    entails (rs (f1;; f2)) (f1;; rs f2).
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
      exact H8. eassumption. }
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

Lemma red_skip_conv : forall f1 f2,
    shift_free f1 ->
    entails (f1;; rs f2) (rs (f1;; f2)).
Proof.
  introv Hsf. unfold entails. intros.

  inverts H as H. 2: { apply Hsf in H. false. }
  inverts H7 as H7.
  
  { eapply s_rs_sh.
    apply* s_seq.
    eassumption. }
  { apply s_rs_val.
    apply* s_seq. }
Qed.

Lemma red_skip2 : forall f1 f2,
    shift_free f1 ->
    bientails (rs (f1;; f2)) (f1;; rs f2).
Proof.
  introv Hsf.
  unfold bientails. iff H.
  { apply* red_skip. }

  inverts H as H. 2: { apply Hsf in H. false. }
  inverts H7 as H7.
  
  { eapply s_rs_sh.
    apply* s_seq.
    eassumption. }
  { apply s_rs_val.
    apply* s_seq. }
Qed.

(* Lemma red_init : forall x b r,
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
Qed. *)

(* Lemma red_extend : forall f2 x b fk v,
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
Qed. *)

(* Lemma red_acc : forall f2 x v r fk fb,
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
    assumption.
  }
Qed. *)

(* Lemma red_shift_elim : forall x v r fk fb,
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
  apply s_defun.
  (* assumption. *)
  reflexivity.
  applys_eq H7.
Qed. *)

(* try to prove the continuation is shift-free *)
(* Lemma red_shift_elim1 : forall x v r fk fb a1 r1,
  entails (rs (shs x fb v (fun r2 => rs fk r2)) r)
    (defun x (fun a r =>
      rs (ens_ \[v = a];; fk) r);; ens_ \[shift_free (unk x a1 r1)];; rs fb r).
Proof.
  unfold entails. intros.
  inverts H as H. 2: { inverts H as H. destr H. vacuous. }
  elim_shs H. clear H0.
  inverts H8 as H8.
  cont_eq.
  eapply s_seq.
  apply s_defun.
  (* assumption. *)
  reflexivity.
  applys_eq H7.
  (* eapply s_seq. *)
Abort. *)

(** * Entailment, entailment sequent, normalization *)
Lemma norm_reassoc : forall H f1 f2,
  (* shift_free f1 -> *)
  entails (req H f1;; f2) (req H (f1;; f2)).
Proof.
  unfold entails.
  intros.
  inverts H0 as H0.
  2: { (* handle shift. it may be possible to relax this *)
    apply s_req. intros.
    inverts H0 as H4.
    specializes H4 H1 H2 H3.
    apply s_bind_sh.
    assumption.
    (* apply H0 in H1. *)
    (* false. *)
  }

  (* destr H1. *)

  (* find out about req *)
  constructor. intros hp hr. intros.

  (* prove the req *)
  inverts H0 as H4.
  specializes H4 hp hr H2 ___.
  applys* s_seq h3.
Qed.

(* Lemma norm_discard : forall f1 f2 x,
  entails f1 f2 ->
  entails (discard f1 x) (discard f2 x).
Proof.
  unfold entails. intros.
  inverts H0 as H0.
  apply s_discard.
  eauto.
  reflexivity.
Qed. *)

Lemma norm_defun : forall x uf a,
  entails (defun x uf;; unk x a) (defun x uf;; uf a).
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

Lemma ent_seq_defun : forall s1 s2 s3 x uf f2 f1,
  entails_sequent (Fmap.update s1 x uf) s2 s1 s3 f1 f2 ->
  entails_sequent s1 s2 s1 s3 (defun x uf;; f1) f2.
Proof.
  unfold entails_sequent. intros.
  inverts H0. 2: { false sf_defun H7. }
  inverts H8.
  specializes H H9. destr H.
  exs. eassumption.
Qed.

Lemma entails_under_seq_defun_both : forall s x uf f2 f1,
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

Lemma entails_under_seq_defun_idem : forall s x uf f1,
  Fmap.indom s x ->
  Fmap.read s x = uf ->
  entails_under s (defun x uf;; f1) f1.
Proof.
  unfold entails_under. intros.
  inverts H1. 2: { vacuous. }
  inverts H9.
  lets: update_idem H H0.
  rewrite H1 in H10.
  assumption.
Qed.

Lemma ens_inv : forall s1 s2 h1 h2 R Q,
  satisfies s1 s2 h1 h2 R (ens Q) ->
  s1 = s2.
Proof.
  intros.
  inverts H as H. destr H.
  reflexivity.
Qed.

Lemma unk_inv : forall s1 s2 h1 h2 R x a uf,
  Fmap.read s1 x = uf ->
  satisfies s1 s2 h1 h2 R (unk x a) ->
  satisfies s1 s2 h1 h2 R (uf a).
Proof.
  intros.
  inverts H0 as H0.
  rewrite H in H0.
  assumption.
Qed.

Lemma entails_under_unk : forall s (x:var) a uf,
  Fmap.read s x = uf ->
  entails_under s (unk x a) (uf a).
Proof.
  unfold entails_under. intros.
  eapply unk_inv.
  exact H.
  assumption.
Qed.

Lemma norm_rs_rs : forall f r,
  entails (rs (rs f)) (rs f).
Proof.
  unfold entails. intros.
  inverts H as H.
  false sf_rs H.
  assumption.
Qed.

Lemma seq_assoc_unrestricted : forall s1 s2 h1 h2 R f1 f2 f3,
  satisfies s1 s2 h1 h2 R (f1;; f2;; f3) <->
  satisfies s1 s2 h1 h2 R ((f1;; f2);; f3).
Proof.
  iff Hs.
  { inverts Hs.
    { inverts H7.
      { applys s_seq H9. applys* s_seq. }
      { applys s_bind_sh. applys* s_seq. } }
    {
      (* at this point we don't know which to pick *)
Abort.

Lemma seq_assoc : forall s1 s2 h1 h2 R f1 f2 f3,
  shift_free f1 ->
  shift_free f2 ->
  satisfies s1 s2 h1 h2 R (f1;; (f2;; f3)) <->
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
    { inverts H1 as H1. destr H1.
      apply H0 in H9. false.
      apply H in H1. false. } }
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
  inverts H as H. 2: { no_shift. }
  inverts H as H. destr H. hinv H. injects H0. subst.
  rew_fmap *.
Qed.

Lemma norm_ens_true : forall f,
  entails (ens_ \[True];; f) f.
Proof.
  unfold entails. intros.
  inverts H as H. 2: { no_shift. }
  inverts H as H. destr H. hinv H. hinv H. hinv H2. injects H0. subst.
  rew_fmap *.
Qed.

Lemma norm_ens_eq : forall f (a:val),
  entails (ens_ \[a = a];; f) f.
Proof.
  unfold entails. intros.
  inverts H as H. 2: { no_shift. }
  inverts H as H. destr H. hinv H. hinv H. hinv H2. injects H0. subst.
  rew_fmap *.
Qed.

Lemma ent_seq_ens_pure_l : forall s1 s2 s3 s4 f f1 (P:val->Prop),
  (forall r, P r -> entails_sequent s1 s2 s3 s4 f1 f) ->
  entails_sequent s1 s2 s3 s4 (ens (fun r => \[P r]);; f1) f.
Proof.
  unfold entails_sequent. intros.
  inverts H0 as H0; no_shift. destr H0.
  inverts H0 as H0. destr H0.
  hinv H0. injects H1.
  subst. rew_fmap *.
Qed.

Lemma ent_seq_ens_void_pure_l : forall s1 s2 s3 s4 f f1 P,
  (P -> entails_sequent s1 s2 s3 s4 f1 f) ->
  entails_sequent s1 s2 s3 s4 (ens_ \[P];; f1) f.
Proof.
  unfold entails_sequent. intros.
  inverts H0 as H0; no_shift. destr H0.
  inverts H0 as H0. destr H0.
  hinv H0. hinv H3. hinv H0. subst. injects H1.
  rew_fmap *.
Qed.

Lemma norm_seq_ens_req : forall f f1 H,
  entails (ens_ H;; f1) f ->
  entails f1 (req H f).
Proof.
  unfold entails. intros.
  apply s_req. intros.
  apply H0.
  eapply s_seq.
  apply s_ens. exists vunit hp.
  splits*.
  hintro; jauto.
  subst. assumption.
Qed.

(* Lemma ent_seq_ens_dep_l : forall env f f1 p,
  (forall r1, p r1 -> entails_sequent env env f1 f) ->
  entails_sequent env env (ens (fun r => \[p r]);; f1) f.
Proof.
  unfold entails_sequent. intros.
  inverts H0 as H0; no_shift. destr H0.
  inverts H0 as H0. destr H0.
  hinv H0. injects H1. subst.
  rew_fmap *.
Qed. *)

Lemma norm_ens_ens_void_l : forall H Q,
  bientails (ens_ H;; ens Q) (ens (Q \*+ H)).
Proof.
  unfold entails.
  iff H0.
  { inverts H0 as H0. 2: { no_shift. }
    inverts H0 as H0.
    destr H0. hinv H0. hinv H0. injects H1.
    inverts H8 as H8. destr H8.
    applys s_ens.
    exists v (h4 \u x0).
    splits*.
    subst. rew_fmap *.
    apply* hstar_intro. }
  { inverts H0 as H0. destr H0. hinv H0.
    eapply s_seq.
    eapply s_ens.
    exists vunit.
    exists x0.
    splits*.
    { hintro. jauto. }
    { constructor. exists v x. jauto. } }
Qed.

Lemma satisfies_ens_ens_void_split : forall H1 H2 s1 s2 h1 h2 R,
  satisfies s1 s2 h1 h2 R (ens_ (H1 \* H2)) ->
  satisfies s1 s2 h1 h2 R (ens_ H1;; ens_ H2).
Proof.
  intros.
  inverts H as H. destruct H as (v&h3&H3&H4&H5&H6).
  rewrite hstar_hpure_l in H4. destruct H4 as (H4&H7).
  (* h3 is the heap that H1 and H2 together add *)
  (* find the intermediate heap *)
  apply hstar_inv in H7. destruct H7 as (h0&h4&H8&H9&H10&H11).
  (* H1 h0, H2 h4 *)
  applys s_seq.
  { constructor. exists vunit. exists h0. intuition. rewrite hstar_hpure_l. intuition. }
  { constructor. exists v. exists h4. intuition. rewrite hstar_hpure_l. intuition. }
Qed.

Lemma satisfies_ens_ens_void_combine : forall H1 H2 s1 s2 h1 h2 R,
  satisfies s1 s2 h1 h2 R (ens_ H1;; ens_ H2) ->
  satisfies s1 s2 h1 h2 R (ens_ (H1 \* H2)).
Proof.
  intros.
  inverts H as H; no_shift. destr H.
  (* give up on careful reasoning *)
  inverts H as H. destr H.
  inverts H9 as H9. destr H9.
  hinv H. hinv H. hinv H6. hinv H6.
  applys_eq s_ens_. injects H0. subst. reflexivity.
  exists (h0 \u h4).
  splits*.
  subst.
  hintro; jauto.
  rew_fmap *.
  rew_fmap *.
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
  inverts H as H14.
  forwards: (H14 hH1 (hr \u hH2) H0).
  fmap_eq.
  fmap_disjoint.

  inverts H as H16.
  specializes H16 hr H5.
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

  inverts H as H14.
  specialize (H14 (hH1 \u hH2) hr ltac:(apply hstar_intro; auto)).
  forwards: H14.
  fmap_eq.
  fmap_disjoint.
  auto.
Qed.

Lemma norm_req_req : forall H1 H2 f,
  bientails (req (H1 \* H2) f) (req H1 (req H2 f)).
Proof.
  intros.
  split.
  - apply norm_req_sep_split.
  - apply norm_req_sep_combine.
Qed.

Lemma norm_rs_req : forall H f,
  entails (rs (req H f)) (req H (rs f)).
Proof.
  unfold entails. intros.
  apply s_req. intros.
  inverts H0 as H0.
  { eapply s_rs_sh.
    inverts H0 as H11. specializes H11 H1 H2 H3.
    eassumption. }
  { inverts H0 as H10. specializes H10 H1 H2 H3.
    apply* s_rs_val. }
Qed.

Lemma norm_rs_seq_ens : forall Q f,
  entails (rs (ens Q;; f)) (ens Q;; (rs f)).
Proof.
  unfold entails. intros.
  apply red_skip.
  apply sf_ens.
  assumption.
Qed.

Lemma norm_rs_seq_ens_void : forall H f,
  entails (rs (ens_ H;; f)) (ens_ H;; (rs f)).
Proof.
  unfold entails. intros.
  apply red_skip.
  apply sf_ens.
  assumption.
Qed.

(** * Biabduction *)

Inductive biab : hprop -> hprop -> hprop -> hprop -> Prop :=

  | b_trivial : forall H,
    biab \[] H H \[]

  | b_base_empty : forall Hf,
    biab \[] Hf \[] Hf

  | b_pts_match : forall a b H1 H2 Ha Hf l,
    biab Ha H1 H2 Hf ->
    biab (\[a=b] \* Ha) (l~~>a \* H1) (l~~>b \* H2) Hf

  | b_any_match : forall H H1 H2 Ha Hf,
    biab Ha H1 H2 Hf ->
    biab Ha (H \* H1) (H \* H2) Hf

  | b_pts_diff : forall a b H1 H2 Ha Hf l1 l2,
    (* l1 <> l2 -> *)
    biab Ha H1 H2 Hf ->
    biab (l2~~>b \* Ha) (l1~~>a \* H1) (l2~~>b \* H2) (l1~~>a \* Hf).

Lemma b_pts_single : forall l a b,
  biab \[a=b] (l~~>a) (l~~>b) \[].
Proof.
  intros.
  rewrite <- (hstar_hempty_r (l~~>a)).
  rewrite <- (hstar_hempty_r (l~~>b)).
  applys_eq b_pts_match.
  instantiate (1 := \[]).
  xsimpl.
  intuition.
  intuition.
  apply b_base_empty.
Qed.

Lemma ens_reduce_frame : forall s1 s2 h1 h hf R H,
  H h ->
  Fmap.disjoint h (hf \u h1) ->
  satisfies s1 s2 (hf \u h1) (hf \u h1 \u h) R (ens_ H) ->
  satisfies s1 s2 h1 (h1 \u h) R (ens_ H).
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

Lemma transpose_pts_diff : forall Ha H1 H2 Hf f (x y:loc) (a b:val),
  entails (ens_ H1;; req H2 f) (req Ha (ens_ Hf;; f)) ->
  entails
    (ens_ (x ~~> a \* H1);; req (y ~~> b \* H2) f)
    (req (y ~~> b \* Ha) (ens_ (x ~~> a \* Hf);; f)).
Proof.
  (* the idea of this proof is to demonstrate that we can commute adding x~~>a and removing y~~>b, by showing that: we can start from a heap without x~~>a (using the lemma ens_reduce_frame), perform the operations, and arrive at the same result. *)

  unfold entails. intros.
  inverts H0 as H0; no_shift.

  (* extract everything we can first. start with x->a *)
  rewrite norm_ens_ens_void in H0.
  inverts H0 as H0.
  inverts H0 as H0. destr H0.
  hinv H0. hinv H0.

  (* and y->b and Ha *)
  rewrite norm_req_req.
  apply s_req. intros.
  apply s_req. intros.

  (* now, start supplying stuff. x->a is easy *)
  rewrite norm_ens_ens_void.
  rewrite <- norm_seq_assoc; shiftfree.
  applys s_seq (hr0 \u x1) vunit.
  apply s_ens. exists vunit x1. splits*. hintro. jauto.

  (* supply y->b. to do this, we need to find h3-h(y->b).
    h3 = h(H1) + h0
       = h(H1) + h(x->a) + h1
       = h(H1) + h(x->a) + hr + h(y->b)

    h3 - h(y->b) = h(H1) + h(x->a) + hr
  *)
  pose proof H11.

  inverts H11 as H11. destr H11. hinv H11. hinv H11. (* find out h(H1) *)
  rewrite norm_req_req in H10.
  inverts H10 as H32. specializes H32 hp (x1 \u hr \u x3) H12.
  forward H32 by fmap_eq. forward H32 by fmap_disjoint.

  (* now we are trying to supply the premise of H. to do this
    we need to remove h(y->2) from both sides of H10. *)
  (* subst. rew_fmap *. *)
  subst h0 h3 h1 h5. lets: ens_reduce_frame (hr \u h4) x3 hp H21.
  forward H4 by fmap_disjoint.
  specializes H4. applys_eq H18. fmap_eq. fmap_eq.
  clear H18.

  (* finally, we can use H. build a seq to do that *)
  lets H13: s_seq H4. specializes H13. applys_eq H32. fmap_eq. clear H4 H32.

  specializes H H13. clear H13.

  (* Ha is in the way, but otherwise we are done *)
  subst. rew_fmap *.
  inverts H as H13.
  specializes H13 hp0 H15.
Qed.

Lemma ens_req_inv : forall s1 s2 h1 h2 R H f,
  satisfies s1 s2 h1 h2 R (ens_ H;; req H f) ->
  satisfies s1 s2 h1 h2 R f.
Proof.
  intros.
  inverts H0 as H0; no_shift.
  inverts H0 as H0. destr H0. hinv H0. hinv H0.
  inverts H8 as H15. specializes H15 H3.
  subst. rew_fmap *.
Qed.

Lemma req_empty_inv : forall s1 s2 h1 h2 R f,
  satisfies s1 s2 h1 h2 R (req \[] f) ->
  satisfies s1 s2 h1 h2 R f.
Proof.
  intros.
  inverts H as H6. specializes H6 empty_heap h1 ___.
  apply hempty_intro.
Qed.

Lemma req_empty_intro : forall s1 s2 h1 h2 R f,
  satisfies s1 s2 h1 h2 R f ->
  satisfies s1 s2 h1 h2 R (req \[] f).
Proof.
  intros.
  apply s_req. intros.
  hinv H0.
  subst. rew_fmap *.
Qed.

Lemma norm_seq_req_emp : forall f,
  bientails (req \[] f) f.
Proof.
  unfold entails. split; intros.
  { apply req_empty_inv in H. assumption. }
  { apply req_empty_intro. assumption. }
Qed.

Lemma ens_empty_intro : forall s1 h1 r,
  satisfies s1 s1 h1 h1 (norm r) (ens (fun r => \[])).
Proof.
  intros.
  apply s_ens.
  exists r empty_heap.
  intuition fmap_eq.
  constructor.
Qed.

Lemma ens_void_empty_intro : forall s1 h1,
  satisfies s1 s1 h1 h1 (norm vunit) (ens_ \[]).
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

Lemma satisfies_ens_void : forall H1 H2 s1 s2 h1 h2 R,
  H1 ==> H2 ->
  satisfies s1 s2 h1 h2 R (ens_ H1) ->
  satisfies s1 s2 h1 h2 R (ens_ H2).
Proof.
  intros.
  inverts H0 as H3. destruct H3 as (v&h3&?&?&?&?).
  constructor. exists v. exists h3.
  intuition.
  rewrite hstar_hpure_l in H3.
  rewrite hstar_hpure_l.
  intuition.
Qed.

Lemma entails_ens_seq : forall H1 H2 f1 f2,
  H1 ==> H2 ->
  entails f1 f2 ->
  entails (ens_ H1;; f1) (ens_ H2;; f2).
Proof.
  unfold entails.
  intros.
  inverts H3 as H3; no_shift. destr H3.
  apply (satisfies_ens_void H) in H3.
  applys* s_seq h3.
Qed.

Lemma ent_req_req : forall f1 f2 H1 H2 env,
  H2 ==> H1 ->
  entails_under env f1 f2 ->
  entails_under env (req H1 f1) (req H2 f2).
Proof.
  unfold entails_under. intros.
  constructor. intros.
  inverts H3. specializes H14 H6; auto.
Qed.

(* This is not very useful for rewriting.
  The sequent form [ent_req_req] is more interesting. *)
Lemma entails_req1 : forall H1 H2 f1 f2,
  H2 ==> H1 ->
  entails f1 f2 ->
  entails (req H1 f1) (req H2 f2).
Proof.
  unfold entails. intros.
  apply s_req. intros.
  apply H in H4.
  inverts H3.
  specializes H14 hr H4.
Qed.

Lemma entails_seq : forall f f1 f2,
  shift_free f ->
  entails f1 f2 ->
  entails (f;; f1) (f;; f2).
Proof.
  unfold entails.
  intros.
  inverts H1 as H1. 2: { apply H in H1. false. }
  apply* s_seq.
Qed.

Lemma norm_seq_ens_empty : forall f,
  bientails (ens_ \[];; f) f.
Proof.
  unfold bientails. intros.
  iff H.
  { inverts H as H; no_shift.
    inverts H as H. destr H.
    hinv H. hinv H. hinv H2.
    subst. rew_fmap *. }
  { eapply s_seq.
    eapply ens_void_empty_intro.
    assumption. }
Qed.

Lemma biab_single_h : forall H s1 s2 h1 h2 R H1 H2 f,
  satisfies s1 s2 h1 h2 R (ens_ (H \* H1);; req (H \* H2) f) ->
  satisfies s1 s2 h1 h2 R (ens_ H1;; req H2 f).
Proof.
  intros.
  inverts H0 as H0; no_shift. destr H0.
  (* ens adds a location to the heap *)
  inverts H0 as H0.
  (* use that to figure out what is in h3 *)
  destr H0. hinv H0. hinv H0. hinv H5. subst h0 h3 x0 x. rew_fmap *.

  (* prove just the first part *)
  rewrite norm_req_req in H10.
  inverts H10 as H10. specializes H10 x1 (h1 \u x2) ___.

  applys s_seq (h1 \u x2) vunit.
  { constructor. exists vunit. exists x2.
    splits*. hintro; jauto. }
  { assumption. }
Qed.

(** Biabduction for a single location. *)
Lemma biab_single : forall (x:loc) (a:val) s1 s2 h1 h2 R H1 H2 f,
  satisfies s1 s2 h1 h2 R (ens_ (x~~>a \* H1);; req (x~~>a \* H2) f)->
  satisfies s1 s2 h1 h2 R (ens_ H1;; req H2 f).
Proof.
  intros.
  applys* biab_single_h (x~~>a).
Qed.

(* This is proved elsewhere *)
Lemma norm_ens_req_transpose : forall H1 H2 Ha Hf f,
  biab Ha H1 H2 Hf ->
  entails (ens_ H1;; req H2 f)
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
    fold entails.
    introv H2.
    rewrite norm_seq_req_emp.
    pose proof entails_ens_seq. specializes H Hf Hf H2.
    rewrite norm_seq_req_emp.
    apply entails_refl. }

  { (* b_pts_match *)
    intros.

    (* use the req *)
    rewrite norm_req_req.
    constructor. intros. hinv H0. subst. rew_fmap.

    apply (IHHbi s1 s2).
    apply (biab_single H). }

  { (* b_any_match *)
    intros.
    apply IHHbi.
    applys* biab_single_h H. }

  { (* b_pts_diff *)
    introv H3.
    pose proof transpose_pts_diff.
    unfold entails in H.
    specializes H IHHbi H3. }
Qed.

(** * Entailment sequent *)

Lemma norm_seq_ens_sl_ex: forall A (c:A->hprop) f,
  entails (ens_ (\exists b, c b);; f)
    (∃ b, ens_ (c b);; f).
Proof.
  unfold entails. intros.
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
  entails_under env f (∀ b, fctx b).
Proof.
  unfold entails_under. intros.
  constructor. intros b.
  auto.
Qed.

Lemma ent_all_r1 : forall f A (fctx:A -> flow) s1 s2 s3 s4,
  (forall b, entails_sequent s1 s2 s3 s4 f (fctx b)) ->
  entails_sequent s1 s2 s3 s4 f (∀ b, fctx b).
Proof.
  unfold entails_sequent. intros.
  constructor. intros b.
  auto.
Qed.

Lemma fall_intro : forall s1 s2 h1 h2 R A (fctx:A -> flow),
  (forall b, satisfies s1 s2 h1 h2 R (fctx b)) ->
  satisfies s1 s2 h1 h2 R (∀ b, fctx b).
Proof.
  intros.
  constructor.
  auto.
Qed.

(* Converse is not true because f1 could depend on b *)
(* Lemma ent_seq_all_r : forall f f1 A (fctx:A -> flow) env,
  shift_free f1 ->
  entails_under env f (f1;; ∀ b, fctx b) ->
  entails_under env f (∀ b, f1;; fctx b).
Proof.
  unfold entails_under. intros.
  specializes H0 H1.
  apply fall_intro. intros.
  inverts H0 as H0. 2: { apply H in H0. false. }
  inverts H9 as H9. specializes H9 b.
  apply* s_seq.
Qed. *)

Lemma norm_seq_all_r: forall (A:Type) (f:A->flow) f1,
  shift_free f1 ->
  entails (f1;; (∀ x:A, f x)) (∀ x:A, f1;; f x).
Proof.
  unfold entails. introv Hsf H0.
  inverts H0. 2: { false Hsf H6. }
  applys s_fall. intros.
  inverts H8. specializes H5 b.
  applys* s_seq.
Qed.

Lemma ent_all_l : forall f A (fctx:A -> flow) s1 s2 s3 s4,
  (exists b, entails_sequent s1 s2 s3 s4 (fctx b) f) ->
  entails_sequent s1 s2 s3 s4 (∀ b, fctx b) f.
Proof.
  unfold entails_sequent. intros.
  destr H.
  apply H1.
  inverts H0 as H0. specializes H0 b.
  assumption.
Qed.

Lemma ent_ex_l : forall f A (fctx:A -> flow) s1 s2 s3 s4,
  (forall b, entails_sequent s1 s2 s3 s4 (fctx b) f) ->
  entails_sequent s1 s2 s3 s4 (fex (fun b => fctx b)) f.
Proof.
  unfold entails_sequent. intros.
  inverts H0 as H0. destr H0.
  specializes H H1.
  auto.
Qed.

Lemma ent_ex_r : forall f A (fctx:A -> flow) s1 s2 s3 s4,
  (exists b, entails_sequent s1 s2 s3 s4 f (fctx b)) ->
  entails_sequent s1 s2 s3 s4 f (fex (fun b => fctx b)).
Proof.
  unfold entails_sequent. intros.
  destr H.
  constructor. exists b.
  auto.
Qed.

Lemma ent_seq_all_l : forall f f1 A (fctx:A -> flow) s1 s2 s3 s4,
  (exists b, entails_sequent s1 s2 s3 s4 (fctx b;; f1) f) ->
  entails_sequent s1 s2 s3 s4 ((∀ b, fctx b);; f1) f.
Proof.
  unfold entails_sequent. intros.
  destr H.
  apply H1.
  inverts H0 as H0.
  { inverts H0 as H0. specializes H0 b.
    applys* s_seq. }
  { inverts H0 as H0. specializes H0 b.
    apply* s_bind_sh. }
Qed.

Lemma ent_seq_ex_l : forall f f1 A (fctx:A -> flow) s1 s2 s3 s4,
  (forall b, shift_free (fctx b)) ->
  (forall b, entails_sequent s1 s2 s3 s4 (fctx b;; f1) f) ->
  entails_sequent s1 s2 s3 s4 ((∃ b, fctx b);; f1) f.
Proof.
  unfold entails_sequent. intros.
  inverts H1 as H1.
  2: { inverts H1 as H1. destr H1. specializes H H2. false. }
  inverts H1 as H1. destr H1.
  applys H0 b.
  apply* s_seq.
Qed.

Lemma ent_seq_ex_r : forall f f1 A (fctx:A -> flow) s1 s2 s3 s4,
  (forall b, shift_free (fctx b)) ->
  (exists b, entails_sequent s1 s2 s3 s4 f (fctx b;; f1)) ->
  entails_sequent s1 s2 s3 s4 f ((∃ b, fctx b);; f1).
Proof.
  unfold entails_sequent. intros.
  destr H0.
  specializes H2 H1.
  inverts H2 as H2. 2: { apply H in H2. false. }
  eapply s_seq.
  apply s_fex.
  exists b.
  eassumption.
  assumption.
Qed.

Lemma ent_req_l : forall f f1 P env,
  P ->
  entails_under env f1 f ->
  entails_under env (req \[P] f1) f.
Proof.
  unfold entails_under. intros.
  inverts H1.
  applys H0.
  applys H9.
  hintro. assumption.
  fmap_eq.
  fmap_disjoint.
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

Lemma ent_ens_void_l : forall env f P,
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

Lemma ent_ens_void_single : forall env H H1,
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

Lemma ent_ens_single : forall env Q Q1,
  (Q1 ===> Q) ->
  entails_under env (ens Q1) (ens Q).
Proof.
  unfold entails_under. intros.
  inverts H0. destr H7.
  applys s_ens.
  exs. splits*.
  applys* H.
Qed.

Lemma ent_disj_l : forall f1 f2 f3 env,
  entails_under env f1 f3 ->
  entails_under env f2 f3 ->
  entails_under env (disj f1 f2) f3.
Proof.
  unfold entails_under. intros.
  inverts H1 as H1; auto.
Qed.

Lemma norm_rs_ex : forall A ctx,
  entails (rs (∃ (x:A), ctx x)) (∃ (x:A), rs (ctx x)).
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

Lemma norm_rs_all : forall A ctx,
  entails (rs (∀ (x:A), ctx x)) (∀ (x:A), rs (ctx x)).
Proof.
  unfold entails. intros.
  inverts H as H.
  { constructor. intros b.
    inverts H as H. specializes H b.
    eapply s_rs_sh; jauto. }
  { constructor. intros b.
    inverts H as H. specializes H b.
    apply s_rs_val.
    assumption. }
Qed.

(* norm_req_ex can't be proved *)
Lemma norm_req_all : forall H (A:Type) (fctx:A->flow),
  entails (req H (∀ b, fctx b)) (∀ b, req H (fctx b)).
Proof.
  unfold entails. intros.
  applys s_fall. intros.
  applys s_req. intros.
  inverts H0. specializes H11 H1 H2 H3.
  inverts* H11.
Qed.


Lemma req_pure_inv: forall s1 s2 h1 h2 R P f,
  P ->
  satisfies s1 s2 h1 h2 R (req \[P] f) ->
  satisfies s1 s2 h1 h2 R f.
Proof.
  intros.
  inverts H0 as H7.
  specializes H7 empty_heap h1. apply H7.
  hintro. assumption. fmap_eq. fmap_disjoint.
Qed.

Lemma req_pure_intro : forall s1 s2 h1 h2 R P f,
  (P -> satisfies s1 s2 h1 h2 R f) ->
  satisfies s1 s2 h1 h2 R (req \[P] f).
Proof.
  intros.
  apply s_req. intros.
  hinv H0. subst. rew_fmap.
  apply* H.
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

Lemma norm_seq_ex_l : forall f1 (A:Type) (fctx:A->flow),
  entails ((∃ b, fctx b);; f1) (∃ b, fctx b;; f1).
Proof.
  unfold entails. intros.
  inverts H.
  { inverts H7. destr H5.
    applys s_fex. exists b.
    applys* s_seq. }
  { inverts H6. destr H5.
    applys s_fex. exists b.
    applys* s_bind_sh. }
Qed.

Lemma norm_seq_ex_r: forall (A:Type) (f:A->flow) f1,
  shift_free f1 ->
  entails (f1;; (∃ x:A, f x)) (∃ x:A, f1;; f x).
Proof.
  unfold entails. introv Hsf H0.
  inverts H0. 2: { false Hsf H6. }
  inverts H8. destr H5.
  applys s_fex. exists b.
  applys* s_seq.
Qed.

Lemma norm_rs_seq_distr : forall f1 f2,
  shift_free f1 ->
  entails (rs (f1;; f2)) (rs f1;; rs f2).
Proof.
  unfold entails. intros.
  inverts H0 as H0.
  { (* f1;; f2 has a shift *)
    inverts H0 as H0.
    2: { false H H0. }
    eapply s_seq.
    apply s_rs_val. eassumption.
    eapply s_rs_sh. eassumption.
    eassumption. }
  { inverts H0 as H0.
    eapply s_seq.
    apply s_rs_val.
    eassumption.
    apply s_rs_val.
    eassumption. }
Qed.

Lemma norm_ens_ens_void_swap : forall H Q f,
  bientails (ens Q;; ens_ H;; f) (ens_ H;; ens Q;; f).
Proof.
  iff H0.
  { inverts H0. 2: { inverts H7. destr H6. discriminate. }
    inverts H8. destr H6. injects H0.
    inverts H9. 2: { inverts H10. destr H9. discriminate. }
    inverts H11. destr H9. injects H0. hinv H3. hinv H0.
    applys s_seq.
    applys s_ens.
    { exists vunit x0. splits*. hintro. splits*. }
    applys s_seq H12.
    applys s_ens.
    { exists v0 h0. splits*. } }
  { inverts H0. 2: { inverts H7. destr H6. discriminate. }
    inverts H8. destr H6. injects H0.
    inverts H9. 2: { inverts H10. destr H9. discriminate. }
    inverts H11. destr H9. injects H0. hinv H1. hinv H0.
    applys s_seq.
    applys s_ens.
    { exists v1 h5. splits*. }
    applys s_seq H12.
    applys s_ens.
    { exists vunit x0. splits*. hintro. splits*. } }
Qed.


Lemma norm_seq_ex_widen : forall f1 A (fctx:A -> flow),
  shift_free f1 ->
  entails (f1;; (∃ b, fctx b))
    (∃ b, f1;; (fctx b)).
Proof.
  unfold entails. intros * Hsf * H.
  inverts H as H1 H2.
  { inverts H2 as (b&H2).
    apply s_fex. exists b.
    applys s_seq H1 H2. }
  { false Hsf H1. }
Qed.

Lemma norm_rs_seq_ex_l : forall f1 A (fctx:A -> flow),
  shift_free f1 ->
  entails (rs (f1;; (∃ b, fctx b)))
    (∃ b, rs (f1;; (fctx b))).
Proof.
  intros.
  rewrite norm_seq_ex_widen.
  2: { assumption. }
  lets H1: norm_rs_ex.
  specializes H1 A (fun b => f1;; fctx b).
Qed.


Definition flow_res (f:flow) (v:val) : Prop :=
  forall s1 s2 h1 h2, satisfies s1 s2 h1 h2 (norm v) f.

Lemma norm_bind_seq : forall f fk v,
  shift_free f ->
  det f ->
  flow_res f v ->
  entails (bind f fk) (f;; fk v).
Proof.
  unfold flow_res, entails. intros * Hsf Hd Hfr * H.
  inverts H. 2: { false Hsf H6. }
  specializes Hfr s1 s3 h1 h3.
  specializes Hd H7 Hfr. injects Hd.
  applys s_seq H7.
  assumption.
Qed.

(* which definition of flow_res should be used? *)
Definition flow_res1 (f:flow) (v1:val) : Prop :=
  forall s1 s2 h1 h2 v, satisfies s1 s2 h1 h2 (norm v) f -> v1 = v.

Lemma norm_bind_seq1 : forall f fk v,
  shift_free f ->
  flow_res1 f v ->
  entails (bind f fk) (f;; fk v).
Proof.
  unfold entails. intros * Hsf Hfr * H.
  inverts H. 2: { false Hsf H6. }
  specializes Hfr H7.
  subst.
  applys* s_seq H7.
Qed.

(** Similar to [norm_seq_assoc].
  We only need one [shift_free] premise here
  because we're rewriting only in one direction. *)
Lemma norm_bind_seq_assoc : forall fk f1 f2,
  shift_free f1 ->
  entails (bind (f1;; f2) fk) (f1;; bind f2 fk).
Proof.
  unfold entails. intros * Hsf1 * H.
  inverts H.
  { inverts H7.
    applys s_seq H6.
    applys* s_bind. }
  { inverts H6.
    - applys s_seq H7.
      applys* s_bind_sh.
    - false Hsf1 H4. }
Qed.

(* TODO can this be generalised (to [norm_bind_pure])? *)
Lemma norm_bind_val : forall fk v,
  entails (bind (ens (fun r => \[r = v])) fk) (fk v).
Proof.
  unfold entails. intros * H.
  inverts H. 2: { false sf_ens H6. }
  inverts H7. destr H5. injects H. hinv H0. subst. rew_fmap.
  assumption.
Qed.

Lemma norm_bind_ens_void : forall fk H,
  entails (bind (ens_ H) fk) (seq (ens_ H) (fk vunit)).
Proof.
  unfold entails. intros * H.
  inverts H.
  { pose proof H8.
    inverts H8. destr H7. hinv H2. hinv H2. injects H1. subst.
    applys* s_seq. }
  { false sf_ens_ H7. }
Qed.

Lemma norm_bind_req : forall f fk H,
  shift_free f ->
  entails (bind (req H f) fk) (req H (bind f fk)).
Proof.
  unfold entails. intros * Hsf * H.
  applys s_req. intros.
  inverts H.
  2: { inverts H10. specializes H11 H1 H2 H3. false Hsf H11. }
  { inverts H11. specializes H10 H1 H2 H3.
    applys* s_bind. }
Qed.

(** * Reduction example *)
(**
  < (shift k. k i1) + (shift k1. k1 i2) >
  assuming left-to-right evaluation
  k1 takes i1, result is i1 + i2
  k2 takes i2, result is also i1 + i2
*)
(* Example e1_red : forall x1 x2 i1 i2 r3, exists f,
  entails_under empty_env
    (rs
      (sh x1 (unk x1 (vint i1));;
        sh x2 (unk x2 (vint i2));;
        ens (fun r => \[r = vint (i1 + i2)]))) f.
Proof.
  intros.
  eexists.

  rewrite red_init.
  rewrite red_acc.
  rewrite red_shift_elim.
  apply ent_seq_defun.

  (* TODO funfold1 *)
  rewrites (>> entails_under_unk x1); [ resolve_fn_in_env | ].
  simpl.

  rewrite norm_ens_eq.
  rewrite (norm_seq_pure_l (fun r0 => r0 = vint i1)).

  rewrite red_init.
  rewrite red_acc.
  rewrite red_shift_elim.
  rewrites (>> red_skip sf_defun).
  apply ent_seq_defun.

  rewrites (>> entails_under_unk x2); [ resolve_fn_in_env | ].
  simpl.

  rewrite norm_ens_eq.

  rewrite red_normal; shiftfree.
  rewrite red_normal; shiftfree.
  rewrite red_normal; shiftfree.

  rewrite (norm_seq_pure_l (fun r4 => r4 = vint i2)).
  apply entails_under_refl.
Qed. *)

Example ex_rewrite_right:
  (* entails (ens_ \[True]) (ens_ \[True];; ens_ \[True]). *)
  entails (ens_ \[True]) (ens_ \[True];; ens_ \[True];; ens_ \[True]).
Proof.
(* Set Typeclasses Debug. *)
  rewrite <- norm_ens_ens_void.
Abort.

Example ex_rewrite_right1:
  entails_under empty_env (ens_ \[True]) (ens_ \[True];; ens_ \[True];; ens_ \[True]).
Proof.
  assert (forall H1 H2, entails_under empty_env (ens_ H1;; ens_ H2) (ens_ (H1 \* H2))) as ?. admit.
  assert (forall H1 H2, entails_under empty_env (ens_ (H1 \* H2)) (ens_ H1;; ens_ H2)) as ?. admit.
  (* rewrite norm_ens_ens_void. *)
  (* Set Typeclasses Debug. *)
  (* rewrite H.
  rewrite H0.
  rewrite <- H. *)
  rewrite <- H0.
  rewrite <- H.

Abort.

Example ex_rewrite_right1:
  entails_under (Fmap.update empty_env "k" (fun a => ens (fun r => \[a = r])))
   (ens_ \[True];; unk "k" (vint 1)) (ens_ \[True]).
Proof.
  (* funfold1 "k". *)
  pose proof (@entails_under_unk (Fmap.update empty_env "k" (fun a => ens (fun r => \[a = r]))) "k").
  specializes H (vint 1) ___.

  rewrite H.
  rew_fmap.

Abort.

Example ex_rewrite_right1:
  entails_under (Fmap.update empty_env "k" (fun a => ens (fun r => \[a = r])))
   (unk "k" (vint 1);; ens_ \[True]) (ens_ \[True]).
Proof.
  (* funfold1 "k". *)
  pose proof (@entails_under_unk (Fmap.update empty_env "k" (fun a => ens (fun r => \[a = r]))) "k").
  specializes H (vint 1) ___.

(* Set Typeclasses Debug. *)
  (* setoid_rewrite H. *)
  rewrite H.
  rew_fmap.

Abort.



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
