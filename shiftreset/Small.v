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
  | fin : flow
  | req : hprop -> flow -> flow
  | ens : postcond -> flow
  | seq : flow -> flow -> flow
  | fex : forall (A:Type), (A -> flow) -> flow
  | fall : forall (A:Type), (A -> flow) -> flow
  | unk : var -> val -> val -> flow
  | intersect : flow -> flow -> flow
  | disj : flow -> flow -> flow
  .

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

Notation "'ens' r '.' Q" := (ens (fun r => Q))
  (at level 80, format "'ens'  r '.'  Q" , only printing) : flow_scope.

Implicit Types s : senv.
Implicit Types h : heap.
Implicit Types H : hprop.
Implicit Types Q : postcond.
Implicit Types u : ufun.
Implicit Types f : flow.
Implicit Types x y z k : var.
Implicit Types a v r : val.
Implicit Types e : expr.

Inductive satisfies : senv -> senv -> heap -> heap -> val -> flow -> flow -> Prop :=

  | s_req1 : forall s1 s2 H h1 h2 v f f1,
    (forall (hp hr:heap),
      H hp ->
      h1 = Fmap.union hr hp ->
      Fmap.disjoint hr hp ->
      satisfies s1 s2 hr h2 v f f1) ->
    satisfies s1 s2 h1 h2 v (req H f) f1

  | s_ens1 : forall s1 Q h1 h2 v h3,
    Q v h3 ->
    h2 = Fmap.union h1 h3 ->
    Fmap.disjoint h1 h3 ->
    satisfies s1 s1 h1 h2 v (ens Q) fin

  | s_seq_empty1 : forall v s1 h1 f2,
    satisfies s1 s1 h1 h1 v (seq fin f2) f2

  | s_seq_step1 : forall v s1 s2 h1 h2 f1 f2 f3,
    satisfies s1 s2 h1 h2 v f1 f3 ->
    satisfies s1 s2 h1 h2 v (seq f1 f2) (seq f3 f2)

  | s_fex1 : forall s1 s2 h1 h2 v (A:Type) (c:A->flow) b,
    satisfies s1 s2 h1 h2 v (@fex A c) (c b)

  | s_fall1 : forall s1 s2 h1 h2 v (A:Type) (c:A->flow) f1,
    (forall b, satisfies s1 s2 h1 h2 v (c b) f1) ->
    satisfies s1 s2 h1 h2 v (@fall A c) f1

  | s_intersect_step_l1 : forall s1 s2 h1 h2 v f1 f2 f3,
    satisfies s1 s2 h1 h2 v f1 f3 ->
    satisfies s1 s2 h1 h2 v (intersect f1 f2) (intersect f3 f2)

  | s_intersect_step_r1 : forall s1 s2 h1 h2 v f1 f2 f3,
    satisfies s1 s2 h1 h2 v f1 f3 ->
    satisfies s1 s2 h1 h2 v (intersect f1 f2) (intersect f1 f3)

  | s_intersect_elim_l1 : forall s1 h1 v f2,
    satisfies s1 s1 h1 h1 v (intersect fin f2) f2

  | s_intersect_elim_r1 : forall s1 h1 v f1,
    satisfies s1 s1 h1 h1 v (intersect f1 fin) f1

  | s_disj_l1 : forall s1 h1 v f1 f2,
    satisfies s1 s1 h1 h1 v (disj f1 f2) f1

  | s_disj_r1 : forall s1 h1 v f1 f2,
    satisfies s1 s1 h1 h1 v (disj f1 f2) f2

  | s_unk1 : forall s1 h1 h1 r xf uf a,
    Fmap.read s1 xf = uf ->
    satisfies s1 s1 h1 h1 r (unk xf a r) (uf a r)
  .

Notation "s1 ',' s2 ','  h1 ','  h2 ','  r  '|=' f1 '~>' f2" :=
  (satisfies s1 s2 h1 h2 r f1 f2) (at level 30, only printing).


Inductive steps :
  senv -> senv -> heap -> heap -> val -> flow -> flow -> Prop :=

  | steps_refl : forall s1 h1 v f,
    steps s1 s1 h1 h1 v f f

  | steps_step : forall s1 s2 s3 h1 h2 h3 v f1 f2 f3,
    satisfies s1 s2 h1 h2 v f1 f2 ->
    steps s2 s3 h2 h3 v f2 f3 ->
    steps s1 s3 h1 h3 v f1 f3.

Notation "s1 ',' s2 ','  h1 ','  h2 ','  r  '|=' f1 '~>*' f2" :=
  (steps s1 s2 h1 h2 r f1 f2) (at level 30, only printing).

Lemma steps_of_step : forall s1 s2 h1 h2 v f1 f2,
  satisfies s1 s2 h1 h2 v f1 f2 ->
  steps s1 s2 h1 h2 v f1 f2.
Proof using.
  introv M. applys steps_step M. applys steps_refl.
Qed.

Lemma steps_trans : forall s1 s2 s3 h1 h2 h3 v f1 f2 f3,
  steps s1 s2 h1 h2 v f1 f2 ->
  steps s2 s3 h2 h3 v f2 f3 ->
  steps s1 s3 h1 h3 v f1 f3.
Proof using.
  introv M1. induction M1; introv M2. { auto. } { constructors*. }
Qed.

Definition terminal f : Prop :=
  f = fin.

Definition reducible s1 h1 f1 : Prop :=
  exists s2 h2 v f2, satisfies s1 s2 h1 h2 v f1 f2.

Lemma reducible_inv : forall s h v,
  ~ reducible s h fin.
Proof using.
  intros. intros M. inverts M. destr H. inverts H0 as H0.
Qed.

Definition notstuck s h f : Prop :=
  terminal f \/ reducible s h f.

(* Inductive terminates : heap->trm->Prop :=
  | terminates_step : forall s t,
      (forall s' t', step s t s' t' -> terminates s' t') ->
      terminates s t.

Definition safe (s:heap) (t:trm) : Prop :=
  forall s' t', steps s t s' t' -> notstuck s' t'.

Definition correct (s:heap) (t:trm) (Q:val->hprop) : Prop :=
  forall s' v, steps s t s' v -> Q v s'. *)

Example step_e1: forall (x y:loc) s1, exists s2 h2 v,
  x <> y ->
  steps s1 s2 empty_heap h2 v (ens_ (x~~>vint 1);; ens_ (y~~>vint 2)) fin.
Proof.
  intros. exs. intros.

  applys steps_step.
  { applys s_seq_step1.
    applys s_ens1.
    - hintro. split. reflexivity. apply hsingle_intro.
    - fmap_eq. reflexivity.
    - fmap_disjoint. }

  applys steps_step.
  { applys s_seq_empty1. }

  applys steps_step.
  { applys s_ens1.
    - hintro. split. reflexivity. apply hsingle_intro.
    - reflexivity.
    - apply* Fmap.disjoint_single_single. }

  applys steps_refl.
Qed.

(** * Entailment *)
Definition entails (f1 f2:flow) : Prop :=
  forall s1 s2 h1 h2 v,
    steps s1 s2 h1 h2 v f1 fin ->
    steps s1 s2 h1 h2 v f2 fin.

Infix "⊑" := entails (at level 90, right associativity) : flow_scope.

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
  Instance Proper_seq : Proper (entails ====> entails ====> entails) seq.
  Proof.
    unfold Proper, entails, respectful.
    intros.
    inverts H1 as H1.
    inverts H1 as H1.
    {
      (* x is fin *)
      specializes H. apply steps_refl.
      specializes H0 H2. clear H2.

      (* applys steps_trans (y;; y0) (fin;; y0). *)
      (* steps of step: ~> to ~>* *)
      (* lets: steps_of_step s_seq_step1. *)
      (* applys steps_step. *)
      (* applys s_seq_step1. *)
      (* applys s_seq_empty1. *)
      admit.
    }
    {
      admit.
    }

  (* Qed. *)
  Abort.

End Propriety.
