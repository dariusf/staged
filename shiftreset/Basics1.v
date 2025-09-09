
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
  (* | vfun : var -> expr -> val *)
  (* | vfix : var -> var -> expr -> val *)
  | vloc : loc -> val
  | vtup : val -> val -> val
  | vstr : string -> val
  | vbool : bool -> val
  | vlist : list val -> val
  | vfptr : var -> val
.


#[global]
Instance Inhab_val : Inhab val.
Proof.
  constructor.
  exists vunit.
  constructor.
Qed.

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
  | bind : flow -> (val -> flow) -> flow
  | fex : forall (A:Type), (A -> flow) -> flow
  | fall : forall (A:Type), (A -> flow) -> flow
  | unk : var -> val -> flow
  | intersect : flow -> flow -> flow
  | disj : flow -> flow -> flow
  | shc : (val -> flow) -> (val -> flow) -> flow
  | rs : flow -> flow
  | defun : var -> (val -> flow) -> flow
  | discard : var -> flow
  | discard_all : flow
  .

Definition seq (f1 f2:flow) := bind f1 (fun _ => f2).

Definition ret (v:val) := ens (fun r => \[r = v]).

(* Definition sh k fb := shc k fb (fun v => ens (fun r => \[r = v])). *)

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
  (* | shft : var -> flow -> (val -> flow) -> result. *)
  | shft : var -> var -> result.
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

(* Notation "'sh' '(' k '.' fb '),' vr" := (sh k fb vr)
  (at level 80, format "'sh'  '(' k '.'  fb '),'  vr", only printing) : flow_scope. *)

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
(* Implicit Types fb : var -> flow. *)
Implicit Types fk : val -> flow.
Implicit Types x y z k : var.
Implicit Types a v r : val.
Implicit Types R : result.

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

  | s_shc : forall xb xk s1 s2 h1 fkb fk,
    (* ~ Fmap.indom s1 k -> *)
    s2 = Fmap.update (Fmap.update s1 xk fk) xb fkb ->
    satisfies s1 s2 h1 h1
      (shft xb xk)
      (shc fkb fk)

  | s_bind_sh : forall s1 s2 s3 h1 h2 f1 (f2 fk:val->flow) xk xb,
  (* f1 (f2:val->flow) fk h1 h2 fb k xb xk fkb, *)
    satisfies s1 s2 h1 h2 (shft xb xk) f1 ->
    s3 = Fmap.update s2 xk (fun r1 => bind (fk r1) f2) ->
    satisfies s1 s3 h1 h2 (shft xb xk) (bind f1 f2)

  | s_rs_sh : forall s1 s2 s3 s4 h1 h2 h3 f R xk xb fkb fk,
    satisfies s1 s3 h1 h3 (shft xb xk) f ->
    fkb = Fmap.read s3 xb ->
    fk = Fmap.read s3 xk ->
    s4 = Fmap.update s3 xk (fun a => rs (fk a)) ->
    satisfies s4 s2 h3 h2 R (rs (fkb (vfptr xk))) ->
    satisfies s1 s2 h1 h2 R (rs f)

  | s_rs_val : forall s1 s2 h1 h2 v f,
    satisfies s1 s2 h1 h2 (norm v) f ->
    satisfies s1 s2 h1 h2 (norm v) (rs f)

  | s_defun s1 s2 h1 x uf :
    ~ Fmap.indom s1 x ->
    s2 = Fmap.update s1 x uf ->
    satisfies s1 s2 h1 h1 (norm vunit) (defun x uf)

  | s_discard s1 s2 h (f:var) :
    s2 = Fmap.remove s1 f ->
    satisfies s1 s2 h h (norm vunit) (discard f)

  | s_discard_all s1 h (f:var) :
    satisfies s1 empty_env h h (norm vunit) (discard_all)

  .

Notation "s1 ',' s2 ','  h1 ','  h2 ','  r  '|=' f" :=
  (satisfies s1 s2 h1 h2 r f) (at level 30, only printing).


Lemma fmap_read_update_not : forall A B {IB:Inhab B} (k k1:A) (v:B) m,
  k <> k1 ->
  read (update m k1 v) k = read m k.
Proof.
  intros. unfold update.
  rewrite read_union_r.
  reflexivity.
  apply fmap_not_indom_of_neq.
  symmetry. assumption.
Qed.

Definition unkf (f:val) (v:val) : flow :=
  ∃ (g:var), ens_ \[vfptr g = f];; unk g v.

Example e1: exists s h R, satisfies empty_env s empty_heap h R
  (rs (shc
    (fun (k:val) => unkf k (vint 1))
    (fun v => ret v))).
Proof.
  exs.
  unfold unkf.
  applys* s_rs_sh.
  { applys s_shc "b" "c". reflexivity. }
  {
    fmap_eq.
    applys s_rs_val.
    applys s_fex.
    exists "c".
    applys s_bind.
    applys s_ens.
    { exists. splits*. hintro. splits*. hintro. reflexivity. }
    applys* s_unk.
    fmap_eq.
    rewrite fmap_read_update_not. 2: { unfold not. intros. false. }
    rewrite fmap_read_update.
    unfold ret.
    applys s_rs_val.
    applys s_ens.
    exs. splits*.
    hintro. reflexivity.
  }
Qed.

(* Lemma s_sh : forall s1 h1 fb k,
  ~ Fmap.indom s1 k ->
  satisfies s1 s1 h1 h1
    (shft k fb (fun r1 => ens (fun r => \[r = r1])))
    (sh k fb).
Proof.
  unfold sh. intros.
  applys* s_shc.
Qed.

(* For when the goal can be dispatched by brute force.
  jauto handles these but will not leave unsolved goals. *)
Ltac zap :=
  lazymatch goal with
  | H: exists _, _ |- _ => destr H; zap
  | H: _ /\ _ |- _ => destr H; zap
  | |- _ /\ _ => splits; zap
  | |- exists _, _ => eexists; zap
  | _ => jauto
  end.

(* Dispatch goals involving the heaps that come out of ens once
  we have to reason about semantics *)
Ltac heaps :=
  lazymatch goal with
  | H: exists _, _ |- _ => destr H; heaps
  | H: _ /\ _ |- _ => destr H; heaps
  | H: norm _ = norm _ |- _ => injects H; heaps
  | H: (_ ~~> _) _ |- _ => hinv H; heaps
  | H: \[_] _ |- _ => hinv H; heaps
  | H: (_ \* _) _ |- _ => hinv H; heaps
  | |- (_ ~~> _) _ => hintro; heaps
  | |- (_ \* _) _ => hintro; heaps
  | |- \[_] _ => hintro; heaps
  (* as late as we can *)
  | |- _ /\ _ => splits; heaps
  | |- exists _, _ => eexists; heaps
  | _ => subst; rew_fmap *
  end.

Lemma s_seq : forall s3 h3 r1 s1 s2 f1 f2 h1 h2 R,
  satisfies s1 s3 h1 h3 (norm r1) f1 ->
  satisfies s3 s2 h3 h2 R f2 ->
  satisfies s1 s2 h1 h2 R (seq f1 f2).
Proof.
  unfold seq. intros.
  applys* s_bind.
Qed.

Notation s_seq_sh := s_bind_sh.

Lemma s_ens_ : forall H h1 h2 s1,
  (exists h3,
    H h3 /\
    h2 = Fmap.union h1 h3 /\
    Fmap.disjoint h1 h3) ->
  satisfies s1 s1 h1 h2 (norm vunit) (ens_ H).
Proof.
  unfold ens_. intros.
  applys* s_ens.
  heaps.
Qed.

Definition entails (f1 f2:flow) : Prop :=
  forall s1 s2 h1 h2 R,
    satisfies s1 s2 h1 h2 R f1 -> satisfies s1 s2 h1 h2 R f2.

Infix "⊑" := entails (at level 90, right associativity) : flow_scope.

Inductive gentails_under : senv -> nat -> flow -> flow -> Prop :=

  | geu_base : forall s1 f1 f2,
    (forall s2 h1 h2 v,
      satisfies s1 s2 h1 h2 (norm v) f1 ->
      satisfies s1 s2 h1 h2 (norm v) f2) ->
    gentails_under s1 O f1 f2

  | geu_shift : forall s1 n f1 f2,
    (forall s2 h1 h2 k fb fk,
      satisfies s1 s2 h1 h2 (shft k fb fk) f1 ->
      exists fb1 fk1,
        satisfies s1 s2 h1 h2 (shft k fb1 fk1) f2 /\
        gentails_under s1 n fb fb1 /\
        forall v, gentails_under s1 n (fk v) (fk1 v)) ->

    gentails_under s1 (S n) f1 f2.

(* hide the index *)
Notation "env '⊢' f1 '⊆' f2" :=
  (gentails_under env _ f1 f2) (at level 90, only printing) : flow_scope.

(* Definition gentails n f1 f2 :=
  forall s1, gentails_under s1 n f1 f2. *)

Inductive gentails : nat -> flow -> flow -> Prop :=

  | ge_base : forall f1 f2,
    (forall s1 s2 h1 h2 v,
      satisfies s1 s2 h1 h2 (norm v) f1 ->
      satisfies s1 s2 h1 h2 (norm v) f2) ->
    gentails O f1 f2

  | ge_shift : forall n f1 f2,
    (forall s1 s2 h1 h2 k fb fk,
      satisfies s1 s2 h1 h2 (shft k fb fk) f1 ->
      exists fb1 fk1,
        satisfies s1 s2 h1 h2 (shft k fb1 fk1) f2 /\
        gentails n fb fb1 /\
        forall v, gentails n (fk v) (fk1 v)) ->

    gentails (S n) f1 f2.

Notation "f1 '⊆' n f2" :=
  (gentails n f1 f2) (at level 90, only printing) : flow_scope.

Lemma entails_gentails: forall n f1 f2,
  entails f1 f2 -> gentails n f1 f2.
Proof.
  unfold entails.
  intros n. induction n; intros.
  { applys* ge_base. }
  { applys ge_shift. jauto. }
Qed.

Definition entails_under s1 f1 f2 :=
  forall h1 h2 s2 R,
    satisfies s1 s2 h1 h2 R f1 -> satisfies s1 s2 h1 h2 R f2.

Notation "env '⊢' f1 '⊑' f2" :=
  (entails_under env f1 f2) (at level 90, only printing) : flow_scope.

Lemma entails_under_gentails_under: forall n s1 f1 f2,
  entails_under s1 f1 f2 -> gentails_under s1 n f1 f2.
Proof.
  unfold entails_under.
  intros n. induction n; intros.
  { applys* geu_base. }
  { applys geu_shift. jauto. }
Qed.

Definition bientails (f1 f2:flow) : Prop :=
  forall h1 h2 R s1 s2,
    satisfies s1 s2 h1 h2 R f1 <-> satisfies s1 s2 h1 h2 R f2.

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

Instance gentails_refl : forall n, Reflexive (gentails n).
Proof.
  unfold Reflexive.
  intros n. induction n; intros.
  - applys ge_base. intros.
    assumption.
  - intros.
    applys ge_shift. intros.
    exs. splits*.
Qed.

(* This is the first lemma we need the index to prove. *)
Instance gentails_trans : forall n, Transitive (gentails n).
Proof.
  unfold Transitive.
  intros n. induction n; intros.
  - inverts H. inverts H0. applys ge_base. intros.
    eauto.
  - applys ge_shift. intros.
    inverts H as H. specializes H H1. destr H.
    inverts H0 as H0. specializes H0 H2. destr H0.
    exs. splits*.
Qed.

Instance gentails_preorder : forall n, PreOrder (gentails n).
Proof.
  constructor.
  apply gentails_refl.
  apply gentails_trans.
Qed.

Instance gentails_under_refl : forall n env, Reflexive (gentails_under env n).
Proof.
  unfold Reflexive.
  intros n. induction n; intros.
  - applys geu_base. intros.
    assumption.
  - intros.
    applys geu_shift. intros.
    exs. splits*.
Qed.

Instance gentails_under_trans : forall n env, Transitive (gentails_under env n).
Proof.
  unfold Transitive.
  intros n. induction n; intros.
  - inverts H. inverts H0. applys geu_base. intros.
    eauto.
  - applys geu_shift. intros.
    inverts H as H. specializes H H1. destr H.
    inverts H0 as H0. specializes H0 H2. destr H0.
    exs. splits*.
Qed.

Instance gentails_under_preorder : forall n env, PreOrder (gentails_under env n).
Proof.
  constructor.
  apply gentails_under_refl.
  apply gentails_under_trans.
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

Definition flow_res (f:flow) (v:val) : Prop :=
  forall s1 s2 h1 h2, satisfies s1 s2 h1 h2 (norm v) f.

(* which definition of flow_res should be used? *)
Definition flow_res1 (f:flow) (v1:val) : Prop :=
  forall s1 s2 h1 h2 v, satisfies s1 s2 h1 h2 (norm v) f -> v1 = v. *)
