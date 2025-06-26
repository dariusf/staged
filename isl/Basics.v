
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
  | verror : val
  | vuninit : val
  | vfreed : val
(** A deeply-embedded function pointer, referring to a [ufun] in the environment. *)

(* with expr : Type :=
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
  | preset (e: expr). *)
  .

Definition vadd (v1 v2 : val) : val :=
  match v1, v2 with
  | vint i1, vint i2 => vint (i1 + i2)
  | _, _ => vunit
  end.

Definition viop f a b :=
  match a, b with
  | vint a1, vint b1 => f a1 b1
  | _, _ => vunit
  end.

Definition vbop f a b :=
  match a, b with
  | vbool a1, vbool b1 => f a1 b1
  | _, _ => vunit
  end.

Definition virel f a b :=
  match a, b with
  | vint a1, vint b1 => f a1 b1
  | _, _ => False
  end.

Definition vgt a b := virel (fun x y => x > y) a b.
Definition vlt a b := virel (fun x y => x < y) a b.
Definition vge a b := virel (fun x y => x >= y) a b.
Definition vle a b := virel (fun x y => x <= y) a b.
Definition veq a b := virel (fun x y => x = y) a b.
Definition vneq a b := virel (fun x y => x <> y) a b.
Definition vsub a b := viop (fun x y => vint (x - y)) a b.

(* Definition vand a b := vbop (fun x y => vbool (x && y)) a b. *)

(* Definition vand (v1 v2 : val) : val :=
  match v1, v2 with
  | vbool b1, vbool b2 => vbool (andb b1 b2)
  | _, _ => vunit
  end. *)

Definition vand (a b:val) :=
  match a, b with
  | vbool true, _ => b
  | vbool false, _ => vbool false
  | _, vbool false => vbool false
  | _, vbool true => a
  | _, _ => vunit
  end.

#[global]
Instance Inhab_val : Inhab val.
Proof.
  constructor.
  exists vunit.
  constructor.
Qed.

(* Coercion vint : Z >-> val.
Coercion vbool : bool >-> val. *)

(* Fixpoint subst (y:var) (v:val) (e:expr) : expr :=
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
  end. *)

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
  | defun : var -> (val -> flow) -> flow
  | discard : var -> flow
  | error : flow
  | alloc : flow
  | free : val -> flow
  | read : val -> flow
  | write : val -> val -> flow
  .

Definition seq (f1 f2:flow) := bind f1 (fun _ => f2).

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

Inductive result : Type :=
  | ok : val -> result
  | err : result.

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
      R = ok v /\
      Q v h3 /\
      h2 = Fmap.union h1 h3 /\
      Fmap.disjoint h1 h3) ->
    satisfies s1 s1 h1 h2 R (ens Q)

  | s_error : forall s1 h1 R,
    satisfies s1 s1 h1 h1 err error

  | s_bind : forall s3 h3 v s1 s2 f1 (f2:val->flow) h1 h2 R,
    satisfies s1 s3 h1 h3 (ok v) f1 ->
    satisfies s3 s2 h3 h2 R (f2 v) ->
    satisfies s1 s2 h1 h2 R (bind f1 f2)

  | s_bind_err : forall s1 s2 f1 (f2:val->flow) h1 h2,
    satisfies s1 s2 h1 h2 err f1 ->
    satisfies s1 s2 h1 h2 err (bind f1 f2)

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

  | s_defun s1 s2 h1 x uf :
    ~ Fmap.indom s1 x ->
    s2 = Fmap.update s1 x uf ->
    satisfies s1 s2 h1 h1 (ok vunit) (defun x uf)

  | s_discard s1 s2 h (f:var) :
    s2 = Fmap.remove s1 f ->
    satisfies s1 s2 h h (ok vunit) (discard f)

  | s_free : forall s1 h1 h2 l vl,
    vl = vloc l ->
    Fmap.indom h1 l ->
    Fmap.read h1 l <> vfreed ->
    h2 = Fmap.update h1 l vfreed ->
    satisfies s1 s1 h1 h2 (ok vunit) (free vl)

  | s_free_err : forall s1 h1 l vl,
    vl = vloc l ->
    Fmap.indom h1 l -> (* miss would relax this *)
    Fmap.read h1 l = vfreed ->
    satisfies s1 s1 h1 h1 err (free vl)

  | s_alloc : forall s1 h1 h2 l vl,
    vl = vloc l ->
    ~ Fmap.indom h1 l ->
    h2 = Fmap.update h1 l vuninit ->
    satisfies s1 s1 h1 h2 (ok vl) alloc

  | s_write : forall s1 h1 h2 l v vl,
    vl = vloc l ->
    Fmap.indom h1 l ->
    Fmap.read h1 l <> vfreed ->
    h2 = Fmap.update h1 l v ->
    satisfies s1 s1 h1 h2 (ok vunit) (write vl v)

  | s_write_err : forall s1 h1 l v vl,
    vl = vloc l ->
    Fmap.indom h1 l ->
    Fmap.read h1 l = vfreed ->
    satisfies s1 s1 h1 h1 err (write vl v)

  | s_read : forall s1 h1 (l:loc) (v vl:val),
    vl = vloc l ->
    Fmap.indom h1 l ->
    Fmap.read h1 l = v ->
    v <> vfreed ->
    v <> vuninit ->
    satisfies s1 s1 h1 h1 (ok v) (read vl)

  | s_read_err : forall s1 h1 (l:loc) (v vl:val),
    vl = vloc l ->
    Fmap.indom h1 l ->
    Fmap.read h1 l = v ->
    (v = vfreed \/ v = vuninit) ->
    satisfies s1 s1 h1 h1 err (read vl)

  .

Notation "s1 ',' s2 ','  h1 ','  h2 ','  r  '|=' f" :=
  (satisfies s1 s2 h1 h2 r f) (at level 30, only printing).

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
  | H: ok _ = ok _ |- _ => injects H; heaps
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
  satisfies s1 s3 h1 h3 (ok r1) f1 ->
  satisfies s3 s2 h3 h2 R f2 ->
  satisfies s1 s2 h1 h2 R (seq f1 f2).
Proof.
  unfold seq. intros.
  applys* s_bind.
Qed.

(* Notation s_seq_sh := s_bind_sh. *)

Lemma s_ens_ : forall H h1 h2 s1,
  (exists h3,
    H h3 /\
    h2 = Fmap.union h1 h3 /\
    Fmap.disjoint h1 h3) ->
  satisfies s1 s1 h1 h2 (ok vunit) (ens_ H).
Proof.
  unfold ens_. intros.
  applys* s_ens.
  heaps.
Qed.

(* possibly needs to be made primitive because l should be fresh, not in current heap *)
(* also definitions like these would need to identify precondition failure with error, which we had trouble with before *)

(* Definition alloc : flow :=
  req \[] (ens (fun r => \exists l, l~~>vuninit \* \[r = l])).

Definition free l : flow :=
  ∀ v, req (l~~>v) (ens_ (l~~>vfreed)).

Definition read l : flow :=
  ∀ v, req (l~~>v) (ens (fun r => l~~>v \* \[r = v])).

Definition write l v1 : flow :=
  ∀ v, req (l~~>v) (ens_ (l~~>v1)). *)

Definition entails (f1 f2:flow) : Prop :=
  forall s1 s2 h1 h2 R,
    satisfies s1 s2 h1 h2 R f1 -> satisfies s1 s2 h1 h2 R f2.

(** * Entailed by, the dual of entailment *)
Definition entailed (f1 f2:flow) : Prop :=
  forall s1 s2 h1 h2 R,
    satisfies s1 s2 h1 h2 R f2 -> satisfies s1 s2 h1 h2 R f1.

(* for all states in post, exists state in pre s.t. eval goes from pre to pos *)
(* Definition entailed (f1 f2:flow) : Prop :=
  forall s2 h2 R,
  exists s1 h1,
    satisfies s1 s2 h1 h2 R f1 ->
    satisfies s1 s2 h1 h2 R f1. *)

Infix "⊒" := entailed (at level 90, right associativity) : flow_scope.
(* Infix "⊑" := entailed (at level 90, right associativity) : flow_scope. *)

Example ex1:
  entailed (bind alloc read) (bind alloc (fun _ => error)).
Proof.
  unfold entailed. intros.
  inverts H. 2: { inverts H6. }
  inverts H7.
  inverts H8.
  applys s_bind.
  applys* s_alloc.
  applys* s_read_err.
  applys indom_update.
  right. rew_fmap. reflexivity.
Qed.

Example ex2:
  entails (bind alloc read) error.
Proof.
  unfold entails. intros.
  inverts H.
  2: { inverts H6. }
  inverts H7.
  inverts H8.
  {
  injects H0.
  rew_fmap.
  false H11. reflexivity.
  }
  { injects H0.
  rew_fmap.
  destruct H10.
  inverts H.
  (* problem: error does not change the heap, so this is the wrong way to state the spec *)
  Fail applys s_error.
Abort.

Instance entailed_refl : Reflexive entailed.
Proof.
  unfold Reflexive, entailed.
  intros.
  exact H.
Qed.

Instance entailed_trans : Transitive entailed.
Proof.
  unfold Transitive, entailed.
  intros.
  auto.
Qed.

Instance entailed_preorder : PreOrder entailed.
Proof.
  constructor.
  apply entailed_refl.
  apply entailed_trans.
Qed.

(* Instance bientails_equiv : Equivalence bientails.
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
Qed. *)
