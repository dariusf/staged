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
  | vconstr0 : string -> val
  | vconstr1 : string -> val -> val
  | vconstr2 : string -> val -> val -> val
  | verr : val
  | vabort : val

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
  | papp (x: expr) (a: expr)
  .

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

Module Export Heap := HeapF.HeapSetup Val.

Implicit Types e: expr.
Implicit Types r v: val.

Inductive bigstep : heap -> expr -> heap -> val -> Prop :=
  | eval_pval : forall h v,
    bigstep h (pval v) h v

  (* there is no var rule *)

  | eval_plet : forall h1 h3 h2 x e1 e2 v Re,
    bigstep h1 e1 h3 v ->
    bigstep h3 (subst x v e2) h2 Re ->
    bigstep h1 (plet x e1 e2) h2 Re

  | eval_padd : forall h x y,
    bigstep h (padd (pval (vint x)) (pval (vint y))) h (vint (x + y))

  | eval_pminus : forall h x y,
    bigstep h (pminus (pval (vint x)) (pval (vint y))) h (vint (x - y))

  | eval_pfun : forall h x e,
    bigstep h (pfun x e) h (vfun x e)

  | eval_pfix : forall h x e xf,
    bigstep h (pfix xf x e) h (vfix xf x e)

  | eval_app_fun : forall v1 v2 h x e Re,
    v1 = vfun x e ->
    bigstep h (subst x v2 e) h Re ->
    bigstep h (papp (pval v1) (pval v2)) h Re

  | eval_app_fix : forall v1 v2 h x e Re xf,
    v1 = vfix xf x e ->
    bigstep h (subst x v2 (subst xf v1 e)) h Re ->
    bigstep h (papp (pval v1) (pval v2)) h Re

  | eval_pif_true : forall h1 h2 Re e1 e2,
    bigstep h1 e1 h2 Re ->
    bigstep h1 (pif (pval (vbool true)) e1 e2) h2 Re

  | eval_pif_false : forall h1 h2 Re e1 e2,
    bigstep h1 e2 h2 Re ->
    bigstep h1 (pif (pval (vbool false)) e1 e2) h2 Re

  | eval_pref : forall h v p,
    ~ Fmap.indom h p ->
    bigstep h (pref (pval v)) (Fmap.update h p v) (vloc p)

  | eval_pderef : forall h p,
    Fmap.indom h p ->
    bigstep h (pderef (pval (vloc p))) h (Fmap.read h p)

  | eval_passign : forall h p v,
    Fmap.indom h p ->
    bigstep h (passign (pval (vloc p)) (pval v)) (Fmap.update h p v) vunit

  | eval_passert : forall h,
    bigstep h (passert (pval (vbool true))) h vunit.

(** * Types *)
Definition type := val -> Prop.
Implicit Types t: type.

(* bot <: err <: t <: ok <: any <: top *)
(* abort <: top *)

Definition tint : type := fun v => exists i, v = vint i.
Definition tbool : type := fun v => exists b, v = vbool b.
Definition ttop : type := fun _ => True.
Definition tbot : type := fun _ => False.
Definition tsingle v1 : type := fun v => v = v1.
Definition tforall A (f:A -> type) : type := fun v => forall x:A, (f x) v.
Definition texists A (f:A -> type) : type := fun v => exists x:A, (f x) v.
Definition tintersect t1 t2 : type := fun v => t1 v /\ t2 v.
Definition tunion t1 t2 : type := fun v => t1 v \/ t2 v.
Definition tnot t : type := fun v => not (t v).
Definition terr : type := tsingle verr.
Definition tabort : type := tsingle vabort.
Definition tany : type := tnot tabort.

Definition vcons a b : val := vconstr2 "cons" a b.
Definition vnil : val := vconstr0 "nil".

Inductive tlist : type -> val -> Prop :=

  | tlist_nil : forall t,
    tlist t vnil

  | tlist_cons : forall vh vt t,
    t vh ->
    tlist t vt ->
    tlist t (vcons vh vt).

Definition tarrow t1 t2 : type := fun vf =>
  forall x e, vf = vfun x e ->
  forall v, t1 v ->
  forall h1 h2 r,
  bigstep h1 (papp (pval (vfun x e)) (pval v)) h2 r -> t2 r.

Declare Scope type_scope.
Open Scope type_scope.

Notation "'∃' x1 .. xn , H" :=
  (texists (fun x1 => .. (texists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '∃' '/ '  x1  ..  xn , '/ '  H ']'") : type_scope.

Notation "'∀' x1 .. xn , H" :=
  (tforall (fun x1 => .. (tforall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '∀' '/ '  x1  ..  xn , '/ '  H ']'") : type_scope.

Definition subtype t1 t2 := forall v, t1 v -> t2 v.
Notation "t1 '<:' t2" := (subtype t1 t2) (at level 40).

Instance subtype_refl : Reflexive subtype.
Proof.
  unfold Reflexive, subtype.
  intros.
  exact H.
Qed.

Instance subtype_trans : Transitive subtype.
Proof.
  unfold Transitive, subtype.
  intros.
  auto.
Qed.

Instance subtype_preorder : PreOrder subtype.
Proof.
  constructor.
  apply subtype_refl.
  apply subtype_trans.
Qed.

Definition tcov : type -> type := fun t1 v =>
  exists t2, t2 <: t1 -> t2 v.
Definition tcontra : type -> type := fun t1 v =>
  exists t2, t1 <: t2 -> t2 v.
Definition tinv : type -> type := fun t1 v => t1 v.
Definition twild := ttop.

(* Instance subtype_refl : Reflexive subtype.
Proof.
  unfold Reflexive, subtype.
  intros.
  exact H.
Qed. *)

Module Examples.

Example ex_list: (tlist tint) (vcons (vint 1) (vcons (vint 2) vnil)).
Proof.
  apply tlist_cons.
  unfold tint. eexists. reflexivity.
  apply tlist_cons.
  unfold tint. eexists. reflexivity.
  apply tlist_nil.
Qed.

Lemma subtype_cov: forall t,
  t <: tcov t.
Proof.
  unfold subtype, tcov. intros.
  eauto.
Qed.

Lemma _list_covariant: forall t,
  tlist t <: tlist (tcov t).
Proof.
  unfold subtype. intros.
  induction H.
  - apply tlist_nil.
  - apply tlist_cons.
    { unfold tcov. intros. exists t. auto. }
    { assumption. }
Qed.

End Examples.

(** * Program specifications *)

(* Even though we use hprop, for pure logic we can just wrap everything in \[P] *)
Definition precond := hprop.
Definition postcond := val -> hprop.

Inductive spec :=
  | req : precond -> spec -> spec
  | ens : postcond -> spec
  | sexists : forall A, (A -> spec) -> spec
  | sforall : forall A, (A -> spec) -> spec
  | scase : spec -> spec -> spec.
