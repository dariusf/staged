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
Implicit Types v: val.

(** * Types *)
Inductive type :=
  | tvar : var -> type
  | ttop : type
  | tbot : type
  | tint : type
  | tsingle : val -> type
  | tfix : var -> type -> type
  | tunion : type -> type -> type
  | tconstr0 : string -> type
  | tconstr1 : string -> type -> type
  | tconstr2 : string -> type -> type -> type
  .

Fixpoint tsubst (y:var) (w:type) (e:type) : type :=
  let aux t := tsubst y w t in
  let if_y_eq x t1 t2 := if var_eq x y then t1 else t2 in
  match e with
  | tvar x => if_y_eq x w e
  | ttop => e
  | tbot => e
  | tint => e
  | tsingle _ => e
  | tunion t1 t2 => tunion (aux t1) (aux t2)
  | tfix x t1 =>
    tfix x (if_y_eq x t1 (aux t1))
  | tconstr0 _ => e
  | tconstr1 s t => tconstr1 s (aux t)
  | tconstr2 s t1 t2 => tconstr2 s (aux t1) (aux t2)
  end.

Inductive has_type : val -> type -> Prop :=

  | d_ttop : forall v,
    has_type v ttop

  (* no case for bot *)

  | d_tint : forall i,
    has_type (vint i) tint

  | d_tsingle : forall v v1,
    v = v1 ->
    has_type v (tsingle v1)

  | d_tfix : forall x v t,
    has_type v (tsubst x (tfix x t) t) ->
    has_type v (tfix x t)

  | d_tunion_l : forall v t1 t2,
    has_type v t1 ->
    has_type v (tunion t1 t2)

  | d_tunion_r : forall v t1 t2,
    has_type v t2 ->
    has_type v (tunion t1 t2)

  | d_tconstr0 : forall s,
    has_type (vconstr0 s) (tconstr0 s)

  | d_tconstr1 : forall s t1 v1,
    has_type v1 t1 ->
    has_type (vconstr1 s v1) (tconstr1 s t1)

  | d_tconstr2 : forall s v1 v2 t1 t2,
    has_type v1 t1 ->
    has_type v2 t2 ->
    has_type (vconstr2 s v1 v2) (tconstr2 s t1 t2)

  .

Definition subtype : type -> type -> Prop := fun t1 t2 =>
  forall v, has_type v t1 -> has_type v t2.


Definition tlist t : type :=
  tfix "list" (tunion (tconstr0 "nil") (tconstr2 "cons" t (tvar "list"))).

Definition vcons a b : val := vconstr2 "cons" a b.
Definition vnil : val := vconstr0 "nil".


Module Examples.

Example ex_list: has_type (vcons (vint 1) (vcons (vint 2) vnil)) (tlist tint).
Proof.
  unfold vcons, vnil, tlist.

  apply d_tfix. simpl.
  apply d_tunion_r.
  apply d_tconstr2.
  apply d_tint.

  apply d_tfix. simpl.
  apply d_tunion_r.
  apply d_tconstr2.
  apply d_tint.

  apply d_tfix. simpl.
  apply d_tunion_l.
  apply d_tconstr0.
Qed.

(* A lemma like this would be in the context if there is a value of [List +A]. *)
Lemma list_covariance: forall t1 t2,
  subtype t1 t2 ->
  subtype (tlist t1) (tlist t2).
Proof.
  unfold tlist. intros.
  unfold subtype. intros.
  inverts H0 as H0. simpl in H0.
  apply d_tfix. simpl.
  inverts H0 as H0.
  { apply d_tunion_l. assumption. }
  { apply d_tunion_r.
    inverts H0 as H0.

    apply d_tconstr2.
    admit.
    admit. }
Admitted.

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
