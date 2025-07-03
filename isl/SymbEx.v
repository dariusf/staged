
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
  (* | vtup : val -> val -> val *)
  (* | vstr : string -> val *)
  (* | vbool : bool -> val *)
  (* | vlist : list val -> val *)
  (* | vfptr : var -> val *)
  | vvar : var -> val
  | verror : val
  | vuninit : val
  | vfreed : val

with expr : Type :=
  (* | pvar (x: var) *)
  | pval (v: val)
  | prefmut (e: expr)
  | pref (e: expr)
  | plet (x: var) (e1 e2:expr)
  | pletmut (x: var) (e1 e2:expr)
  (* | pseq (e1 e2: expr) *)
  | passume (e: expr)
  | pchoice (e1: expr) (e2: expr)
  | prepeat (e: expr)
  | papp (e1: expr) (e2: expr)

  | padd (v1 v2: val)

  (* | plet (x: var) (e1 e2: expr) *)
  (* | pfix (xf: var) (x: var) (e: expr) *)
  (* | pfun (x: var) (e: expr) *)
  (* | pfst (e: expr) *)
  (* | psnd (e: expr) *)
  (* | pminus (e1 e2: expr) *)
  (* | passert (e: expr) *)
  (* | pref (e: expr)
  | pderef (e: expr)
  | passign (e1: expr) (e2: expr)
  | pfree (e: expr) *)
  (* | pif (v: expr) (e1: expr) (e2: expr) *)
  .

(* Definition padd (e1 e2 : expr) : expr :=
  match e1, e2 with
  | pval (vint i1), pval (vint i2) => pval (vint (i1 + i2))
  | _, _ => pval vunit
  end. *)

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

(* Definition vbop f a b :=
  match a, b with
  | vbool a1, vbool b1 => f a1 b1
  | _, _ => vunit
  end. *)

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

(* Definition vand (a b:val) :=
  match a, b with
  | vbool true, _ => b
  | vbool false, _ => vbool false
  | _, vbool false => vbool false
  | _, vbool true => a
  | _, _ => vunit
  end. *)

#[global]
Instance Inhab_val : Inhab val.
Proof.
  constructor.
  exists vunit.
  constructor.
Qed.

(* Coercion vint : Z >-> val.
Coercion vbool : bool >-> val. *)

Fixpoint subst (y:var) (v:val) (e:expr) : expr :=
  let aux t := subst y v t in
  let if_y_eq x t1 t2 := if var_eq x y then t1 else t2 in
  match e with
  | pval v => pval v
  (* | padd e1 e2 => padd (aux e1) (aux e2) *)
  | padd v1 v2 => padd v1 v2
  (* | pminus x z => pminus x z *)
  (* | pfst x => pfst x *)
  (* | psnd x => psnd x *)
  (* | pvar x => if_y_eq x (pval v) e *)
  (* | passert b => passert (aux b) *)
  (* | pderef r => pderef (aux r) *)
  (* | passign x z => passign (aux x) (aux z) *)
  | pref v => pref (aux v)
  | prefmut v => prefmut (aux v)
  | passume e => passume (aux e)
  (* | pfun x t1 => pfun x (if_y_eq x t1 (aux t1)) *)
  (* | pfix f x t1 => pfix f x (if_y_eq f t1 (if_y_eq x t1 (aux t1))) *)
  | papp e1 e2 => papp (aux e1) (aux e2)
  | plet x t1 t2 => plet x (aux t1) (if_y_eq x t2 (aux t2))
  | pletmut x t1 t2 => pletmut x (aux t1) (if_y_eq x t2 (aux t2))
  (* | pif t0 t1 t2 => pif (aux t0) (aux t1) (aux t2) *)
  | pchoice t1 t2 => pchoice (aux t1) (aux t2)
  | prepeat e => prepeat (aux e)
  (* | pshift e => pshift (fun k => aux (e k)) *)
  (* | preset e => preset (aux e) *)
  end.

Module Val.
  Definition value := val.
End Val.

Module Export Heap := HeapF.HeapSetup Val.

Definition empty_heap : heap := Fmap.empty.

(* Definition postcond := val -> hprop. *)
Definition postcond : Type := val * hprop.

Inductive result : Type :=
  | ok : result
  | err : result.

Definition spec : Type := hprop * result * hprop.

#[global]
Instance Inhab_spec : Inhab spec.
Proof.
  constructor.
  exists (\[], ok, \[]).
  constructor.
Qed.

Definition senv := fmap var spec.

(* [biab m p q f] means [m * p =| q * f].
  frame is abduced, antiframe (missing) is anti-abduced *)
Inductive biab : hprop -> hprop -> hprop -> hprop -> Prop :=

  | b_trivial : forall H,
    biab \[] H H \[]

  | b_base_empty_l : forall Hf,
    biab \[] Hf \[] Hf

  | b_base_empty_r : forall Ha,
    biab Ha \[] Ha \[]

  | b_base : forall Hf Ha,
    biab Ha Hf Ha Hf

  | b_match : forall a H1 H2 Ha Hf l,
    biab Ha H1 H2 Hf ->
    biab Ha (l~~>a \* H1) (l~~>a \* H2) Hf

  | b_match_neq : forall a b H1 H2 Ha Hf l,
    biab Ha H1 H2 Hf ->
    biab Ha (l~~>a \* H1) (l~~>b \* H2) (\[a=b] \* Hf)

  | b_move_l : forall H1 H2 Ha Hf H,
    biab Ha H1 H2 (H \* Hf) ->
    biab Ha H1 (H \* H2) Hf

  | b_move_r : forall H1 H2 Ha Hf H,
    biab (H \* Ha) H1 H2 Hf ->
    biab Ha (H \* H1) H2 Hf
  .

Lemma biab_sound: forall m p q f,
  biab m p q f ->
  q \* f ==> m \* p.
Proof.
  introv Hbiab.
  induction Hbiab.
  { xsimpl. }
  { xsimpl. }
  { xsimpl. }
  { xsimpl. }
  { rewrite hstar_assoc.
    xchange IHHbiab.
    xsimpl. }
  { rewrite hstar_assoc.
    xchange IHHbiab.
    xsimpl. auto. }
  { rewrite hstar_assoc.
    xchange IHHbiab. }
  { xchange IHHbiab. xsimpl. }
Qed.

(* BiabDiscover(y→Y * v→V * z→Z ∧Z= nil, y→Y * z→Z * Y →W ),
which yields {(m, f)}with m ≡ Y→W and f≡v→V∧Z=nil. *)
Example ex_biab: forall y Y z Z v V W nil, exists m f,
  biab m
    (y~~>vloc Y \* z~~>Z \* v~~>V \* \[Z=nil])
    (y~~>vloc Y \* z~~>Z \* Y~~>W) f
  /\ m = Y~~>W /\ f = v~~>V \* \[Z = nil].
Proof.
  intros. exs.
  split.
  applys b_match.
  applys b_match.
  applys b_base.
  auto.
Qed.


Implicit Types H : hprop.
Implicit Types Q : postcond.
Implicit Types v : val.
Implicit Types e : expr.
Implicit Types R : result.
Implicit Types s : senv.

(* the eval function: (senv, pre, e) -> (ok/err, missing, post) *)
Inductive eval : senv -> hprop -> expr -> result -> hprop -> postcond -> Prop :=
  | e_val : forall s H v,
    eval s H (pval v) ok \[] (v, H)

  | e_add : forall s H v1 v2,
    eval s H (padd v1 v2) ok \[] (vadd v1 v2, H)

  | e_let : forall s H e1 e2 R m1 m2 Q Hq x v,
    eval s H e1 ok m1 (v, Hq) ->
    eval s Hq (subst x v e2) R m2 Q ->
    eval s H (plet x e1 e2) R (m1 \* m2) Q

  (* | e_bind : forall s p e1 e2 R m1 m2 q q1,
    eval s p e1 ok m1 q1 ->
    eval s q1 e2 R m2 q ->
    eval s p (pseq e1 e2) R (m1 \* m2) q

  | e_bind_err : forall s p e1 e2 R m q,
    eval s p e1 err m q ->
    eval s p (pseq e1 e2) R m q

  | e_choice_l : forall s p e1 e2 R m q,
    eval s p e1 R m q ->
    eval s p (pchoice e1 e2) R m q

  | e_choice_r : forall s p e1 e2 R m q,
    eval s p e2 R m q ->
    eval s p (pchoice e1 e2) R m q

  | e_fn : forall s p e R m (f:var) F A p1 q1,
    Fmap.read s f = (p1, R, q1) ->
    biab m p A F ->
    eval s p (papp (pvar f) e) R m (q1 \* F) *)




  (* | e_ref : forall p e R m q,
    eval p (pref e) R m q *)

  (* | e_deref : forall p e R m q,
    eval p e1 err m q ->
    eval p (pderef e) R m q *)

  .


Declare Scope expr_scope.
Open Scope expr_scope.

(* Infix ";;" := pseq (at level 38, right associativity) : expr_scope. *)

(* Notation "'let' x '=' f1 'in' f2" :=
  (bind f1 (fun x => f2))
  (at level 38, x binder, right associativity, only printing) : expr_scope. *)

Definition default_env : senv := Fmap.empty.

Example e0: exists R m q,
  eval default_env \[]
  (pval (vint 1)) R m q
  /\ R = ok
  /\ m = \[]
  /\ q = (vint 1, \[]).
Proof.
  exs. split.
  applys e_val.
  splits*.
Qed.

Example e0_let: exists R m q,
  eval default_env \[]
  (plet "x" (pval (vint 1)) (padd (vvar "x") (vint 2))) R m q
  /\ R = ok
  /\ m = \[]
  /\ q = (vint 1, \[]).
Proof.
  exs. split.
  applys e_let.
  - applys e_val.
  - simpl.
    applys e_add.
    splits*.
    xsimpl.
  (* apply fun_ext_dep. intros. xsimpl*. *)
Qed.

(* Definition pref e := papp (pvar "ref") e.
Definition pderef e := papp (pvar "deref") e.
Definition passign e := papp (pvar "assign") e.
Definition pfree e := papp (pvar "free") e. *)

(* Definition spec_alloc_1 := (\[], ok, \exists l, l~~>vuninit).
Definition spec_free := (\forall l v, l~~>v, ok, \[]).
Definition spec_deref := (\forall l v, l~~>v, ok, \exists l v1, l~~>v1).

Definition default_env :=
  Fmap.update (Fmap.single "free" spec_free) "ref" spec_alloc_1. *)

Example e1: exists R m q,
  eval default_env \[]
  (pref (pval (vint 1))) R m q
  /\ R = ok
  /\ m = \[]
  /\ q = \exists l, l ~~> vuninit.
Proof.
  exs. split.
  applys e_fn.
    { unfold default_env. resolve_fn_in_env. }
    { applys b_trivial. }
  splits*. xsimpl.
Qed.

Example e2: forall l, exists R m q,
  eval (Fmap.single "deref" spec_deref) (l~~>vint 1)
  (pderef (pval (vloc l))) R m q
  /\ R = ok
  /\ m = \[]
  /\ q = \exists l v, l ~~> v.
Proof.
  intros. exs. split.
  (* TODO allow picking a different spec. maybe not with an env *)
  applys e_fn.
    { unfold default_env. resolve_fn_in_env. }
    { applys b_trivial. }
  splits*. xsimpl.
Qed.
