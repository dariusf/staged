
(* Require Import msl.msl_standard. *)
(* Require Import msl.knot_hered. *)
(* Require Import msl.functors. *)
Require Import msl.base.
(* Require Import msl.functors. *)
(* Require Import msl.functor_facts. *)
(* Require Import msl.knot. *)
Require Import msl.knot_hered.
Require Import msl.knot_prop.


Require Import msl.functors.
Require Import msl.ageable.

Import CovariantFunctor.
Import CovariantFunctorLemmas.
Import CovariantFunctorGenerator.

From Coq Require Import Classes.RelationClasses.
From Coq Require Morphisms Program.Basics.

From Staged Require Export HeapF.
From Staged Require Export LibFmap.
From Staged Require Export ExtraTactics.

Local Open Scope string_scope.
(* Local Open Scope nat_scope. *)
Local Open Scope Z_scope.
Local Open Scope list_scope.

Set Implicit Arguments.
Definition var : Type := string.
Notation var_eq := String.string_dec.

Definition loc := nat.

Inductive val :=
  | vunit : val
  | vint : Z -> val
  | vfptr : var -> val.

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

(* Locate TY_FUNCTOR_PROP. *)

Module TFP <: TY_FUNCTOR_PROP.
  (* Definition T := Prop. *)
  (* Definition T_bot := False. *)

  Definition F1 : Type -> Type :=
    (* fun X => var -> heap -> heap -> val -> X. *)
    fun X => var -> X.

  (* Definition fmap : forall A B, (A -> B) -> F1 A -> F1 B :=
    fun A B (g : A -> B) (psi : F1 A) =>
    fun x h1 h2 v =>
      g (psi x h1 h2 v). *)

  Definition fmap : forall A B, (A -> B) -> F1 A -> F1 B :=
    fun A B (g : A -> B) (psi : F1 A) =>
    fun x =>
      g (psi x).

  Lemma fmap_id : forall A, fmap (id A) = id (F1 A).
  Proof.
    unfold fmap, id, compose, option_map.
    intro.
    extensionality FA a.
    (* extensionality FB v. *)
    reflexivity.
  Qed.

  Lemma fmap_comp : forall A B C (f:B -> C) (g:A -> B),
    fmap f oo fmap g = fmap (f oo g).
  Proof.
    unfold fmap, id, compose, option_map.
    intros.
    extensionality FA a.
    (* extensionality FB b. *)
    reflexivity.
  Qed.

  Definition F :=
    {| _functor := F1;
      CovariantFunctor.fmap := fmap;
      functor_facts :=
        {| ff_id := fmap_id;
          ff_comp := fmap_comp |} |}.

  Definition other : Type := heap * heap * val.
End TFP.

Export TFP.


Module K := KnotProp(TFP).
(* Module KL := KnotProp_Lemmas(K). *)

(* Module K := KnotHered(TFP). *)
(* Module KL := KnotHered_Lemmas(K). *)

Export K.
(* Export KL. *)

Variant result : Type :=
| norm : val -> result
| shift : var -> var -> result.

Definition env : Type := knot.
Definition flow : Type := env -> env -> heap -> heap -> val -> Prop.

Definition ens (Q:val->hprop) : flow :=
  fun s1 s2 h1 h2 v =>
    exists v1 h3,
      v1 = v /\
      Q v1 h3 /\
      h2 = Fmap.union h1 h3 /\
      Fmap.disjoint h1 h3.

Definition req (H:hprop) (f:flow) : flow :=
  fun s1 s2 h1 h2 v =>
    forall (hp hr:heap),
      H hp ->
      h1 = Fmap.union hr hp ->
      Fmap.disjoint hr hp ->
      f s1 s2 hr h2 v.

Definition unk (f:var) (v:val) : flow :=
  fun s1 s2 h1 h2 v =>
    let (k, env) := unsquash s1 in
    let f1 := env f in
    (* let f2 := proj1_sig f1 in *)
    let f2 := f1 in
    (* TODO does not have to be hereditary because the env is never updated? *)
    (* TODO later s? otherwise we get a meaningless env *)
    let f3 := f2 (s1, (h1, h2, v)) in
    f3.

Definition bind (f:flow) (fk:val->flow) : flow :=
  fun s1 s2 h1 h2 v =>
    forall h3 v1,
      f s1 s2 h1 h3 v1 ->
      (fk v1) s1 s2 h3 h2 v.

Definition seq (f1 f2:flow) : flow :=
  bind f1 (fun _ => f2).

Definition ens_ (H:hprop) : flow :=
  ens (fun r => H \* \[r = vunit]).

Definition ret (v:val) : flow :=
  ens (fun r => \[r = v]).


Lemma val_eq_dec : forall (x1 x2 : val), {x1 = x2} + {x1 <> x2}.
Proof.
  decide equality.
  apply Z.eq_dec.
  apply String.string_dec.
Defined.

  (* Locate "=?". *)
  (* Locate eqb. *)

Definition p2f (p:predicate) : flow :=
  fun s1 s2 h1 h2 v =>
  (* TODO s2 *)
    p (s1, (h1, h2, v)).

Definition f2p (f:flow) : predicate :=
  fun '(s1, (h1, h2, v)) =>
  (* TODO s2 *)
    f s1 s1 h1 h2 v.

Definition defun (f:var) (fk:val->flow) : flow :=
  fun s1 s2 h1 h2 v =>
  h1 = h2 /\ v = vunit /\
  let s3 := s1 in
  let (k, env) := unsquash s3 in
  let _ : var->predicate := env in
  let y : var->predicate := fun f1 =>
  (* f2p (fk ) *)
    (* fun '(s4, (h3, h4, v1)) => *)
    (* TODO convert a val->flow into a var->predicate *)
    fun '(s3, (h3, h4, v)) => exists (f2:val), f2 = vfptr f1 /\
      fk f2 s3 s3 h3 h4 v
  in
  let z : var->predicate := fun x =>
    if var_eq x f then y x else env x
  in
  (* let w :=  in *)
  (* let y:predicate :=
  fun '(s1, (h1, h2, v)) =>
  (fun (v1:var) => if var_eq v1 f then f2p (fk (vfptr f)) else env v1) in *)
  (* s2 = (fun k => if k = f then fk else env k) *)
  (* 1 *)
  s2 = squash (k, z)
  .

(* Definition effect (v:var) : flow :=
  ens (fun r => \[r = v]). *)

Definition entails (f1 f2:flow) : Prop :=
  forall s1 s2 h1 h2 v,
    f1 s1 s2 h1 h2 v ->
      f2 s1 s2 h1 h2 v.

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


Example ex1 : forall x,
  entails (ens_ \[x = 1]) (ens_ \[x >= 1]).
Proof.
  unfold entails. intros.
  unfold ens_, ens in *.
  destr H. hinv H. hinv H. hinv H2.
  exs.
  splits*.
  subst.
  hintro.
  hintro. lia.
  hintro. reflexivity.
  fmap_disjoint.
Qed.

Example ex2 : forall f v,
  entails (unk f v) (unk f v).
Proof.
  reflexivity.
Qed.

Check age1.
Search "age".

Print TF.F.
(* the functor F we defined in the module above *)
Locate TF.F.
Print predicate.
