
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

Coercion vint : Z >-> val.
Coercion vbool : bool >-> val.

Module Val.
  Definition value := val.
End Val.

Module Export Heap := HeapF.HeapSetup Val.

Definition empty_heap : heap := Fmap.empty.

Definition postcond := val -> hprop.

Section flow.
  Variable var : Type.

  (* a lambda calculus-like version of φ.
    deep embedding of syntax, but shallow embedding of binders. *)
  Inductive flow : Type :=
    | req : hprop -> flow -> flow
    | ens : postcond -> flow
    | ident : var -> flow
    | lambda : (var -> flow) -> flow
    | app : flow -> flow -> flow
    | bind : flow -> (val -> flow) -> flow
    | fex : forall (A:Type), (A -> flow) -> flow
    | fall : forall (A:Type), (A -> flow) -> flow
    .
End flow.

(* closed terms *)
Definition flow0 := forall V, flow V.

(* terms with one free variable *)
Definition flow1 := forall V, V -> flow V.

(* a constructor for a closed term *)
Example app0 (f1 f2: flow0) : flow0 := fun _ =>
  app (f1 _) (f2 _).

(* constructors for open terms, which have to be defined this way *)
Example identity {V} : flow V :=
  lambda (fun x => ident x).

Definition ret {V} (v:val): flow V :=
  ens _ (fun r => \[r = v]).

Example app2 : flow0 := fun _ =>
  app identity (ret (vint 1)).

Inductive satisfies {V} : heap -> heap -> val -> flow V -> Prop :=

  | s_req : forall H (h1 h2:heap) R (f:flow V),
    (forall (hp hr:heap),
      H hp ->
      h1 = Fmap.union hr hp ->
      Fmap.disjoint hr hp ->
      satisfies hr h2 R f) ->
    satisfies h1 h2 R (req H f)

  | s_ens : forall Q h1 h2 R,
    (exists v h3,
      R = v /\
      Q v h3 /\
      h2 = Fmap.union h1 h3 /\
      Fmap.disjoint h1 h3) ->
    satisfies h1 h2 R (ens _ Q)

  | s_bind : forall h3 v f1 (f2:val->flow V) h1 h2 R,
    satisfies h1 h3 v f1 ->
    satisfies h3 h2 R (f2 v) ->
    satisfies h1 h2 R (bind f1 f2)

  | s_fex h1 h2 R (A:Type) (f:A->flow V)
    (H: exists b,
      satisfies h1 h2 R (f b)) :
    satisfies h1 h2 R (@fex _ A f)

  | s_fall h1 h2 R (A:Type) (f:A->flow V)
    (H: forall b,
      satisfies h1 h2 R (f b)) :
    satisfies h1 h2 R (@fall _ A f)

(* this case probably needs type info *)

  (* | s_app : forall h1 h2 R (f1 f2:flow V) (f3:V->flow V),
    f1 = lambda f3 ->
    satisfies h1 h2 R (f3 f2) ->
    satisfies h1 h2 R (@app _ f1 f2) *)

.

(*
  http://adam.chlipala.net/cpdt/html/Hoas.html
  https://xavierleroy.org/mpri/2-4/mechanization.pdf
  http://adam.chlipala.net/cpdt/html/OpSem.html
*)