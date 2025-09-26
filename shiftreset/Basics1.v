
From Stdlib Require Import Classes.RelationClasses.
From Stdlib Require Morphisms Program.Basics.
From Stdlib Require Import Lia.

From Staged Require Export HeapF.
From Staged Require Export LibFmap.
From Staged Require Export ExtraTactics.

Local Open Scope string_scope.
Local Open Scope nat_scope.
(* Local Open Scope Z_scope. *)
Local Open Scope list_scope.

From Stdlib Require Import Program.Equality.
From Stdlib Require Import Logic.FunctionalExtensionality.

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

Coercion vint : Z >-> val.
Coercion vbool : bool >-> val.

Module Val.
  Definition value := val.
End Val.

Module Export Heap := HeapF.HeapSetup Val.

Definition empty_heap : heap := Fmap.empty.

Definition postcond := val -> hprop.

Module Types.

  (*

  Type_0 = Unit
  StoreType_k = Loc ->fin Type_k
  Type_k+1 = StoreType_k * val -> Prop

  t in Type_0 iff t={}
  t in Type_k+1 iff forall (j, env, v) in t, j <= k /\ env in StoreType_j

  env in StoreType_k iff forall l in dom(env), env(l) in Type_k

  *)

  Fixpoint iflow : nat -> Type :=
    fun k =>
      match k with
      | O => unit
      | S j => (iflow j * ((var -> iflow j) -> (var -> iflow j) -> Prop))%type
      end.

  Definition env : nat -> Type :=
    fun k =>
      var -> iflow k.

  Definition flow : Type := forall k, iflow k.

  Definition IT : iflow O :=
    tt.

  Definition ref (tau : flow) : flow :=
    nat_rect iflow IT
      (fun k tauk => (tauk, fun s1 s2 => True))
    .

End Types.

Fixpoint iflow : nat -> Type :=
  fun k =>
    match k with
    | O => unit
    | S j =>
      (iflow j *
        ((var -> (val -> iflow j)) -> (var -> (val -> iflow j)) -> heap -> heap -> val -> Prop))%type
    end.

Definition env : nat -> Type :=
  fun k =>
    var -> (val -> iflow k).

Definition flow : Type := forall k, iflow k.

Definition itrue : iflow O := tt.

Notation satisfies_at k f s1 s2 h1 h2 v :=
  (snd (f (S k)) s1 s2 h1 h2 v).

Definition ens (Q:val->hprop) : flow :=
  nat_rect iflow itrue
    (fun k tauk => (tauk, fun s1 s2 h1 h2 v =>
      exists (* v1 *) h3,
        (* R = norm v /\ *)
        (* v1 = v /\ *)
        Q v h3 /\
        h2 = Fmap.union h1 h3 /\
        Fmap.disjoint h1 h3
      ))
  .

(* Compute (ens (fun r => \[]) 2). *)

Definition req (H:hprop) (f:flow) : flow :=
  nat_rect iflow itrue
    (fun k (tauk:iflow k) =>
      (tauk, fun (s1 s2:env k) h1 h2 v =>
        forall (hp hr:heap),
          H hp ->
          h1 = Fmap.union hr hp ->
          Fmap.disjoint hr hp ->
          satisfies_at k f s1 s2 h1 h2 v
        ))
  .

Definition bind (f1:flow) (f2:val->flow) : flow :=
  nat_rect iflow itrue
    (fun k (tauk:iflow k) =>
      (tauk, fun (s1 s2:env k) h1 h2 v =>
          forall s3 h3 v1 v,
            satisfies_at k f1 s1 s3 h1 h3 v1 ->
            satisfies_at k (f2 v1) s3 s2 h3 h2 v
        ))
  .

Definition seq (f1 f2:flow) : flow :=
  bind f1 (fun _ => f2).

Infix ";;" := seq (at level 38, right associativity).

(* Lemma approx_env : forall k j:nat, j < k ->
  env k -> env j.
Proof.
  unfold env.
  (* intros. *)
  (* unfold iflow. *)
Admitted. *)

(* Definition approx_env : forall (k j:nat) (H:j < k),
  env k -> env j :=
  (fun v j H s1 => fun v x => 1)
. *)

(* Search (_ < _ -> exists _, _). *)

(* Nat.lt_exists_pred: *)

(* Program Definition approx_flow : forall (k j:nat) (H:j<k),
  iflow k -> iflow j :=
  fun k j f1 => _.
Next Obligation.
lets H: Nat.lt_exists_pred f1.
Admitted. *)


(* Locate LibOrder.lt.
Print LibOrder.lt.
Locate "<". *)

(* Check lt_dec. *)

(* Definition approx_flow : forall (k j:nat)
  (H:j<k)
  (* (lt_dec j k) -> *)
, iflow k -> iflow j :=
  fun k j H f1 =>
    (* match k with
    | O => True
    | S k1 =>

    end *)
    (* fun x v1 => *)
    (* let y := s1 x v1 in *)
      (* 1 *)
      True
      . *)


Check le_dec.
(* Search sumbool. *)
Check eq_nat_decide.
(* Check eqb_dec. *)

Definition approx_flow (k j : nat) : j<k -> iflow k -> iflow j.
(* := *)
Proof.
  intros H_lt f.
  induction k as [| k' IHk'].
  - exfalso.
    exact (Nat.nlt_0_r j H_lt).
  - unfold "<" in H_lt.
    destruct (le_lt_eq_dec _ _ H_lt) as [H_cmp | H_cmp].
    + rewrite <- Nat.succ_lt_mono in H_cmp.
      exact (IHk' H_cmp (fst f)).
    + injection H_cmp as H_cmp.
      rewrite <- H_cmp in f.
      exact (fst f).
Defined.

(*
Search (0 < _).
Compute (approx_flow Nat.lt_1_2 (ens (fun _ => \[]) 2)).
*)

(* fun f1 =>
if eq_nat_decide k j then
else if lt_dec k j then
  else



match k with
| O => itrue
end *)

(* Definition env : nat -> Type :=
  fun k =>
    var -> (val -> iflow k). *)

Definition approx_env : forall (k j:nat), j<k -> env k -> env j.
Proof.
  intros k j H_lt s1 x v.
  exact (approx_flow H_lt (s1 x v)).
Defined.


Definition unk (f:var) (v:val) : flow.
Proof.
  intros k.
  induction k as [| k'].
  - constructor.
  -
  constructor.
  assumption.
  intros s1 s2 h1 h2 v1.
  lets uf: s1 f v.
  destruct k'.
  + exact True.
  + set (s1' := @approx_env (S k') k' (Nat.lt_succ_diag_r _) s1).
    set (s2' := @approx_env (S k') k' (Nat.lt_succ_diag_r _) s2).
    exact ((snd uf) s1' s2' h1 h2 v).
Defined.

Compute (unk "x" vunit) 2.

(* Notation satisfies_at k f s1 s2 h1 h2 v :=
  (snd (f (S k)) s1 s2 h1 h2 v). *)


  (* Check satisfies_at. *)
  (* lets: satisfies_at k uf s1 s2 h1 h2 v. *)
  (* unfold iflow in uf. *)
  (* lets uf: s1 f v. *)
  (* Check (satisfies_at k uf s1 s2 h1 h2 v). *)

  (* Check (snd (uf (S k)) s1 s2 h1 h2 v). *)

  (* exact (satisfies_at k f s1 s2 h1 h2 v). *)


  (* destruct k.
   (* eqn:Hjk. *)
  + exact True.
  + *)
    (* rewrite <- Hjk in IHk. *)





  (* nat_rect iflow itrue
    (fun k (tauk:iflow k) =>
      (tauk, fun (s1 s2:env k) h1 h2 v1 =>
        forall uf,
          (* Fmap.read *) s1 f = uf ->
          match k as k0 return k = k0 -> Prop with
          | O => fun _ => True
          | S j => fun eq =>
            let y : iflow (S j) := ltac:(subst; exact (uf v)) in
            let z := snd y in
            (* let s3 := @approx_env k j _ s1 in *)
            (* satisfies_at j y s1 s2 h1 h2 v1 *)
            (* TODO approximate the env down? *)
            True
            (* 1 *)
        end eq_refl
        ))
  . *)


(* Definition unk (f:var) (v:val) : flow :=
  nat_rect iflow itrue
    (fun k (tauk:iflow k) =>
      (tauk, fun (s1 s2:env k) h1 h2 v1 =>
        forall uf,
          (* Fmap.read *) s1 f = uf ->
          match k as k0 return k = k0 -> Prop with
          | O => fun _ => True
          | S j => fun eq =>
            let y : iflow (S j) := ltac:(subst; exact (uf v)) in
            let z := snd y in
            (* let s3 := @approx_env k j _ s1 in *)
            (* satisfies_at j y s1 s2 h1 h2 v1 *)
            (* TODO approximate the env down? *)
            True
            (* 1 *)
        end eq_refl
        ))
  . *)

Definition entails (f1 f2:flow) : Prop :=
  forall k s1 s2 h1 h2 v,
    satisfies_at k f1 s1 s2 h1 h2 v ->
    satisfies_at k f2 s1 s2 h1 h2 v.

Example ex1 :
  entails (ens (fun r => \[r = 1+1]))
    (ens (fun r => \[r = 2])).
Proof.
  unfold entails. intros.
  simpl in *.
  destr H.
  hinv H.
  exists empty_heap.
  splits*.
  subst.
  hintro. reflexivity.
  fmap_eq.
Qed.

Infix "====>" := Morphisms.respectful (at level 80, right associativity).
Notation Proper := Morphisms.Proper.
Notation respectful := Morphisms.respectful.
Notation impl := Program.Basics.impl.
Notation flip := Basics.flip.

#[global]
Instance Proper_entails_entails : Proper
  (flip entails ====> entails ====> impl)
  entails.
Proof.
  unfold flip, Proper, respectful, impl.
  unfold entails. intros. auto.
Qed.

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

Example ex2 :
  entails (ens (fun r => \[r = 1+1]))
    (ens (fun r => \[r = 2])).
Proof.
  rewrite ex1.
  reflexivity.
Qed.
