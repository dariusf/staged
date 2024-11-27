(** A minimal, reference formalization of #<a href="https://dl.acm.org/doi/10.1007/978-3-031-71162-6_26">Staged Specification Logic for Verifying Higher-Order Imperative Programs</a># (FM 2024). *)
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

From Coq Require Recdef.

Definition sum_len {A} (ls : (list A * list A)) : nat :=
  length (fst ls) + length (snd ls).



Function interleave3 {A} (ls : (list A * list A))
  {measure sum_len ls} : list A :=
  match ls with
  | (nil, _) => nil
  | (h :: t, l2) => h :: interleave3 (l2, t)
  end.
Proof.
  intros A ls l1 l2 h t -> ->; unfold sum_len; simpl; rewrite Nat.add_comm; trivial with arith.
Defined.


(** * Programs *)
(** The representation of programs and the use of substitution are mostly reused from SLF. *)
Definition var : Type := string.
Definition var_eq := String.string_dec.

Inductive val :=
  | vunit : val
  | vint : Z -> val
  | vval : string -> val
  | vbool : bool -> val
  | vlist : list val -> val

with expr : Type :=
  | pval (v: val)
  | plet (x: var) (e1 e2: expr)
  | pev  (x:var) 
  | passign (x: expr) (v: expr)
  | pif (b: expr) (e1: expr) (e2: expr)
  | papp (x: expr) (a: expr).

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
  | pval (vval x) => if_y_eq x (pval (w)) e
  | pval v => pval v
  | pev x  =>  pev x  
  | passign x y => passign x y
  | papp e v => papp e v
  | plet x t1 t2 => plet x (aux t1) (if_y_eq x t2 (aux t2))
  | pif t0 t1 t2 => pif t0 (aux t1) (aux t2)
  end.

Module Val.
  Definition value := val.
End Val.

Inductive theta :=
  | bot : theta
  | emp : theta
  | any 
  | theta_singleton :  var -> theta
  | seq : theta -> theta -> theta
  | disj : theta -> theta -> theta
  | kleene : theta -> theta.

Inductive future_condition :=
  | fc_singleton : theta -> future_condition
  | conj : future_condition -> future_condition -> future_condition.


Definition fstEv : Type := (var).


(** SLF's heap theory as a functor. *)
Module Export Heap := HeapF.HeapSetup Val.

Definition empty_heap : heap := Fmap.empty.

Definition precond := hprop.
Definition postcond := val -> hprop. 

Definition pre_state  : Type := (hprop * future_condition).
Definition post_state : Type := (postcond * theta * future_condition).

Definition rho : Type := (list fstEv).



Fixpoint nullable (t: theta): bool :=
  match t with
  | bot => false 
  | any => false
  | emp => true 
  | theta_singleton ev => false
  | seq t1 t2 =>  andb (nullable t1) (nullable t2 )
  | disj t1 t2 => orb (nullable t1) (nullable t2)
  | kleene _ => true 
  end.

Fixpoint fst (t: theta): list fstEv :=
  match t with
  | bot => nil
  | emp => nil
  | any => ("_") :: nil
  | theta_singleton ev => (ev) :: nil
  | seq t1 t2 => if (nullable t1) then fst t1 ++ fst t2 else fst t1 
  | disj t1 t2 => fst t1 ++ fst t2
  | kleene t1 => fst t1 
  end. 


Fixpoint theta_der (t:theta) (f:fstEv) : theta := 
  match t with 
  | bot => bot
  | emp => bot
  | any => emp 
  | theta_singleton ev1 => 
    if (String.eqb f ev1) then emp else bot  
  | seq t1 t2 => 
    let temp := seq (theta_der t1 f) t2 in 
    if (nullable t1) then disj temp (theta_der t2 f) else temp
  | disj t1 t2 => disj (theta_der t1 f) (theta_der t2 f)
  | kleene t1 => seq (theta_der t1 f) t 
  end.



Fixpoint sum_theta (t:theta) : nat :=
  match t with
  | bot => 0
  | emp => 0
  | any => 1
  | theta_singleton ev1 => 1 
  | seq t1 t2 => sum_theta t1 + sum_theta t2
  | disj t1 t2 => sum_theta t1 + sum_theta t2
  | kleene t1 => sum_theta t1
  end.

Fixpoint inclusion_ranking (hypos:list (theta * theta) ) : nat := 
  match hypos with 
  | nil => 0 
  | x :: xs => 1 + inclusion_ranking xs
  end.

Definition measure_test (hypos:list (theta * theta) ) : nat := 100 - (inclusion_ranking hypos). 

Inductive inclusion : theta -> theta -> Prop := 
  | inc_bot: forall t, 
    inclusion bot t 
  | inc_emp: forall t, 
    nullable t -> 
    inclusion emp t
  | inc_singleton: forall ev1 ev2, 
    (String.eqb ev1 ev2) -> 
    inclusion (theta_singleton ev1) (theta_singleton ev2)
  | inc_rec: forall t1 t2 ev,
    let deriv1 := theta_der t1 ev in 
    let deriv2 := theta_der t2 ev in 
    inclusion deriv1 deriv2 -> 
    inclusion t1 t2. 
 

Inductive future_condition_entailment : future_condition -> future_condition -> future_condition -> Prop := 
  | fce_emp : forall t1 t2,
    inclusion t1 t2 -> 
    future_condition_entailment (fc_singleton t1) (fc_singleton t2) (fc_singleton (kleene any))

  | fce_frame : forall f f1 f2 fr,
    future_condition_entailment f1 f2 fr -> 
    future_condition_entailment (conj f f1) f2 (conj fr f)

  | fce_conj : forall f f1 f2 fr1 fr2, 
    future_condition_entailment f f1 fr1 -> 
    future_condition_entailment f f2 fr2 -> 
    future_condition_entailment f (conj f1 f2) (conj fr1 fr2)
  .
    


Function inclusion (t1:theta) (t2:theta) (hypos: list (theta * theta) ) {measure measure_test hypos} : (bool) := 
  if Nat.eqb (inclusion_ranking hypos) 0 then false 
  else 
    let (fstSet) := fst t1 in 
    fold_right (fun (a:fstEv) (acc:(bool)) => 
      let bres := inclusion t1 t2 ((t1, t2)::hypos) in 
      (andb acc bres)
    
    ) true fstSet
  .
Proof.
  intros.
  unfold measure_test.
  unfold inclusion_ranking.
  fold inclusion_ranking.
  check (Nat.add_comm).
  rewrite Nat.add_comm.
  Search(_ - _ < _ - _).
  Admitted.
Defined.

Function inclusion (t1:theta) (t2:theta) (hypos: list (theta * theta) ) {measure inclusion_ranking hypos} : (bool) := 
  if andb (nullable t1) (negb (nullable t2)) then false
  else if Nat.eqb (inclusion_ranking hypos) 0 then false 
  else 
    let fstSet := fst t1 in 
    fold_right (fun (a:fstEv)  (acc:(bool)) => 
      let hypos' := ((t1, t2)::nil ) ++ hypos in 
      let bres := inclusion t1 t2 hypos' in 
      (andb acc bres)
    
    ) true fstSet.
Proof.
  intros A ls l1 l2 h t -> ->; unfold sum_len; simpl; rewrite Nat.add_comm; trivial with arith.
Defined.

Fixpoint inclusion (t1:theta) (t2:theta) (hypo: list (theta * theta) ): (bool) := 
  if andb (nullable t1) (negb (nullable t2)) then false
  else 
    let fstSet := fst t1 in 
    fold_right (fun (a:fstEv)  (acc:(bool)) => 
      let deriv1 := theta_der t1 a in 
      let deriv2 := theta_der t2 a in 
      let hypo' := ((t1, t2)::nil ) ++ hypo in 
      let bres := inclusion deriv1 deriv2 hypo' in 
      (andb acc bres)
    
    ) true fstSet. 

(*
T1  <:  T2 ~~~ T_residue

T1  <:  T2 . T_residue 

A   <:  A \/ B ~~~> 
*)



Fixpoint subtract_trace_from_future (st:future_condition) (t:theta) : future_condition := 
  let fstSet := fst t in 

  A.B.C - (A \/ B) = B.C \/ Bot = B.C 

  A.B.C /\ _^*.C   - (A \/ C) = (B.C /\ _^*.C) 
.

(*
if  st - t = st' :  t . st'  <:  st 
for all rho |= t, there exist rho' |= st' such that rho ++ rho' |= st 
*)

Fixpoint future_condition_der (st:future_condition) (ev: fstEv): future_condition :=
  match st with
  | fc_singleton theta => fc_singleton (theta_der theta ev)
  | conj f1 f2 => conj (future_condition_der f1 ev) (future_condition_der f2 ev)
  end.



Inductive forward : pre_state -> expr -> post_state -> Prop :=
| fw_val: forall sigma st v,
  forward (sigma, st) 
  (pval v) 
  (fun res => sigma \* \[res = v], emp, st)
| fw_ev : forall ev sigma st, 
  forward (sigma, st) 
  (pev ev) 
  (fun res => sigma \* \[res = vunit], theta_singleton ev, future_condition_der st (ev)).



Inductive bigstep : rho -> expr -> rho -> Prop :=
  | eval_pval : forall his v,
    bigstep his (pval v) his
    
  | eval_pev : forall his ev,
    bigstep his (pev ev) (his++(ev::nil))
  
  .

Inductive satisfies : rho -> theta -> Prop :=
  | ts_emp : satisfies nil (emp)
  | ts_ev: forall ev, satisfies (ev::nil) (theta_singleton ev)
  .


Definition sem_tuple (e: expr) (f: theta) : Prop :=
  bigstep rho e rho' -> satisfies env h1 h2 (norm v) f.


Notation derivable := forward.
Notation valid := sem_tuple.

Theorem soundness : forall e f,
  derivable e f -> valid e f.
