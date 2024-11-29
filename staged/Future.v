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

(*
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
*)


(** * Programs *)
(** The representation of programs and the use of substitution are mostly reused from SLF. *)
Definition var : Type := string.
Definition var_eq := String.string_dec.

Inductive constant := 
  | cunit : constant
  | cbool : bool -> constant
  | cint  : Z -> constant.

Inductive val :=
  | vconst : constant -> val
  | vint : Z -> val.

Definition event : Type := (var * val).

Definition constant_eqb (c1:constant) (c2:constant) : bool := 
  match c1, c2 with 
  | cunit, cunit => true 
  | cbool b1, cbool b2 => Bool.eqb b1 b2
  | cint i1, cint i2 => Z.eqb i1 i2
  | _, _ => false 
  end. 
  

Definition compare_event (ev1:event) (ev2:event) : bool := 
  let (s1, v1) := ev1 in 
  let (s2, v2) := ev1 in 
  andb (String.eqb s1 s2) (String.eqb s1 s2).

Inductive theta :=
  | bot : theta
  | emp : theta
  | any : theta
  | theta_singleton : event -> theta
  | not_event : event -> theta
  | seq : theta -> theta -> theta
  | disj : theta -> theta -> theta
  | kleene : theta -> theta.

Inductive futureCond :=
  | fc_singleton : theta -> futureCond
  | fc_conj : futureCond -> futureCond -> futureCond.

Inductive expr : Type :=
  | pval (v: val)
  | plet (x: var) (e1 e2: expr)
  | pevent  (ev:event) 
  | passume (f:futureCond)
  | pif (b: var) (e1: expr) (e2: expr)
  | papp (x: var) (a: val).

#[global]
Instance Inhab_val : Inhab val.
Proof.
  constructor.
  exists (vconst cunit).
  constructor.
Qed.


Module Val.
  Definition value := val.
End Val.


Definition stack : Type := list (var * constant).

Definition rho : Type := list (event).

Definition env : Type := (stack * rho * futureCond).

Fixpoint update_stack  (s:stack) (str:var) (c:constant): stack := 
  match s with 
  | nil => (str, c)::nil 
  | (str1, c1) :: s' => 
    if (String.eqb str str1) 
    then (str, c) :: s'
    else (str1, c1) :: (update_stack s' str c)
  end. 

Fixpoint read_stack  (s:stack) (str:var) : constant := 
  match s with 
  | nil => cint 0 
  | (str1, c1) :: s' => 
    if (String.eqb str str1) then c1
    else (read_stack s' str)
  end. 

Inductive bigstep : stack -> rho -> futureCond -> expr -> stack -> rho -> futureCond  -> constant -> Prop :=
  | bigstep_const : forall s s' r f c, 
    bigstep s r f (pval (vconst c)) s' r f c 
  
  | bigstep_var : forall s s' c r f x, 
    c = read_stack s x -> 
    bigstep s r f (pval (vconst c)) s' r f c

  | bigstep_let : forall s r f s1 r1 f1 s2 r2 f2 x e1 e2 c1 c2, 
    bigstep s r f e1 s1 r1 f1 c1 -> 
    bigstep ((x, c1)::s1) r1 f1 e2 s2 r2 f2 c2 -> 
    bigstep s r f (plet x e1 e2) s2 r2 f2 c2

  | bigstep_if_true : forall s r f b e1 e2 s' r' f' c, 
    (cbool true) = read_stack s b -> 
    bigstep s r f e1 s' r' f' c -> 
    bigstep s r f (pif b e1 e2) s' r' f' c

  | bigstep_if_false : forall s r f b e1 e2 s' r' f' c, 
    (cbool false) = read_stack s b -> 
    bigstep s r f e2 s' r' f' c -> 
    bigstep s r f (pif b e1 e2) s' r' f' c

  | bigstep_assume : forall s r f f_assume, 
    bigstep s r f (passume f_assume) s r (fc_conj f f_assume) cunit

  | bigstep_event : forall s r f ev, 
    bigstep s r f (pevent ev) s (r ++ (ev::nil)) f cunit
  .

Inductive trace_model : rho -> theta -> Prop :=
  | tm_emp : trace_model nil emp

  | tm_singleton : forall ev1 ev, 
    compare_event ev ev1 = true -> 
    trace_model (ev1::nil) (theta_singleton ev)

  | tm_notevent : forall ev1 ev, 
    compare_event ev ev1 = false -> 
    trace_model (ev1::nil) (not_event ev)


  | tm_any : forall ev, 
    trace_model (ev::nil) (any)

  | tm_seq : forall rho rho1 rho2 t1 t2, 
    rho1 ++ rho2 = rho ->
    trace_model rho1 t1 -> 
    trace_model rho2 t2 -> 
    trace_model rho (seq t1 t2)

  | tm_disj_left : forall rho t1 t2, 
    trace_model rho t1 -> 
    trace_model rho (disj t1 t2)

  | tm_disj_right : forall rho t1 t2, 
    trace_model rho t2 -> 
    trace_model rho (disj t1 t2)

  | tm_kleene_emp : forall rho t, 
    trace_model rho emp -> 
    trace_model rho (kleene t)

  | tm_kleene_rec : forall rho t, 
    trace_model rho (seq t (kleene t)) -> 
    trace_model rho (kleene t)
  . 
    
Inductive fc_model : rho -> futureCond -> Prop :=
  | fc_model_singleton : forall rho t, 
    trace_model rho t -> 
    fc_model rho (fc_singleton t)

  | fc_model_conj : forall rho f1 f2, 
    fc_model rho f1 -> 
    fc_model rho f2 -> 
    fc_model rho (fc_conj f1 f2)
    .



Definition fstEv : Type := (var).


(** SLF's heap theory as a functor. *)
Module Export Heap := HeapF.HeapSetup Val.

Definition empty_heap : heap := Fmap.empty.

Definition precond := hprop.
Definition postcond := val -> hprop. 

Definition pre_state  : Type := (hprop * futureCond).
Definition post_state : Type := (postcond * theta * futureCond).

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

Inductive inclusion : theta -> theta -> bool -> Prop := 
  | inc_emp: forall t1 t2, 
    nullable t1 -> 
    not (nullable t2) -> 
    inclusion t1 t2 false 
  | inc_singleton: forall t1 t2, 
    fst t1 = nil -> 
    inclusion t1 t2 true 
  | inc_rec: forall t1 t2 ev,
    let deriv1 := theta_der t1 ev in 
    let deriv2 := theta_der t2 ev in 
    inclusion deriv1 deriv2 true -> 
    inclusion t1 t2 true. 
 

Inductive future_condition_entailment : futureCond -> futureCond -> futureCond -> Prop := 
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
 (*
    


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



Fixpoint subtract_trace_from_future (st:futureCond) (t:theta) : futureCond := 
  let fstSet := fst t in 

  A.B.C - (A \/ B) = B.C \/ Bot = B.C 

  A.B.C /\ _^*.C   - (A \/ C) = (B.C /\ _^*.C) 
.

(*
if  st - t = st' :  t . st'  <:  st 
for all rho |= t, there exist rho' |= st' such that rho ++ rho' |= st 
*)

Fixpoint future_condition_der (st:futureCond) (ev: fstEv): futureCond :=
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

 *)