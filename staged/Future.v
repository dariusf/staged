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

with event : Type := ev (s:var) (v:val)

with theta :=
  | bot : theta
  | emp : theta
  | any : theta
  | theta_singleton : event -> theta
  | seq : theta -> theta -> theta
  | disj : theta -> theta -> theta
  | kleene : theta -> theta

with futureCond :=
  | fc_singleton : theta -> futureCond
  | fc_conj : futureCond -> futureCond -> futureCond

with expr : Type :=
  | pvar (x: var)
  | pval (v: val)
  | plet (x: var) (e1 e2: expr)
  | pevent  (ev:event) 
  | passume (f:futureCond)
  | pif (b: expr) (e1: expr) (e2: expr)
  | papp (x: var) (a: val).


Definition compare_event (ev1:event) (ev2:event) : bool := 
  let (s1, v1) := ev1 in 
  let (s2, v2) := ev1 in 
  andb (String.eqb s1 s2) (String.eqb s1 s2).



#[global]
Instance Inhab_val : Inhab val.
Proof.
  constructor.
  exists (vunit).
  constructor.
Qed.


Module Val.
  Definition value := val.
End Val.


Definition rho : Type := list (event).

Definition fstEvs : Type := list (event).


(*
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
*)
Fixpoint subst (y:var) (w:val) (e:expr) : expr :=
  let aux t := subst y w t in
  let if_y_eq x t1 t2 := if var_eq x y then t1 else t2 in
  match e with
  | pval v => pval v
  | pvar x => if_y_eq x (pval w) e
  | papp e v => papp e v
  | plet x t1 t2 => plet x (aux t1) (if_y_eq x t2 (aux t2))
  | pif t0 t1 t2 => pif (aux t0) (aux t1) (aux t2)
  | pevent _ => e 
  | passume _ => e
  end.




Inductive bigstep : rho -> futureCond -> expr -> rho -> futureCond  -> val -> Prop :=
  | eval_const : forall r f v, 
    bigstep r f (pval v) r f v
  

  | eval_let : forall r f r1 f1 v1 r2 f2 v2 x e1 e2,
    bigstep r f e1 r1 f1 v1 ->
    bigstep r1 f1 (subst x v1 e2) r2 f2 v2 ->
    bigstep r f  (plet x e1 e2) r2 f2 v2

  | eval_if_true : forall r f e1 e2 r' f' v, 
    bigstep r f e1 r' f' v -> 
    bigstep r f (pif (pval (vbool true)) e1 e2) r' f' v

  | eval_if_false : forall r f e1 e2 r' f' v, 
    bigstep r f e2 r' f' v -> 
    bigstep r f (pif (pval (vbool false)) e1 e2) r' f' v

  | eval_assume : forall r f f_assume, 
    bigstep r f (passume f_assume) r (fc_conj f f_assume) vunit

  | eval_event : forall r f ev, 
    bigstep r f (pevent ev) (r ++ (ev::nil)) f vunit
  .

Inductive trace_model : rho -> theta -> Prop :=
  | tm_emp : trace_model nil emp

  | tm_singleton : forall ev1 ev, 
    compare_event ev ev1 = true -> 
    trace_model (ev1::nil) (theta_singleton ev)

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


Inductive forward : theta -> futureCond -> expr -> theta -> futureCond -> val -> Prop := 
  | fw_val: forall t f v,
    forward t f (pval v) t f v. 





Example ex1 : forward emp (fc_singleton emp) (pval (vint 1)) emp (fc_singleton emp) (vint 1).
Proof.
  constructor.
Qed.

Print ex1.


Fixpoint nullable (t: theta): bool :=
  match t with
  | bot => false 
  | any => false
  | emp => true 
  | theta_singleton _ => false
  | seq t1 t2 =>  andb (nullable t1) (nullable t2 )
  | disj t1 t2 => orb (nullable t1) (nullable t2)
  | kleene _ => true 
  end.

Fixpoint fst (t: theta): fstEvs :=
  match t with
  | bot => nil
  | emp => nil
  | any => (ev "_" vunit) :: nil
  | theta_singleton (ev e v) => (ev e v) :: nil
  | seq t1 t2 => if (nullable t1) then fst t1 ++ fst t2 else fst t1 
  | disj t1 t2 => fst t1 ++ fst t2
  | kleene t1 => fst t1 
  end. 


Fixpoint theta_der (t:theta) (ev:event) : theta := 
  match t with 
  | bot => bot
  | emp => bot
  | any => emp 
  | theta_singleton ev1 => 
    if compare_event ev ev1 then emp else bot  
  | seq t1 t2 => 
    let temp := seq (theta_der t1 ev) t2 in 
    if (nullable t1) then disj temp (theta_der t2 ev) else temp
  | disj t1 t2 => disj (theta_der t1 ev) (theta_der t2 ev)
  | kleene t1 => seq (theta_der t1 ev) t 
  end.



Inductive inclusion : theta -> theta -> bool -> Prop := 
  | inc_emp: forall t1 t2, 
    nullable t1 -> 
    not (nullable t2) -> 
    inclusion t1 t2 false 
  | inc_exact: forall t, 
    inclusion t t true
  | inc_singleton: forall t1 t2, 
    fst t1 = nil -> 
    inclusion t1 t2 true 
  | inc_rec: forall t1 t2 ev,
    let deriv1 := theta_der t1 ev in 
    let deriv2 := theta_der t2 ev in 
    inclusion deriv1 deriv2 true -> 
    inclusion t1 t2 true. 
 

Inductive futureCondEntail : futureCond -> futureCond -> futureCond -> Prop := 
  | futureCondEntail_empty : forall t1 t2, 
    inclusion t1 t2 true -> 
    futureCondEntail (fc_singleton t1) (fc_singleton t2)  (fc_singleton (kleene any)).

Lemma futureCondEntail_exact : forall f, 
  futureCondEntail f f (fc_singleton(kleene any)).
Proof.
Admitted.

Theorem soundness : forall e t1 t2 f1 f2 v v' rho1 rho2 f',
  forward t1 f1 e t2 f2 v ->  
  bigstep rho1 f1 e rho2 f' v' -> 
  trace_model rho1 t1 -> 
  trace_model rho2 t2 /\ exists f_Res, futureCondEntail f2 f' f_Res. 
Proof. 
  intros. 
  induction H.
  inverts H0. 
  split.
  exact H1.
  exists (fc_singleton(kleene any)).
  apply futureCondEntail_exact.
Qed. 

  
  



(** SLF's heap theory as a functor. *)
Module Export Heap := HeapF.HeapSetup Val.

Definition empty_heap : heap := Fmap.empty.

Definition precond := hprop.
Definition postcond := val -> hprop. 

Definition pre_state  : Type := (hprop * futureCond).
Definition post_state : Type := (postcond * theta * futureCond).

Definition rho : Type := (list fstEv).






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