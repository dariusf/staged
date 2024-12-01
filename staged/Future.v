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
  | pevent  (ev:event) 
  | pif (b: expr) (e1: expr) (e2: expr)
  | pref (v: expr)
  | pderef (v: expr)
  | passign (x: expr) (v: expr)
  | passume (f:futureCond)

  | papp (x: var) (a: val)
  | plet (x: var) (e1 e2: expr). 






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


Definition compare_event (ev1:event) (ev2:event) : bool := 
  let (s1, v1) := ev1 in 
  let (s2, v2) := ev2 in 
  (String.eqb s1 s2).




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
  | pderef t1 => pderef (aux t1)
  | passign t1 t2 =>  passign (aux t1) (aux t2)
  | pref t1 => pref (aux t1)
  end.

(** SLF's heap theory as a functor. *)
Module Export Heap := HeapF.HeapSetup Val.

Definition empty_heap : heap := Fmap.empty.

Definition precond := hprop.
Definition postcond := val -> hprop.



Inductive bigstep : heap -> rho -> futureCond -> expr -> heap -> rho -> futureCond  -> val -> Prop :=
  | eval_const : forall h r f v, 
    bigstep h r f (pval v) h r f v
  
  | eval_let : forall h r f h1 r1 f1 v1 h2 r2 f2 v2 x e1 e2,
    bigstep h r f e1 h1 r1 f1 v1 ->
    bigstep h1 r1 f1 (subst x v1 e2) h2 r2 f2 v2 ->
    bigstep h r f (plet x e1 e2) h2 r2 f2 v2

  | eval_if_true : forall h r f e1 e2 h' r' f' v, 
    bigstep h r f e1 h' r' f' v -> 
    bigstep h r f (pif (pval (vbool true)) e1 e2) h' r' f' v

  | eval_if_false : forall h r f e1 e2 h' r' f' v, 
    bigstep h r f e2 h' r' f' v -> 
    bigstep h r f (pif (pval (vbool false)) e1 e2) h' r' f' v

  | eval_assume : forall h r f f_assume, 
    bigstep h r f (passume f_assume) h r (fc_conj f f_assume) vunit

  | eval_event : forall h r f ev, 
    bigstep h r f (pevent ev) h (r ++ (ev::nil)) f vunit

  | eval_pref : forall h r f loc v,
    ~ Fmap.indom h loc ->
    bigstep h r f (pref (pval v)) (Fmap.update h loc v) r f (vloc loc)

  | eval_pderef : forall h r f loc,
    Fmap.indom h loc ->
    bigstep h r f (pderef (pval (vloc loc))) h r f (Fmap.read h loc)

  | eval_passign : forall h r f loc v,
    Fmap.indom h loc ->
    bigstep h r f (passign (pval (vloc loc)) (pval v)) (Fmap.update h loc v) r f vunit
  .

Inductive trace_model : rho -> theta -> Prop :=
  | tm_emp : trace_model nil emp

  | tm_singleton : forall ev1 ev, 
    ev = ev1 -> 
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




Definition pre_state  : Type := (hprop * futureCond).
Definition post_state : Type := (postcond * theta * futureCond).


Inductive forward : hprop -> theta -> futureCond -> expr -> (val -> hprop) -> theta -> futureCond -> Prop := 
  | fw_val: forall t f v P ,
    forward P t f (pval v) (fun res => P \* \[res = v]) t f

  | fw_cond : forall (b:bool) e1 e2 t t1 f f1 P Q, 
    forward P t f (if b then e1 else e2) Q t1 f1 -> 
    forward P t f (pif (pval (vbool b)) e1 e2) Q t1 f1

  | fw_event: forall t f P (ev:event) ,
    forward P t f (pevent ev) (fun res => P \* \[res = vunit]) (seq t (theta_singleton ev)) f

  | fw_ref : forall t f v, 
    forward \[] t f (pref (pval v)) (fun res => \exists p, \[res = vloc p] \* p ~~> v) t f
  
  | fw_deref : forall t f loc v, 
    forward (loc ~~> v) t f (pderef (pval(vloc loc))) (fun res => (loc ~~> v) \* \[res = v])  t f

  | fw_assign : forall t f loc v v', 
    forward (loc ~~> v') t f (passign (pval(vloc loc)) (pval v)) (fun res => (loc ~~> v) \* \[res = vunit])  t f

  | fw_assume : forall P t f f1, 
    forward P t f (passume f1) (fun res => P \* \[res = vunit])  t (fc_conj f f1) 


  | fw_let : forall x e1 e2 P t f t1 f1 Q t2 f2 Q', 
    forward P t f e1 Q t1 f1  -> 
    forall v, forward (Q v) t1 f1 (subst x v e2) Q' t2 f2 -> 
    forward P t f (plet x e1 e2) Q' t2 f2. 




Example ex1 : exists Q, forward \[] emp (fc_singleton emp) (pval (vint 1)) Q emp (fc_singleton emp).
Proof.
  eexists.
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
    futureCondEntail (fc_singleton t1) (fc_singleton t2)  (fc_singleton (kleene any))
  | futureCondEntail_conj_right : forall f f1 f2 fR1 fR2, 
    futureCondEntail f f1 fR1 -> 
    futureCondEntail f f2 fR2 -> 
    futureCondEntail f (fc_conj f1 f2) (fc_conj fR1 fR2) 

  | futureCondEntail_conj_left : forall f f1 f2 fR1 fR2, 
    futureCondEntail f1 f fR1 -> 
    futureCondEntail f2 f fR2 -> 
    futureCondEntail (fc_conj f1 f2) f  (fc_singleton (kleene any))
  .

Lemma futureCondEntail_exact : forall f, 
  futureCondEntail f f (fc_singleton(kleene any)).
Proof.
  intros.
  induction f.
  constructor.
  constructor.
  
Admitted.

Lemma trace_model_prefix : forall rho t rho1 t1, 
  trace_model rho t -> 
  trace_model rho1 t1 -> 
  trace_model (rho++rho1) (seq t t1).
Proof.
Admitted.



Theorem soundness : forall e P t1 t2 Q f1 f2 v h1 h2 rho1 rho2 f',
  forward P t1 f1 e Q t2 f2 ->  
  bigstep h1 rho1 f1 e h2 rho2 f' v -> 
  P h1 -> 
  trace_model rho1 t1 -> 
  Q v h2 /\ trace_model rho2 t2 /\ exists f_Res, futureCondEntail f2 f' f_Res.  
  
Proof. 
  intros.
  induction H.
  -
  invert H0.
  intros.
  split.
  rewrite hstar_hpure_r.
  split. subst. auto.
  reflexivity.
  split. subst. auto.
  exists (fc_singleton(kleene any)).
  apply futureCondEntail_exact.

  - 
  invert H0.
  intros.
  apply IHforward. 
  induction b.
  exact H13.   
  lia.
  exact H1.
  exact H2.
  intros.
  apply IHforward. 
  induction b.
  lia.
  exact H13.   
  exact H1.
  exact H2.

  - 
  invert H0.
  intros.
  split.
  rewrite hstar_hpure_r.
  split. subst. auto.
  reflexivity.
  split.
  apply trace_model_prefix.
  exact H2.
  constructor. reflexivity.
  exists (fc_singleton(kleene any)).
  apply futureCondEntail_exact.
  -  
  invert H0.
  intros.
  split. 
  exists loc0.  
  rewrite H7.
  rewrite H10.
  rewrite hstar_hpure_l.
  split.
  reflexivity.
  rewrite H1 in H7.
  rewrite Fmap.update_empty in H7. 
  apply Logic.eq_sym in H7.
  rewrite H7. 
  apply hsingle_intro.
  split.
  subst. exact H2.
  exists (fc_singleton(kleene any)).
  apply futureCondEntail_exact.

  - 
  invert H0.
  intros.
  split.
  rewrite H10.
  subst. 
  rewrite hstar_hpure_r. 
  split. exact H1. 
  apply hsingle_inv in H1.
  rewrite H1.
  apply Fmap.read_single. 
  split. subst. 
  exact H2.
  exists (fc_singleton(kleene any)).
  apply futureCondEntail_exact.

  -
  invert H0.
  intros.
  split. 
  rewrite H6.
  rewrite hstar_hpure_r. subst.
  split. 
  apply hsingle_inv in H1.
  rewrite H1.
  rewrite Fmap.update_single.
  Search (Fmap.single _ _ ). 
  apply hsingle_intro. 
  reflexivity. 
  split. subst.  exact H2.
  exists (fc_singleton(kleene any)).
  apply futureCondEntail_exact.

  - 
  invert H0.
  intros.
  split. 
  rewrite hstar_hpure_r. subst.
  split. exact H1. 
  reflexivity.
  split.
  subst.
  exact H2.
  exists (fc_singleton(kleene any)).
  apply futureCondEntail_exact.

  




   


  -
  invert H0.
  intros.  subst. 
  apply IHforward2.
  induction e2.
  invert H3.
  intros.  









 (*
    

  
  
  rewrite H7.
  rewrite IHforward2. 

  constructor. 
  unfold bigstep.
  exact H0. 



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