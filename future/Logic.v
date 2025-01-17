(*

$ opam pin add coq 8.18.0
$ opam install vscoq-language-server

$ which vscoqtop

opam pin add vscoq-language-server.2.2.1  https://github.com/coq/vscoq/releases/download/v2.2.1/vscoq-language-server-2.2.1.tar.gz
*)

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

with event : Type := 
  | ev (s:var) (v:val) | any 

with theta :=
  | bot : theta
  | emp : theta
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
  | papp (f: expr) (e: expr)
  | pseq (e1:expr) (e2:expr)
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



Definition rho : Type := list (event).

Definition fstEvs : Type := list (event).


Fixpoint subst (y:var) (w:val) (e:expr) : expr :=
  let aux t := subst y w t in
  let if_y_eq x t1 t2 := if var_eq x y then t1 else t2 in
  match e with
  | pval v => pval v
  | pvar x => if_y_eq x (pval w) e
  | papp t1 t2 => papp (aux t1) (aux t2)
  | plet x t1 t2 => plet x (aux t1) (if_y_eq x t2 (aux t2))
  | pif t0 t1 t2 => pif (aux t0) (aux t1) (aux t2)
  | pevent _ => e 
  | passume _ => e
  | pderef t1 => pderef (aux t1)
  | passign t1 t2 =>  passign (aux t1) (aux t2)
  | pseq t1 t2 =>  pseq (aux t1) (aux t2)
  | pref t1 => pref (aux t1)
  end.

(** SLF's heap theory as a functor. *)
Module Export Heap := HeapF.HeapSetup Val.

Definition empty_heap : heap := Fmap.empty.

Definition precond := hprop.
Definition postcond := val -> hprop.

Inductive trace_model : rho -> theta -> Prop :=
  | tm_emp : trace_model nil emp

  | tm_singleton : forall ev1 ev, 
    ev = ev1 -> 
    trace_model (ev1::nil) (theta_singleton ev)

  | tm_seq : forall rho1 rho2 t1 t2, 
    trace_model rho1 t1 -> 
    trace_model rho2 t2 -> 
    trace_model (rho1 ++ rho2) (seq t1 t2)

  | tm_disj_left : forall rho t1 t2, 
    trace_model rho t1 -> 
    trace_model rho (disj t1 t2)

  | tm_disj_right : forall rho t1 t2, 
    trace_model rho t2 -> 
    trace_model rho (disj t1 t2)

  | tm_kleene_emp : forall t, 
    trace_model nil (kleene t)

  | tm_kleene_rec : forall rho t, 
    trace_model rho (seq t (kleene t)) -> 
    trace_model rho (kleene t).

Inductive fc_model : rho -> futureCond -> Prop :=
  | fc_model_singleton : forall rho t, 
    trace_model rho t -> 
    fc_model rho (fc_singleton t)

  | fc_model_conj : forall rho f1 f2, 
    fc_model rho f1 -> 
    fc_model rho f2 -> 
    fc_model rho (fc_conj f1 f2)
    .


Inductive nullable: theta -> Prop :=
  | nullable_emp : nullable emp 
  | nullable_seq : forall t1 t2, 
    nullable t1 -> nullable t2 -> nullable (seq t1 t2)
  | nullable_disj_left : forall t1 t2, 
    nullable t1 -> nullable (disj t1 t2)
  | nullable_disj_right : forall t1 t2, 
    nullable t2 -> nullable (disj t1 t2)
  | nullable_kleene : forall t, nullable (kleene t) . 


Lemma empty_rho_model_nullable_trace : forall t, 
  nullable t -> 
  trace_model nil t. 
Proof.
  intros.
  induction H.
  - constructor.
  - pose proof List.app_nil_l. 
    specialize (H1 event nil). 
    rewrite <- H1.
    constructor.
    exact IHnullable1.
    exact IHnullable2.  
  - apply tm_disj_left. exact IHnullable.
  - apply tm_disj_right. exact IHnullable.
  - apply tm_kleene_emp. 
Qed.   

Lemma trace_model_emp_must_nil : forall rho, 
  trace_model rho emp -> rho = nil.
Proof.
  intros.
  invert H.
  intros.
  reflexivity.   
Qed. 



Inductive fst : theta -> fstEvs -> Prop :=
  | fst_bot: fst bot nil 
  | fst_emp: fst emp nil 
  | fst_event: forall e v, 
    fst (theta_singleton (ev e v)) ((ev e v) :: nil)
  | fst_seq_nullable: forall t1 t2 fst1 fst2, 
    nullable t1 -> 
    fst t1 fst1 -> 
    fst t2 fst2 -> 
    fst (seq t1 t2) (fst1 ++ fst2)
  | fst_seq_not_nullable: forall t1 t2 fst1, 
    fst t1 fst1 -> 
    fst (seq t1 t2) (fst1)
  | fst_disj: forall t1 t2 fst1 fst2, 
    fst t1 fst1 -> 
    fst t2 fst2 -> 
    fst (disj t1 t2) (fst1 ++ fst2)
  | fst_kleene : forall t f1, 
    fst t f1 -> 
    fst (kleene t) f1
  .

Inductive theta_der : theta -> event -> theta  -> Prop := 
  | derivative_bot : forall ev, 
    theta_der bot ev bot 

  | derivative_emp : forall ev, 
    theta_der emp ev bot 

  | derivative_event_singleton : forall ev1 ev2, 
    ev1 = ev2 -> 
    theta_der (theta_singleton ev1) ev2 emp 

  | derivative_seq_nullable: forall t1 t2 ev t1_der t2_der, 
    nullable t1 -> 
    theta_der t1 ev t1_der -> 
    theta_der t2 ev t2_der -> 
    theta_der (seq t1 t2) ev (disj (seq t1_der t2) t2_der)

  | derivative_seq_not_nullable: forall t1 t2 ev t1_der, 
    theta_der t1 ev t1_der -> 
    theta_der (seq t1 t2) ev (seq t1_der t2)
    
  | derivative_disj: forall t1 t2 ev t1_der t2_der, 
    theta_der t1 ev t1_der -> 
    theta_der t2 ev t2_der -> 
    theta_der (disj t1 t2) ev (disj t1_der t2_der)

  | derivative_kleene: forall t ev t_der, 
    theta_der t ev t_der -> 
    theta_der (kleene t) ev (seq (t_der) (kleene t))
  . 

Inductive fc_der : futureCond -> event -> futureCond  -> Prop := 
  | derivative_theta: forall t ev t1, 
    theta_der t ev t1 ->
    fc_der (fc_singleton t ) ev (fc_singleton t1 )

  | derivative_fc_conj: forall f1 f2 ev f_der1 f_der2, 
    fc_der f1 ev f_der1 -> 
    fc_der f2 ev f_der2 -> 
    fc_der (fc_conj f1 f2) ev (fc_conj f_der1 f_der2 )
    . 



Lemma nullable_trans : forall t1 t2, 
  nullable t1 -> nullable t2 -> nullable (seq t1 t2).
Proof.
  intros.
  constructor.
  exact H. exact H0.
Qed.     

Axiom normal_emp : forall t, seq emp t = t. 
Axiom normal_kleene : forall t, kleene t = disj emp (seq t (kleene t)).


Lemma nullable_rev : forall t, 
  nullable t -> trace_model nil t.
Proof.
  intros.
  induction H.
  -constructor.
  -intros. 
   rewrite<-(List.app_nil_r nil).
   constructor. 
   exact  IHnullable1.
   exact IHnullable2.
  - apply tm_disj_left. exact IHnullable.
  - apply tm_disj_right. exact IHnullable.
  - apply tm_kleene_emp.  
Qed.    

Axiom disj_not_bot: forall t1 t2, 
  disj t1 t2 <> bot -> 
  (t1 <> bot /\ t1=bot) \/ 
  (t2 <> bot /\ t2=bot) \/ 
  (t1 <> bot /\ t2 <> bot) .

Axiom seq_not_bot: forall t1 t2, 
  seq t1 t2 <> bot -> t1 <> bot /\ t2 <> bot.

Axiom theta_singleton_not_emp: forall ev, 
  theta_singleton ev <> emp. 

Axiom theta_singleton_not_bot: forall ev, 
  theta_singleton ev <> bot. 

Axiom theta_der_not_bot: forall t ev t_der, 
  theta_der t ev t_der -> 
  t_der <> bot -> 
  t <> bot.  

Axiom kleene_not_bot : forall t rho, 
  t <> bot -> 
  trace_model rho (kleene t) ->   rho <> nil.

Lemma derivative_model : forall t1 ev0 deriv1 rho0, 
  theta_der t1 ev0 deriv1 -> 
  deriv1 <> bot -> 
  trace_model rho0 t1 -> 
  exists rho1, 
  rho0 = ev0 :: rho1 /\ trace_model rho1 deriv1.
Proof.
  intros.
  gen rho0.
  induction H.
  -
  intros. false.  
  -
  intros. false.  
  - 
  intros. subst. 
  invert H1.
  intros. subst.
  exists (nil:rho).
  split.
  reflexivity. constructor.
  -
  intros.
  invert H3.
  intros. subst.
  pose disj_not_bot. 
  specialize (o (seq t1_der t2) t2_der H0 ). 
  destruct o. destruct H3. 
  false.  
  destruct H3. destruct H3. false. 
  destruct H3. 
  specialize (IHtheta_der2 H4 rho2 H8).
  destr IHtheta_der2.
  pose seq_not_bot. 
  specialize (a t1_der t2 H3). 
  destr a.
  specialize (IHtheta_der1 H5 rho1 H7). 
  destr IHtheta_der1.
  exists (rho3 ++ rho2).
  rewrite H12.
  split. eauto. 
  apply tm_disj_left.
  constructor.
  exact H13. exact H8.
  -
  intros. invert H1.
  intros. subst.
  pose seq_not_bot. 
  specialize (a t1_der t2 H0). 
  destr a.
  specialize (IHtheta_der H1 rho1 H5). 
  destr IHtheta_der.
  exists (rho0++rho2).
  split.
  rewrite H4.
  eauto. constructor. exact H7. exact H6.
  -
  intros.
  invert H2.
  intros. subst.
  pose disj_not_bot. 
  specialize (o t1_der t2_der H0 ). 
  destruct o. destruct H2. false.  
  destruct H2. destruct H2. false. 
  destruct H2. 
  specialize (IHtheta_der1 H2 rho0 H5). 
  destr IHtheta_der1.
  exists (rho1).
  split.
  rewrite H6.
  eauto. apply tm_disj_left. exact H7.
  intros. subst. 
  pose disj_not_bot. 
  specialize (o t1_der t2_der H0 ). 
  destruct o. destruct H2. false.  
  destruct H2. destruct H2. false. 
  destruct H2. 
  specialize (IHtheta_der2 H3 rho0 H5). 
  destr IHtheta_der2.
  exists (rho1).
  split.
  rewrite H6.
  eauto. apply tm_disj_right. exact H7.
  -
  intros.
  pose seq_not_bot. 
  specialize (a t_der (kleene t) H0).  
  destr a. 
  pose theta_der_not_bot. 
  specialize (n t ev0 t_der H H2). 
  pose kleene_not_bot. 
  specialize (n0 t rho0 n H1).  
  invert H1.
  intros. subst. false.
  intros. 
  invert H6. 
  intros. subst. 
  specialize (IHtheta_der H2  rho2 H9) .   
  destr IHtheta_der.
  exists ( rho1 ++ rho3).
  split.
  rewrite H4. eauto.
  constructor.
  exact H5. exact H10.
Qed.         

Lemma derivative_model_reverse: forall rho1 deriv2 t2 ev0, 
  trace_model rho1 deriv2 -> 
  theta_der t2 ev0 deriv2 -> 
  trace_model (ev0 :: rho1) t2. 
Proof. 
  intros.
  gen rho1.
  induction H0.
  -
  intros. 
  invert H.
  -
  intros. 
  invert H.
  -
  intros. 
  invert H0.
  intros. subst.   
  constructor.
  reflexivity.
  -
  intros. 
  invert H0.
  intros. subst.
  invert H3.
  intros. subst.  
  specialize (IHtheta_der1 rho0 H4).
  pose proof List.app_comm_cons.
  specialize (H0 event rho0 rho2 ev0).  
  rewrite H0.
  constructor.
  exact IHtheta_der1.
  exact H5.
  intros. subst.
  specialize (IHtheta_der2 rho1 H3).
  Search (nil++ _ ). 
  pose proof List.app_nil_l.
  specialize (H0 event (ev0 :: rho1)). 
  rewrite <- H0.
  constructor. 
  apply empty_rho_model_nullable_trace. exact H. exact IHtheta_der2.     
  - 
  intros. invert H.
  intros. subst.
  specialize (IHtheta_der rho0 H4 ).  
  pose proof List.app_comm_cons.
  specialize (H event rho0 rho2 ev0).
  rewrite H.
  constructor. 
  exact IHtheta_der.
  exact H5.
  -
  intros.
  invert H.
  intros. subst.
  specialize (IHtheta_der1 rho1 H2).
  apply tm_disj_left.
  exact IHtheta_der1.
  intros. subst.
  specialize (IHtheta_der2 rho1 H2).
  apply tm_disj_right. exact IHtheta_der2.
  -
  intros.
  invert H.
  intros. subst.
  specialize (IHtheta_der rho0 H4). 
  pose proof List.app_comm_cons. 
  specialize (H event rho0 rho2 ev0).
  rewrite H. 
  constructor.
  constructor.
  exact IHtheta_der.
  exact H5.   
Qed. 



Inductive inclusion : theta -> theta -> Prop := 

  | inc_bot: forall t, inclusion bot t 

  | inc_emp: forall t, 
    nullable t -> 
    inclusion emp t 

  | (* Unfold *)
    inc_unfold: forall t1 t2 ev deriv1 deriv2,
    theta_der t1 ev deriv1 -> 
    deriv1 <> bot -> 
    theta_der t2 ev deriv2 -> 
    inclusion deriv1 deriv2 -> 
    inclusion t1 t2
. 


Theorem inclusion_sound: forall t1 t2 rho, 
  inclusion t1 t2 -> 
  trace_model rho t1 -> 
  trace_model rho t2.
Proof.
  intros. 
  gen rho0. 
  induction H.
  - intros.
    invert H0.  
  - intros. 
    pose proof empty_rho_model_nullable_trace.
    specialize (H1 t H).
    pose proof trace_model_emp_must_nil.
    specialize (H2 rho0 H0).
    subst.
    exact H1.
  - intros.
    pose proof derivative_model.
    specialize (H4 t1 ev0 deriv1 rho0 H H0 H3). 
    destr H4.
    specialize (IHinclusion rho1 H6).  
    subst.
    pose proof derivative_model_reverse. 
    specialize (H4 rho1 deriv2 t2 ev0 IHinclusion H1). 
    exact H4.
Qed. 

Lemma trace_model_nil_indicate_nullable: forall t rho, 
  trace_model rho t -> rho = nil -> nullable t. 
Proof.
  intros.
  induction H.
  - constructor.
  - false.
  - 
    pose proof List.app_eq_nil.
  specialize (H2 event rho1 rho2 H0). 
  destr H2. subst.
  constructor.
  apply IHtrace_model1.
  reflexivity.
  apply IHtrace_model2.
  reflexivity.
  - subst. 
  constructor.
  apply IHtrace_model. reflexivity.
  - apply nullable_disj_right.     
  apply IHtrace_model. exact H0.
  - 
  constructor.
  - constructor.  
Qed.     

Axiom all_trace_have_derivative: forall t ev , 
  exists deriv, theta_der t ev deriv. 

Axiom inclusion_theta_der_indicate : forall t1 t2 ev0 deriv1, 
  inclusion t1 t2 -> 
  theta_der t1 ev0 deriv1 -> 
  exists deriv2, 
  theta_der t2 ev0 deriv2 /\ inclusion deriv1 deriv2.




Theorem inclusion_trans : forall t1 t2 t3, 
  inclusion t1 t2 -> 
  inclusion t2 t3 -> 
  inclusion t1 t3.
Proof.
  intros.
  gen t3.
  induction H.
  - 
  intros.
  constructor.  
  -
  intros. 
  pose proof empty_rho_model_nullable_trace.
  specialize (H1 t H). 
  pose proof inclusion_sound.
  specialize (H2 t t3 nil H0 H1). 
  invert H2.
  intros.
  constructor.
  constructor.
  intros. 
  apply inc_emp. 
  Search (_ ++ _ =nil).  
  pose proof List.app_eq_nil.
  specialize (H2 event rho1 rho2 H3). 
  destr H2. 
  constructor. 
  subst. 
  pose proof trace_model_nil_indicate_nullable.
  specialize (H2 t1 nil H4). 
  apply H2. reflexivity.
  subst. 
  pose proof trace_model_nil_indicate_nullable.
  specialize (H2 t2 nil H5). 
  apply H2. reflexivity.
  intros.
  constructor.
  apply nullable_disj_left.
  subst. 
  pose proof trace_model_nil_indicate_nullable.
  specialize (H2 t1 nil H3).
  apply H2. reflexivity.
  intros.
  constructor.
  apply nullable_disj_right.
  subst. 
  pose proof trace_model_nil_indicate_nullable.
  specialize (H2 t2 nil H3).
  apply H2. reflexivity.
  intros. subst. 
  constructor.
  constructor. 
  intros. subst.
  constructor. constructor.
  -
  intros.
  pose inclusion_theta_der_indicate.
  specialize (e t2 t3 ev0 deriv2 H3 H1). 
  destr e. 
  specialize (IHinclusion deriv0 H6 ). 
  pose proof inc_unfold.   
  specialize (H4 t1 t3 ev0 deriv1 deriv0 H H0 H5 IHinclusion).
  exact H4. 
Qed. 




Lemma trace_model_prefix : forall rho t rho1 t1, 
  trace_model rho t -> 
  trace_model rho1 t1 -> 
  trace_model (rho++rho1) (seq t t1).
Proof.
  intros.
  gen rho1 t1. 
  induction H.
  - 
  intros. constructor. constructor. exact H0.
  -    
  intros. subst. constructor. constructor. reflexivity. exact H0.     
  - 
  intros. subst. specialize (IHtrace_model1 rho0 t0 H1).   
  intros. subst. specialize (IHtrace_model2 rho0 t0 H1).   
  invert IHtrace_model1.
  invert IHtrace_model2. 
  intros. subst.
  constructor.
  constructor. eauto. eauto. auto.
  - 
  intros.
  specialize (IHtrace_model rho1 t0 H0 ). 
  constructor.
  invert IHtrace_model. intros. subst.
  apply tm_disj_left. exact H.
  exact H0.
  - 
  intros. 
  specialize (IHtrace_model rho1 t0 H0 ). 
  constructor.
  invert IHtrace_model. intros. subst.
  apply tm_disj_right. exact H.
  exact H0.
  - 
  intros.
  constructor.
  constructor.
  exact H0.
  -
  intros.
  specialize (IHtrace_model rho1 t1 H0).  
  invert IHtrace_model.
  intros. subst. rewrite H1. 
  constructor.
  constructor. exact H. 
  exact H0.   
Qed.

Inductive futureCondEntail : futureCond -> futureCond -> Prop := 
  | futureCondEntail_empty : forall t1 t2, 
    inclusion t1 t2 -> 
    futureCondEntail (fc_singleton t1) (fc_singleton t2)

  | futureCondEntail_conj_LHS_1 : forall f1 f2 f, 
    futureCondEntail f1 f -> 
    futureCondEntail (fc_conj f1 f2) f 

  | futureCondEntail_conj_LHS_2 : forall f1 f2 f, 
    futureCondEntail f2 f -> 
    futureCondEntail (fc_conj f1 f2) f 

  | futureCondEntail_conj_RHS : forall f1 f2 f, 
    futureCondEntail f f1 -> 
    futureCondEntail f f2 -> 
    futureCondEntail f (fc_conj f1 f2) 
 .



Theorem futureCond_sound : forall f1 f2 rho, 
  futureCondEntail f1 f2 -> 
  fc_model rho f1 -> 
  fc_model rho f2.
Proof. 
  intros.
  gen rho0.
  induction H. 
  - 
  intros.   
  invert H0. 
  intros.
  subst.   
  constructor.
  pose proof inclusion_sound.
  specialize (H0 t1 t2 rho0 H H3). 
  eapply H0. 
  - intros. specialize (IHfutureCondEntail rho0).
  apply IHfutureCondEntail.
  invert H0.
  intros. subst.
  exact H4.    
  - intros. apply IHfutureCondEntail. 
  invert H0.   
  intros. subst.
  exact H5.
  -
  intros.
  specialize (IHfutureCondEntail1 rho0 H1).     
  specialize (IHfutureCondEntail2 rho0 H1).
  constructor.
  exact IHfutureCondEntail1. 
  exact IHfutureCondEntail2.
Qed.         


Lemma inclusion_futureCondEntail: forall t1 t2 f, 
  inclusion t1 t2 -> 
  futureCondEntail (fc_singleton t2) f -> 
  futureCondEntail (fc_singleton t1) f.
Proof.  
Admitted.  


Theorem futureCond_trans : forall f1 f2 f3, 
  futureCondEntail f1 f2 -> 
  futureCondEntail f2 f3 -> 
  futureCondEntail f1 f3.
Proof.
  intros.
  gen f3.
  induction H.
  - 
  intros.
  invert H0.
  intros. subst. constructor. 
  pose proof inclusion_trans.
  apply (H0 t1 t2 t3). exact H. exact H2. 
  intros. subst.
  apply futureCondEntail_conj_RHS.
  pose proof inclusion_futureCondEntail. 
  specialize (H0 t1 t2 f1 H H1). exact H0.
  pose proof inclusion_futureCondEntail. 
  specialize (H0 t1 t2 f2 H H2). exact H0.
  -
  intros. specialize (IHfutureCondEntail f3 H0). 
  apply futureCondEntail_conj_LHS_1. exact IHfutureCondEntail. 
  - 
  intros. specialize (IHfutureCondEntail f3 H0). 
  apply futureCondEntail_conj_LHS_2. exact IHfutureCondEntail.
  -
  intros.
  invert H1.
  +
  intros. subst. specialize (IHfutureCondEntail1 f3 H5). exact IHfutureCondEntail1.
  +
  intros. subst. specialize (IHfutureCondEntail2 f3 H5). exact IHfutureCondEntail2.
  + 
  intros. subst.  
  invert H2.
  * intros. subst. apply futureCondEntail_conj_RHS. 
    exact (IHfutureCondEntail1 f0 H6).
    invert H3.
    intros. subst. exact (IHfutureCondEntail1 f4 H5).
    intros. subst. exact (IHfutureCondEntail2 f4 H5).
 
Admitted.  

Axiom futureCond_distr : forall f1 f2 f3, 
  fc_conj (fc_conj f1 f2) f3 = 
  fc_conj f2 (fc_conj f1 f3).
  
Axiom futureCond_distr1 : forall f1 f2 f3, 
  fc_conj (fc_conj f1 f2) f3 = 
  fc_conj f1 (fc_conj f2 f3).

Axiom futureCond_distr2 : forall f1 f2 f3, 
  fc_conj (fc_conj f1 f2) f3 = 
  fc_conj (fc_conj f1 f3) (fc_conj f2 f3).


Theorem futureCond_distribution : forall f1 f2 f3 f4, 
  futureCondEntail f1 f2 -> 
  futureCondEntail f3 f4 -> 
  futureCondEntail (fc_conj f1 f3) (fc_conj f2 f4).
Proof.
  intros.
  gen f3 f4.
  induction H.
  - intros. 
  apply futureCondEntail_conj_RHS.  
  apply futureCondEntail_conj_LHS_1.  
  constructor.
  exact H.
  apply futureCondEntail_conj_LHS_2.
  exact H0.
  - 
  intros.
  specialize (IHfutureCondEntail f3 f4 H0). 
  rewrite futureCond_distr. 
  apply futureCondEntail_conj_LHS_2.
  exact IHfutureCondEntail.
  -
  intros.
  specialize (IHfutureCondEntail f3 f4 H0).
  rewrite futureCond_distr1. 
  apply futureCondEntail_conj_LHS_2.
  exact IHfutureCondEntail.
  -
  intros.
  specialize (IHfutureCondEntail1 f3 f4 H1).
  specialize (IHfutureCondEntail2 f3 f4 H1).

  rewrite futureCond_distr2. 
  apply futureCondEntail_conj_RHS.
  exact IHfutureCondEntail1.
  exact IHfutureCondEntail2.
Qed.

Axiom futureCond_excahnge : forall f1 f2, 
  fc_conj f1 f2 = fc_conj f2 f1. 


Theorem strong_LHS_futureEnatil : forall f1 f2 f3, 
  futureCondEntail f1 f2 -> 
  futureCondEntail (fc_conj f1 f3) f2.
Proof.
  intros.
  apply futureCondEntail_conj_LHS_1.
  exact H.
Qed.

Definition trace_default := (kleene (theta_singleton any)). 

Definition fc_default := fc_singleton(kleene (theta_singleton any)). 


Axiom f_conj_kleene_any_is_f : forall f, 
   fc_conj (fc_default) f = f. 

Axiom inclusion_exact: forall t, 
  inclusion t t.


Axiom futureCondEntail_exact : forall f,  
  futureCondEntail f f .

Axiom anything_entail_default : forall t,  
  inclusion t ((trace_default)).
    
Lemma anything_future_entail_default : forall f,  
  futureCondEntail f (fc_default).
Proof.
  intros. 
  induction f.
  - constructor. 
  exact (anything_entail_default t).
  - 
  apply futureCondEntail_conj_LHS_1. 
  exact IHf1.
Qed.   


Lemma fc_singleton_to_trace : forall rho t, 
  fc_model rho (fc_singleton t) -> 
  trace_model rho t.
Proof.
  intros. 
  invert H.
  intros.
  exact H2.
Qed. 

Lemma fc_conj_to_trace : forall rho f1 f2, 
  fc_model rho (fc_conj f1 f2) -> 
  fc_model rho f1 /\ fc_model rho f2.
Proof.
  intros. 
  invert H.
  intros. subst. split. exact H3. exact H4.
Qed.     



Lemma trace_to_fc_singleton : forall rho t, 
  trace_model rho t -> 
  fc_model rho (fc_singleton t). 
Proof.
  intros.
  invert H.
  - intros. subst.
    constructor.
    constructor.
  - intros. subst.
    constructor. constructor. reflexivity.
  - intros. subst. constructor. constructor. 
  exact H0. exact H1.   
  - intros. subst. constructor. 
    constructor. exact H0. 
  - intros. subst. constructor. 
    apply tm_disj_right.  exact H0.
  - intros. subst. constructor. constructor. 
  - intros. subst. constructor. constructor. exact H0.
Qed. 

Lemma trace_model_consequent: forall rho t1 t2, 
  trace_model rho t1 -> 
  inclusion t1 t2 ->
  trace_model rho t2.
Proof. 
  intros.
  pose proof inclusion_sound.
  specialize (H1 t1 t2 rho0 H0 H).
  exact H1.
Qed.   




Inductive futureSubtraction : futureCond -> theta -> futureCond -> Prop :=  
  | futureSubtraction_conj : forall f1 f2 f3 f4 t, 
    futureSubtraction f1 t f3 ->
    futureSubtraction f2 t f4 -> 
    futureSubtraction (fc_conj f1 f2) t (fc_conj f3 f4)

  | futureSubtraction_base : forall t, 
    futureSubtraction (fc_singleton t) emp (fc_singleton t)

  | futureSubtraction_induc : forall ev f f_der t t_der res, 
    fc_der f ev f_der -> 
    theta_der t ev t_der ->  
    futureSubtraction f_der t_der res -> 
    futureSubtraction f t res. 


Fixpoint concate_trace_fc (t:theta) (f:futureCond)  : futureCond :=
  match f with 
  | fc_singleton t1 => fc_singleton (seq t t1)
  | fc_conj f1 f2 => fc_conj (concate_trace_fc t f1) (concate_trace_fc t f2)
  end. 

Axiom fc_model_theta_der_indicate : forall rho0 t ev0 t_der res, 
  fc_model rho0 (concate_trace_fc t res) -> 
  theta_der t ev0 t_der -> 
  exists rho, 
  fc_model rho (concate_trace_fc t_der res) /\ rho0 = ev0 :: rho. 

Axiom fc_der_fc_model_indicate: forall f ev0 f_der rho1, 
  fc_der f ev0 f_der -> 
  fc_model rho1 f_der -> 
  fc_model (ev0::rho1) f. 


Theorem futureSubtraction_cound : forall f t f_der rho, 
  futureSubtraction f t f_der -> 
  fc_model rho (concate_trace_fc t f_der) -> 
  fc_model rho f. 
Proof. 
  intros. 
  gen rho0. 
  induction H. 
  - 
  intros. 
  unfold concate_trace_fc in H1. 
  fold concate_trace_fc in H1. 
  invert H1. 
  intros. subst. 
  specialize (IHfutureSubtraction1 rho0 H5).
  specialize (IHfutureSubtraction2 rho0 H6). 
  constructor. 
  exact IHfutureSubtraction1. 
  exact IHfutureSubtraction2. 
  -
  intros. 
  unfold concate_trace_fc in H0. 
  fold concate_trace_fc in H0. 
  invert H0. 
  intros. subst. 
  Search (nil ++ _). 
  pose proof List.app_nil_l. 
  specialize (H event rho0). 
  rewrite  <-  H in H2.  
  invert H2. 
  intros. subst. 
  invert H4. 
  intros. subst. 
  constructor. 
  Search (nil ++ _). 
  rewrite List.app_nil_l in H3.  
  rewrite List.app_nil_l in H3.  subst. 
  exact H5. 
  -
  intros.  
  pose fc_model_theta_der_indicate as H3. 
  specialize (H3 rho0 t ev0 t_der res H2 H0). 
  destr H3. 
  specialize (IHfutureSubtraction rho1 H3).  
  rewrite H5. 
  pose proof fc_der_fc_model_indicate as H4. 
  specialize (H4 f ev0 f_der rho1 H IHfutureSubtraction).  
  exact H4. 
Qed. 
  


Inductive futureSubtraction_linear : futureCond -> rho -> futureCond -> Prop :=  
  | futureSubtraction_linear_conj : forall f1 f2 f3 f4 t, 
    futureSubtraction_linear f1 t f3 ->
    futureSubtraction_linear f2 t f4 -> 
    futureSubtraction_linear (fc_conj f1 f2) t (fc_conj f3 f4)

  | futureSubtraction_linear_base : forall t, 
    futureSubtraction_linear (fc_singleton t) nil (fc_singleton t)

  | futureSubtraction_linear_induc : forall ev f f_der rho rho1 res, 
    fc_der f ev f_der -> 
    rho = ev::rho1  ->  
    futureSubtraction_linear f_der rho1 res -> 
    futureSubtraction_linear f rho res. 



Inductive bigstep : heap -> rho -> futureCond -> expr -> heap -> rho -> futureCond -> val -> Prop :=

  | eval_plet : forall h1 h2 h3 x e1 e2 v r rho1 rho2 rho3 f1 f2 f3,
    bigstep h1 rho1 f1 e1 h2 rho2 f2 v ->
    bigstep h2 rho2 f2 (subst x v e2) h3 rho3 f3 r ->
    bigstep h1 rho1 f1 (plet x e1 e2) h3 rho3 f3 r
  
  | eval_const : forall h r f v, 
    bigstep h r f (pval v) h r f v 

  
  | eval_if_true : forall h r f e1 e2 h' r' f' v, 
    bigstep h r f e1 h' r' f' v -> 
    bigstep h r f (pif (pval (vbool true)) e1 e2) h' r' f' v

  | eval_if_false : forall h r f e1 e2 h' r' f' v, 
    bigstep h r f e2 h' r' f' v -> 
    bigstep h r f (pif (pval (vbool false)) e1 e2) h' r' f' v

  | eval_assume : forall h r f f_assume, 
    bigstep h r f (passume f_assume) h r (fc_conj f f_assume) vunit

  | eval_event : forall h r f ev f', 
    futureSubtraction f (theta_singleton ev) f' -> 
    bigstep h r f (pevent ev) h (r ++ (ev::nil)) f' vunit

  | eval_pderef : forall h r f loc,
    Fmap.indom h loc ->
    bigstep h r f (pderef (pval (vloc loc))) h r f (Fmap.read h loc)

  | eval_passign : forall h r f loc v,
    Fmap.indom h loc ->
    bigstep h r f (passign (pval (vloc loc)) (pval v)) (Fmap.update h loc v) r f vunit

  | eval_app : forall fromal_arg e actual_arg h1 h2 rho1 rho2 f1 f2 v, 
    bigstep h1 rho1 f1 (subst fromal_arg actual_arg e) h2 rho2 f2 v -> 
    bigstep h1 rho1 f1 (papp (pval (vfun fromal_arg e)) (pval actual_arg)) h2 rho2 f2 v

  | eval_pref : forall h r f loc v,
    ~ Fmap.indom h loc ->
    bigstep h r f (pref (pval v)) (Fmap.update h loc v) r f (vloc loc)

. 



Inductive forward : hprop -> theta -> futureCond -> expr -> (val -> hprop) -> theta -> futureCond -> Prop := 


  | fw_consequence: forall P1 P2 P3 P4 t' f' t f e, 
    forward P3 emp (fc_singleton (trace_default)) e P4 t' f' -> 
    P1 ==> P3 -> 
    P4 ===> P2 -> 
    inclusion t' t -> 
    futureCondEntail f f' -> 
    forward P1 emp (fc_singleton (trace_default)) e P2 t f

  | fw_frame: forall P Q t F e P_frame, 
    forward P emp (fc_singleton (trace_default)) e Q t F -> 
    forward (P\*P_frame) emp (fc_singleton (trace_default)) e (Q\*+P_frame) t F 


  | fw_let : forall x e1 e2 P Q Q1 t2 t3 f2 f3, 
    forward P emp (fc_singleton (trace_default)) e1 Q t2 f2  -> 
    (forall v, forward (Q v) t2 f2 (subst x v e2) Q1 t3 f3 ) -> 
    forward P emp (fc_singleton (trace_default)) (plet x e1 e2) Q1 t3 f3
  
  | fw_val: forall v P ,
    forward P emp (fc_singleton (trace_default)) (pval v) (fun res => P \* \[res = v]) emp (fc_singleton (trace_default))

  | fw_event: forall P (ev:event) ,
    forward P emp (fc_singleton (trace_default)) (pevent ev) (fun res => P \* \[res = vunit]) (theta_singleton ev) (fc_singleton (trace_default))

  | fw_cond : forall (b:bool) e1 e2 t f P Q, 
    forward P emp (fc_singleton (trace_default)) (if b then e1 else e2) Q t f -> 
    forward P emp (fc_singleton (trace_default)) (pif (pval (vbool b)) e1 e2) Q t f

  | fw_deref : forall loc v, 
    forward (loc ~~> v) emp (fc_singleton (trace_default)) (pderef (pval(vloc loc))) (fun res => (loc ~~> v) \* \[res = v]) emp (fc_singleton (trace_default))

  | fw_assign : forall loc v v', 
    forward (loc ~~> v') emp (fc_singleton (trace_default)) (passign (pval(vloc loc)) (pval v)) (fun res => (loc ~~> v) \* \[res = vunit])  emp (fc_singleton (trace_default))

  | fw_assume : forall P f1, 
    forward P emp (fc_singleton (trace_default)) (passume f1) (fun res => P \* \[res = vunit]) emp f1

  | fw_app : forall fromal_arg e actual_arg P Q t f, 
    forward P emp (fc_singleton (trace_default)) (subst fromal_arg actual_arg e) Q t f  -> 
    forward P emp (fc_singleton (trace_default)) (papp (pval (vfun fromal_arg e)) (pval actual_arg)) Q t f

  | fw_structural: forall P Q t f f_ctx t_ctx f_ctx' e, 
    forward P emp (fc_singleton (trace_default)) e Q t f -> 
    futureSubtraction f_ctx t f_ctx' -> 
    forward P t_ctx f_ctx e Q (seq t_ctx t) (fc_conj f_ctx' f)

(*
  | fw_ref : forall v, 
    forward \[] emp (fc_singleton (trace_default)) (pref (pval v)) (fun res => \exists p, \[res = vloc p] \* p ~~> v) emp (fc_singleton (trace_default))
    *)
.



Axiom subtractFromTrueISTrue: forall ev f, 
  futureSubtraction (fc_singleton (trace_default))
(theta_singleton ev) f -> f = (fc_singleton (trace_default)).
   
Axiom futureCondEntailTrueISTrue: forall f, 
  futureCondEntail (fc_singleton (trace_default)) f -> f = (fc_singleton (trace_default)).

Lemma weaken_futureCond_big_step : forall h1 r1 f1 e h2 r2 f2 v f3, 
  bigstep h1 r1 f1 e h2 r2 f2 v -> 
  futureCondEntail f1 f3 -> 
  exists f4,  
  bigstep h1 r1 f3 e h2 r2 f4 v /\ 
  futureCondEntail f2 f4.
Proof.
  intros. 
  gen f3. 
  induction H.
  - 
  intros. 
  specialize (IHbigstep1 f0 H1). 
  destr IHbigstep1.
  specialize (IHbigstep2 f4 H4). 
  destr IHbigstep2. 
  exists f5.
Admitted.   

Lemma strenthen_futureCond_big_step : forall h1 r1 f1 e h2 r2 f2 v f3, 
  bigstep h1 r1 f1 e h2 r2 f2 v -> 
  futureCondEntail f3 f1 -> 
  exists f4,  
  bigstep h1 r1 f3 e h2 r2 (fc_conj f4 f2) v. 
Proof. Admitted.  

Lemma future_frame_big_step : forall P e Q t f h3 rho3 f4 h2 rho2 f0 v f1, 
  forward P emp (fc_singleton (trace_default)) e Q t f -> 
  bigstep h3 rho3 f4 e h2 rho2 f0 v -> 
  futureSubtraction f4 t f1 -> 
  futureCondEntail f1 f0. 
Proof. Admitted.  

Lemma future_frame_big_step_aux : forall P e Q t f h1 rho1 f1 h2 rho2 f2 v, 
  forward P emp (fc_singleton (trace_default)) e Q t f -> 
  bigstep h1 rho1 f1 e h2 rho2 f2 v -> 
  exists rho3 f3, 
  bigstep h1 nil (fc_singleton (trace_default)) e h2 rho3 f3 v /\ 
  rho2 = rho1 ++ rho3 /\ futureCondEntail f f3 /\ futureCondEntail f2 f3
  . 
Proof. Admitted.  

Axiom strengthening_futureSubtraction_residue: forall f t f1 f2, 
  futureSubtraction f t f1 -> 
  futureSubtraction f t (fc_conj f1 f2)
.  

Axiom fc_comm: forall f1 f2, fc_conj f1 f2 = fc_conj f2 f1. 

Lemma weakening_futureSubtraction: forall f1 t f2 f3, 
  futureSubtraction f1 t f2 -> 
  futureCondEntail f1 f3 -> 
  futureSubtraction f3 t f2. 
Proof. 
  intros. 
  gen f3.
  induction H.
  - intros. 
  invert H1.
  intros. subst. specialize (IHfutureSubtraction1 f0 H5). 
  pose strengthening_futureSubtraction_residue as H1.
  specialize (H1 f0 t f3 f4 IHfutureSubtraction1). 
  exact H1.
  intros. subst. specialize (IHfutureSubtraction2 f0 H5). 
  pose strengthening_futureSubtraction_residue as H1.
  specialize (H1 f0 t f4 f3 IHfutureSubtraction2). 
  rewrite fc_comm.  exact H1.
 Admitted.  

(* to prove the let rule *)
Lemma strengthening_futureCond_from_pre: forall h3 rho3 f4 e h2 rho2 f0 v Q t2 f2 Q1 t3 f3 , 
  bigstep h3 rho3 f4 e h2 rho2 f0 v -> 
  forward Q t2 f2 e Q1 t3 f3 -> 
  futureCondEntail f2 f4 -> 
  exists x0, 
  bigstep h3 rho3 f2 e h2 rho2 (fc_conj x0 f0) v /\ futureCondEntail f3 f0. 
Proof. 
  intros.
  gen h3 rho3 f4 h2 rho2 f0 v. 
  induction H0. 

  -
  intros. 
  specialize (IHforward h3 rho3 f4 H4 h2 rho2 f0 v H5). 
  destr IHforward. 
  exists x0.
  split.
  exact H7.
  pose proof futureCond_trans.
  specialize (H6 f f' f0 H3 H8). 
  exact H6.
  -
  intros. 
  specialize (IHforward h3 rho3 f4 H1 h2 rho2 f0 v H). 
  destr IHforward. 
  exists x0. 
  split.
  exact H3.
  exact H4.
  - 
  intros.  
  pose proof H3. 
  invert H3. 
  intros.
  subst. 
  specialize (IHforward h3 rho3 f4 H2 h0 rho0 f5 v0 H15 ).
  destr IHforward.
  specialize (H1 v0 h0 rho0 f5 H6 h2 rho2 f0 v H16). 
  destr H1.
  exists ((fc_singleton (trace_default))).
  split.
  pose futureCondEntailTrueISTrue as H3.
  specialize (H3 f4 H2). subst. 
  rewrite  f_conj_kleene_any_is_f.
  exact H4. exact H7.
  - 
  intros.
  pose futureCondEntailTrueISTrue as H0.
  specialize (H0 f4 H1). subst. 
  exists ((fc_singleton (trace_default))).
  split.
  rewrite  f_conj_kleene_any_is_f.
  exact H. invert H.
  intros. subst.
  apply futureCondEntail_exact.
  - 
  intros.
  pose proof futureCondEntailTrueISTrue.
  specialize (H0 f4 H1). subst.
  exists ((fc_singleton (trace_default))).
  split.
  rewrite  f_conj_kleene_any_is_f.
  exact H. invert H.
  intros. subst.
  pose subtractFromTrueISTrue as H.
  specialize (H ev0 f0 H5). subst.  
  apply futureCondEntail_exact.
  - intros.
  induction b.
  + 
  invert H.
  intros. subst.  
  specialize (IHforward h3 rho3 f4 H1 h2 rho2 f0 v H11). 
  destr IHforward. 
  exists (x0).
  split. constructor. exact H2. exact H3.
  + 
  invert H.
  intros. subst.  
  specialize (IHforward h3 rho3 f4 H1 h2 rho2 f0 v H11). 
  destr IHforward. 
  exists (x0).
  split. constructor. exact H2. exact H3. 

  - 
  intros. 
  invert H.
  intros. subst.  
  pose futureCondEntailTrueISTrue as H.
  specialize (H f0 H1). subst. 
  exists ((fc_singleton (trace_default))).
  split.
  rewrite  f_conj_kleene_any_is_f.
  constructor. exact H5.
  apply futureCondEntail_exact.

  - intros.
  invert H. intros. subst. 
  exists ((fc_singleton (trace_default))).
  rewrite  f_conj_kleene_any_is_f.
  split. 
  pose futureCondEntailTrueISTrue as H.
  specialize (H f0 H1). subst. 
  constructor.  exact H10.
  exact H1.
  - intros.
  invert H. intros. subst. 
  exists ((fc_singleton (trace_default))).
  rewrite  f_conj_kleene_any_is_f.
  pose futureCondEntailTrueISTrue as H.
  specialize (H f4 H1). subst. 
  split. 
  constructor.
  rewrite  f_conj_kleene_any_is_f. 
  apply futureCondEntail_exact. 

  - 
  intros.  
  invert H.  
  intros. subst.   
  specialize (IHforward h3 rho3 f4 H1 h2 rho2 f0 v H12). 
  destr IHforward. 
  exists x0.
  pose futureCondEntailTrueISTrue as H.
  specialize (H f4 H1). subst. 
  split. 
  constructor. 
  exact H2. exact H3.       

  - intros.
  pose proof futureCondEntail_exact.
  specialize (H3 (fc_singleton (trace_default))).
  pose proof weaken_futureCond_big_step.
  pose proof anything_future_entail_default. 
  specialize (H5 f4). 
  specialize (H4 h3 rho3 f4 e h2 rho2 f0 v (fc_singleton (trace_default)) H2 H5).   
  destr H4. 
  specialize (IHforward h3 rho3 (fc_singleton (trace_default)) H3 h2 rho2 f1 v H4). 
  destr IHforward.

  pose proof strenthen_futureCond_big_step.
  specialize (H6 h3 rho3 f4 e h2 rho2 f0 v f_ctx H2 H1 ). 
  destr H6.
  exists f2.
  split. exact H10. 
  pose proof weakening_futureSubtraction. 
  specialize (H6 f_ctx t f_ctx' f4 H H1). 
  pose proof future_frame_big_step.
  specialize (H11 P e Q t f h3 rho3 f4 h2 rho2 f0 v f_ctx' H0 H2 H6). 

  pose proof strong_LHS_futureEnatil.
  specialize (H12 f_ctx' f0 f H11).
  exact H12.  
Qed. 

Lemma heap_disjoint_consequence: forall [A B : Type] (h1:Fmap.fmap A B) h2 h3 h4, 
  Fmap.disjoint h1 h2 -> 
  h1 = h3 \u h4 -> 
  Fmap.disjoint h3 h2 /\ Fmap.disjoint h4 h2. 
Proof.
  Search (Fmap.disjoint _ _ -> _ ).
  intros.
  split.
  (*
  fmap_disjoint.
  fmap_disjoint.
  *)
  eauto.
  info_eauto. 
  (*
  disjoint_union_eq_l
  disjoint_union_eq_r
  disjoint_3_unfold : rew_disjoint.
  *)
Qed.

Lemma heap_disjoint_consequence_aux: forall [A B : Type] (h1:Fmap.fmap A B) h2 h3, 
  Fmap.disjoint h1 h2 -> 
  Fmap.disjoint h2 h3 -> 
  Fmap.disjoint h1 h3-> 
  Fmap.disjoint h1 (h2 \u h3). 
Proof. 
  intros.
    pose proof  disjoint_union_eq_r. 
  info_eauto.
Qed. 

Lemma heap_framing_bigstep : forall h1 rho1 f1 e h2 rho2 f2 v h4, 
  bigstep h1 rho1 f1 e h2 rho2 f2 v -> 
  Fmap.disjoint h1 h4 -> 
  bigstep (h1\u h4) rho1 f1 e (h2\u h4) rho2 f2 v. 
Proof. Admitted. 

(* to prove the frame rule *)
Lemma frame_big_step: forall h1 h2 h3 h_frame e t f1 f2 v P Q rho1 rho2 F , 
  forward P emp (fc_singleton (trace_default)) e Q t F -> 
  bigstep h1 rho1 f1 e h2 rho2 f2 v -> 
  P h3 -> 
  Fmap.disjoint h3 h_frame->
  h1 = h3 \u h_frame -> 
  exists h4, 
  Fmap.disjoint h4 h_frame /\ h2 = h4 \u h_frame /\ bigstep h3 rho1 f1 e h4 rho2 f2 v. 
Proof. 
  intros.
  gen h1 rho1 f1 h2 rho2 f2 v h3 h_frame. 
  induction H. 
  -
  intros.
  unfold himpl in H0.
  specialize (H0 h3 H5).  
  specialize (IHforward h1 rho1 f1 h2 rho2 f2 v H4 h3 H0 h_frame H6 H7). 
  destr IHforward.
  exists h4.
  split. exact H9. split. exact H8. exact H11.
  - 
  intros.
  Search ((_ \* _) _).
  apply hstar_inv in H1. 
  destr H1.  
  specialize (IHforward h1 rho1 f1 ).
  pose proof heap_disjoint_consequence. 
  specialize (H6 loc Val.value h3 h_frame h0 h4 H2 H7 ).  
  destr H6.
  pose proof heap_disjoint_consequence_aux. 
  specialize (H6 loc Val.value  h0 h4 h_frame H5 H9 H8). 
  specialize (IHforward h2 rho2 f2 v H0 h0 H4 (h4\u h_frame) H6 ).
  Search ((_ \u _) \u _).  
  pose proof Fmap.union_assoc. 
  rewrite H3 in IHforward.
  rewrite H7 in IHforward.
  specialize (H10 loc Val.value h0 h4 h_frame ). 
  specialize (IHforward H10). 
  destr IHforward.
  exists (h5 \u h4).
  subst. 
  split.
  eauto.
  split.
  eauto.
  pose proof heap_framing_bigstep. 
  specialize (H3 h0 rho1 f1 e h5 rho2 f2 v h4 H14 H5).
  exact H3.
  -
  intros.
  
Admitted. 


Lemma bigstep_frame : forall h1 rho1 f_ctx e h2 rho2 f3 v rho3 f0 f_ctx', 
  bigstep h1 rho1 f_ctx e h2 rho2 f3 v -> 
  bigstep h1 nil (fc_singleton (trace_default)) e h2 rho3 f0 v ->
  futureSubtraction_linear f_ctx rho3 f_ctx' /\ 
  f3 = fc_conj f_ctx' f0. 
Proof. 
Admitted. 


Theorem soundness : forall P e Q t1 t2 rho1 rho2 h1 v h2 f1 f2 f3,
  forward P t1 f1 e Q t2 f2 ->  
  P h1 -> 
  trace_model rho1 t1 -> 
  bigstep h1 rho1 f1 e h2 rho2 f3 v ->  
  Q v h2 /\ trace_model rho2 t2 /\ futureCondEntail f2 f3.  
Proof. 
  introv.
  intros. 
  gen h1 v h2 rho1 rho2 f3.
  induction H.
  - (* consequence *)
  intros.
  unfold himpl in H0. 
  specialize (H0 h1 H4).  
  specialize (IHforward h1 H0 v h2 rho1 H5 rho2 f3 H6). 
  destr IHforward. 
  split.
  unfold qimpl, himpl in H1.  
  specialize (H1 v h2 H7). 
  exact H1.
  split.
  pose proof inclusion_sound.
  specialize (H8 t' t rho2 H2 H9).
  exact H8.
  pose proof futureCond_trans.
  specialize (H8 f f' f3 H3 H10). 
  exact H8. 
  - (* frame *)
  intros.
  apply hstar_inv in H0. 
  destruct H0 as (h0&h4&H8&H9&H10&H11).  
  pose proof frame_big_step.
  specialize (H0 h1 h2 h0 h4 e t (fc_singleton (trace_default)) f3 v P Q rho1 rho2 F H H2 H8 H10 H11). 
  destruct H0 as (h5&H12&H13&H14).    

  specialize (IHforward h0 H8 v h5 rho1 H1 rho2 f3 H14). 
  destruct IHforward as (H15&H16&H17).
  split.
  + rewrite H13.
  Search ((_ \* _) (_ \u _)).  
  apply hstar_intro. exact H15. exact H9. exact H12.  
  + split. exact H16. exact H17.   
  
  - (* let *)
  intros.
  invert H4. intros. subst.
  specialize (IHforward h1 H2 v0 h3 rho1).
  specialize (IHforward H3 rho3 f4 H15).
  destr IHforward.
  specialize (H0 v0). 
  pose proof strengthening_futureCond_from_pre.
  specialize (H5 h3 rho3 f4 (subst x v0 e2) h2 rho2 f0 v (Q v0) t2 f2 Q1 t3 f3 H16 H0 H7). 
  destruct H5 as (x0&H5&H18). 
  specialize(H1 v0 h3 H4 v h2 rho3 H6 rho2 (fc_conj x0 f0) H5).
  destruct H1. destruct H8.
  split.
  exact H1.
  split.
  exact H8. 
  exact H18. 

  - (* val *)
  intros.
  invert H2.
  intros. subst.
  split.
  rewrite hstar_hpure_r.
  split. subst. auto.
  reflexivity.
  split. subst. auto.
  apply futureCondEntail_exact.

  - (* event *)
  intros.
  invert H2.
  intros. subst.
  split.
  rewrite hstar_hpure_r.
  split.
  exact H0. 
  reflexivity.
  split.
  pose proof trace_model_emp_must_nil.
  specialize (H rho1 H1).
  subst.
  Search (nil ++ _). 
  rewrite List.app_nil_l. 
  constructor. reflexivity.
  pose subtractFromTrueISTrue as H. 
  specialize (H ev0 f3 H6). 
  subst.
  apply futureCondEntail_exact. 

  - (* if-else *)
  intros.
  invert H2.
  intros. subst.
  eapply IHforward.
  eapply H0.
  eapply H1.
  exact H13.
  intros. subst.
  eapply IHforward.
  eapply H0.
  eapply H1.
  exact H13.
  
  - (* deref *) 
  intros.
  invert H2.
  intros. subst.
  split.
  rewrite hstar_hpure_r. 
  split. exact H0. 
  apply hsingle_inv in H0.
  rewrite H0.
  apply Fmap.read_single. 
  split. 
  exact H1. 
  apply futureCondEntail_exact.



  - (* assign *) 
  intros.
  invert H2.
  intros. subst.
  split.
  rewrite hstar_hpure_r.
  split. 
  apply hsingle_inv in H0.
  rewrite H0.
  rewrite Fmap.update_single.
  Search (Fmap.single _ _ ). 
  apply hsingle_intro. 
  reflexivity. 
  split.  exact H1. 
  apply futureCondEntail_exact.

  - (*assume*)
  intros.
  invert H2.
  intros. subst.
  split. 
  rewrite hstar_hpure_r. subst.
  split. exact H0.
  reflexivity.
  split.
  exact H1.
  rewrite  f_conj_kleene_any_is_f. 
  apply futureCondEntail_exact.

  - (* fun call *)
  intros.
  invert H2.
  intros. subst.  
  specialize (IHforward h1 H0 v h2 rho1 H1 rho2 f3 H13). 
  destr IHforward.
  split.
  exact H2.
  split. 
  exact H4. exact H5.     

  - (* STRUCTURAL RULE *) 
  intros. 
  pose proof future_frame_big_step_aux.
  specialize (H4 P e Q t f h1 rho1 f_ctx h2 rho2 f3 v H H3). 
  destr H4.  
  specialize (IHforward h1 H1 v h2 nil tm_emp rho3 f0 H5). 
  destr IHforward.
  split.
  exact H7.
  split.
  subst.   
  constructor.
  exact H2. exact H10.
  subst.
  pose proof bigstep_frame.
  specialize (H4 h1 rho1 f_ctx e h2 (rho1 ++ rho3) f3 v rho3 f0 f_ctx' H3 H5). 
  destr H4.
  subst.   
  pose proof futureCond_distribution.
  specialize (H4 f_ctx' f_ctx' f f0).
  apply H4.
  apply futureCondEntail_exact.
  exact H11. 
Qed. 