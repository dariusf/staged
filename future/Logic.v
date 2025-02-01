(*

$ opam pin add coq 8.18.0
$ opam install vscoq-language-server

$ which vscoqtop

opam pin add vscoq-language-server.2.2.2  https://github.com/coq/vscoq/releases/download/v2.2.2/vscoq-language-server-2.2.2.tar.gz
*)

From Coq Require Import Classes.RelationClasses.
From Coq Require Morphisms Program.Basics.

From Lib Require Export HeapF.
From Lib Require Export LibFmap.
From Lib Require Export ExtraTactics.

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
  | passign (x: expr) (v: expr)
  | passume (f:futureCond)
  | papp (f: expr) (e: expr)
  | pseq (e1:expr) (e2:expr)
  | plet (x: var) (e1 e2: expr)
  | pref (v: expr)
  | pderef (v: expr)
  | pfree (e:expr)
  | popen (x: val)
  | pclose (e:expr)
  . 



Definition trace_default := (kleene (theta_singleton any)). 
Definition fc_default := fc_singleton(kleene (theta_singleton any)). 

Definition trace_finally ev := (seq trace_default (theta_singleton ev)). 
Definition fc_finally ev := fc_singleton (trace_finally ev). 

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
  | pfree t1 => pfree (aux t1)
  | popen x => e
  | pclose t1 => pclose (aux t1)
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

  | derivative_event_singleton_bot : forall ev1 ev2, 
    ev1 <> ev2 -> 
    theta_der (theta_singleton ev1) ev2 bot 


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

Axiom fc_model_rev: forall  f ev0 f_der rho0', 
  fc_der f ev0 f_der -> 
  fc_model rho0' f_der -> 
  fc_model (ev0 :: rho0') f. 


Lemma nullable_trans : forall t1 t2, 
  nullable t1 -> nullable t2 -> nullable (seq t1 t2).
Proof.
  intros.
  constructor.
  exact H. exact H0.
Qed.     


Axiom normal_emp : forall t, seq emp t = t. 
Axiom disj_not_bot: forall t1 t2, 
  disj t1 t2 <> bot -> 
  (t1 <> bot /\ t1=bot) \/ 
  (t2 <> bot /\ t2=bot) \/ 
  (t1 <> bot /\ t2 <> bot) .

Axiom seq_not_bot: forall t1 t2, 
  seq t1 t2 <> bot -> t1 <> bot /\ t2 <> bot.

Axiom fc_conj_not_bot: forall f1 f2, 
  fc_conj f1 f2 <> fc_singleton bot -> f1 <> fc_singleton bot /\ f2 <> fc_singleton bot.


Axiom seq_not_bot_rev: forall t1 t2, 
  t1 <> bot /\ t2 <> bot -> seq t1 t2 <> bot. 

Axiom disj_not_bot_rev: forall t1 t2, 
  t1 <> bot /\ t2 <> bot -> disj t1 t2 <> bot. 

Axiom theta_singleton_is_not_bot: forall ev, 
  theta_singleton ev <> bot. 

Axiom kleene_not_bot : forall t rho, 
  t <> bot -> 
  trace_model rho (kleene t) -> rho <> nil.
Axiom case_spliting_helper: forall (ev1:event) (ev2:event), 
  ev1 = ev2 \/ ev1 <> ev2. 

Axiom case_spliting_helper_bot: forall (t:theta) , 
  t = bot \/ t <> bot. 

Axiom futureCond_distr : forall f1 f2 f3, 
  fc_conj (fc_conj f1 f2) f3 = 
  fc_conj f2 (fc_conj f1 f3).
  
Axiom futureCond_distr1 : forall f1 f2 f3, 
  fc_conj (fc_conj f1 f2) f3 = 
  fc_conj f1 (fc_conj f2 f3).

Axiom futureCond_distr2 : forall f1 f2 f3, 
  fc_conj (fc_conj f1 f2) f3 = 
  fc_conj (fc_conj f1 f3) (fc_conj f2 f3).

Axiom futureCond_excahnge : forall f1 f2, fc_conj f1 f2 = fc_conj f2 f1. 

Axiom f_conj_kleene_any_is_f : forall f, fc_conj (fc_default) f = f. 

Axiom fc_comm: forall f1 f2, fc_conj f1 f2 = fc_conj f2 f1. 
Axiom fc_exact: forall f, fc_conj f f = f. 

Axiom fc_assio: forall f1 f2 f3, fc_conj f1 (fc_conj f2 f3) = fc_conj (fc_conj f1 f2) f3. 







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




Lemma theta_der_not_bot: forall t ev t_der, 
  theta_der t ev t_der -> 
  t_der <> bot -> 
  t <> bot. 
Proof. 
  intros. 
  induction H. 
  - false.
  - false.  
  - pose proof (theta_singleton_is_not_bot ).
    exact (H1 ev1).
  - false.
  - pose disj_not_bot. 
    specialize (o (seq t1_der t2) t2_der H0). 
    invert o.  
    intros.
    destr H3.
    false.
    intros.
    invert H3.
    intros. 
    destr H4.
    false.
    intros.
    destr H4.
    pose seq_not_bot.
    specialize (a t1_der t2 H3). 
    destr a.
    specialize (IHtheta_der1 H4).
    pose seq_not_bot_rev.
    specialize (n t1 t2). 
    apply n.
    split. exact IHtheta_der1. exact H6.
  - pose  (seq_not_bot ). 
    specialize (a t1_der t2 H0)  . 
    destr a. 
    specialize (IHtheta_der H1).
    pose seq_not_bot_rev.
    specialize (n t1 t2). 
    apply n.
    split. exact IHtheta_der. exact H2.
  - pose disj_not_bot. 
    specialize (o t1_der t2_der H0). 
    invert o.
    intros. destr H2.  false. 
    intros. invert H2. 
    intros.  destr H3. false.
    intros. destr H3.  
    specialize (IHtheta_der1 H2).
    specialize (IHtheta_der2 H4).
    pose proof disj_not_bot_rev. 
    eapply H3.
    split. exact IHtheta_der1. exact IHtheta_der2.
    -
    pose seq_not_bot.
    specialize (a t_der (kleene t) H0). 
    destr a.
    exact H2.
Qed.        


Axiom derivative_model_false : forall t1 ev0, 
  theta_der t1 ev0 bot -> false. 



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
  false.  
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
  (* Search (nil++ _ ).  *)
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

(* by definition *)
Axiom inclusion_rev : forall t1 t2 ev1 deriv0 deriv, 
  inclusion t1 t2 ->
  theta_der t1 ev1 deriv0 -> 
  theta_der t1 ev1 deriv0 -> 
  inclusion deriv0 deriv.   


Axiom emp_is_not_bot : emp <> bot. 
Axiom kleene_bot_is_emp : kleene bot = emp. 
Axiom kleene_emp_is_bot : kleene emp = bot. 
Axiom kleene_def : forall t, kleene t = emp \/ kleene t = seq t (kleene t). 

Axiom inclusion_exact: forall t, inclusion t t.
Axiom anything_entail_default : forall t, inclusion t ((trace_default)).
Axiom inclusion_bot: forall t, inclusion t bot -> t = bot .                

Lemma all_trace_have_derivative: forall t ev , 
  exists deriv, theta_der t ev deriv. 
Proof.
  intros.
  induction t.
  -
  exists bot. 
  constructor.
  -
  exists bot. 
  constructor.
  -
  pose proof case_spliting_helper. 
  specialize (H e ev0).
  invert H.
  intros.
  exists emp. 
  constructor. exact H0.
  exists bot.
  constructor. exact H0.
  -
  destr IHt1. 
  destr IHt2. 
  exists (seq deriv t2).
  constructor. exact H.
  -
  destr IHt1. 
  destr IHt2.
  exists (disj deriv deriv0).
  constructor.
  exact H. exact H0.
  -
  destr IHt.
  exists (seq deriv (kleene t)).
  constructor.
  exact H.
Qed.    




Lemma inclusion_theta_der_indicate : forall t1 t2 ev0 deriv1, 
  inclusion t1 t2 -> 
  theta_der t1 ev0 deriv1 -> 
  exists deriv2, 
  theta_der t2 ev0 deriv2 /\ inclusion deriv1 deriv2.
Proof.
  intros.  
  gen ev0 deriv1. 
  pose proof H. 
  invert H.
  - intros. subst. invert H3.
  intros. subst. 
  pose proof all_trace_have_derivative.
  specialize (H t2 ev0 ).
  destr H.
  exists deriv.
  split. exact H1. constructor.
  -
  intros. subst.
  invert H4.
  intros. subst. 
  pose proof all_trace_have_derivative.
  specialize (H t2 ev0 ). 
  destr H.
  exists deriv. 
  split. exact H2. constructor.  
  -
  intros. subst. 
  pose proof all_trace_have_derivative.
  specialize (H t2 ev1 ). 
  destr H.
  exists deriv. 
  split.
  exact H5.
  pose proof inclusion_rev.
  eapply H.
  exact H0.
  exact H7.
  exact H7.     
Qed. 


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
  (* Search (_ ++ _ =nil).   *)
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

  | futureCondEntail_trans : forall f1 f2 f3, 
    futureCondEntail f1 f2 -> 
    futureCondEntail f2 f3 -> 
    futureCondEntail f1 f3
 .


(* by definition *)
Axiom futureCondEntail_rev : forall t1 t2 ev1 deriv0 deriv, 
  futureCondEntail t1 t2 ->
  fc_der t1 ev1 deriv0 -> 
  fc_der t1 ev1 deriv0 -> 
  futureCondEntail deriv0 deriv.   

Axiom futureCondEntail_exact : forall f, futureCondEntail f f .
Axiom futureCondEntailTrueISTrue: forall f, 
  futureCondEntail fc_default f -> f = fc_default.
Axiom futureCondEntail_indicate: forall f1 f2, futureCondEntail f1 f2 -> 
  exists f3, f1 = fc_conj f3 f2.  

Axiom f_entail_conj_indicate : forall f3 x0 f0, 
  futureCondEntail f3 (fc_conj x0 f0) -> 
  futureCondEntail f3 x0 /\ futureCondEntail f3 f0.



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
  -
  intros. 
  specialize (IHfutureCondEntail1 rho0 H1).
  specialize (IHfutureCondEntail2 rho0 IHfutureCondEntail1). 
  exact IHfutureCondEntail2. 
Qed.         








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
  -
  intros. 
  apply futureCondEntail_conj_RHS.
  constructor.
  pose proof  futureCondEntail_trans.
  specialize (H2 f1 f2 f3 H H0).
  exact H2.
  apply futureCondEntail_conj_LHS_2.
  exact H1.    
Qed.

Theorem strong_LHS_futureEnatil : forall f1 f2 f3, 
  futureCondEntail f1 f2 -> 
  futureCondEntail (fc_conj f1 f3) f2.
Proof.
  intros.
  apply futureCondEntail_conj_LHS_1.
  exact H.
Qed.



    
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



Inductive futureSubtraction_linear : futureCond -> rho -> futureCond -> Prop :=  

  | futureSubtraction_linear_conj : forall f1 f2 f3 f4 t, 
    futureSubtraction_linear f1 t f3 ->
    futureSubtraction_linear f2 t f4 -> 
    futureSubtraction_linear (fc_conj f1 f2) t (fc_conj f3 f4)

  | futureSubtraction_linear_base : forall f, 
    futureSubtraction_linear f nil f 

  | futureSubtraction_linear_induc : forall ev f f_der t t_der res, 
    fc_der f ev f_der -> 
    f_der <> (fc_singleton bot) -> 
    t = ev :: t_der  ->  
    futureSubtraction_linear f_der t_der res -> 
    futureSubtraction_linear f t res. 

Inductive futureSubtraction : futureCond -> theta -> futureCond -> Prop :=  
  | futureSubtraction_bot: forall f1 f2, 
    futureSubtraction f1 bot f2

  | futureSubtraction_conj : forall f1 f2 f3 f4 t, 
    futureSubtraction f1 t f3 ->
    futureSubtraction f2 t f4 -> 
    futureSubtraction (fc_conj f1 f2) t (fc_conj f3 f4)

  | futureSubtraction_base : forall t, 
    futureSubtraction (fc_singleton t) emp (fc_singleton t)

  | futureSubtraction_induc : forall ev f f_der t t_der res, 
    fc_der f ev f_der -> 
    f_der <> (fc_singleton bot) -> 
    theta_der t ev t_der ->  
    futureSubtraction f_der t_der res -> 
    futureSubtraction f t res
 
  | futureSubtraction_strengthing_res: forall f t f1 f2, 
    futureSubtraction f t f1 -> 
    futureCondEntail f2 f1 -> 
    futureSubtraction f t f2
  
  | futureSubtraction_weakening_f:forall f1 t f2 f3, 
    futureSubtraction f1 t f2 -> 
    futureCondEntail f1 f3 -> 
    futureSubtraction f3 t f2
    
  | futureSubtraction_strengthing_t: forall f1 t t' f2, 
    futureSubtraction f1 t f2 -> 
    inclusion t' t -> 
    futureSubtraction f1 t' f2
  . 

Fixpoint concate_trace_fc (t:theta) (f:futureCond)  : futureCond :=
  match f with 
  | fc_singleton t1 => fc_singleton (seq t t1)
  | fc_conj f1 f2 => fc_conj (concate_trace_fc t f1) (concate_trace_fc t f2)
  end. 

Axiom concate_trace_fc_bot: forall f, concate_trace_fc bot f = fc_singleton bot. 
Axiom concate_trace_fc_emp: forall f, concate_trace_fc emp f = f. 
Axiom concate_trace_fc_ev: forall t res rho0 ev0 t_der, 
  fc_model rho0 (concate_trace_fc t res) -> theta_der t ev0 t_der -> 
  exists rho0', fc_model rho0' (concate_trace_fc t_der res) /\ rho0 = ev0 :: rho0'. 

Axiom concate_trace_fc_model: forall f2 f1 rho0 t, 
  futureCondEntail f2 f1 -> 
  fc_model rho0 (concate_trace_fc t f2) -> fc_model rho0 (concate_trace_fc t f1). 

Axiom concate_trace_inclusion_sound: forall f1 rho0 t t', 
  inclusion t' t -> 
  fc_model rho0 (concate_trace_fc t' f1) -> fc_model rho0 (concate_trace_fc t f1). 


Theorem futureSubtraction_sound: forall f f' t rho, 
  futureSubtraction f t f' -> 
  fc_model rho (concate_trace_fc t f') -> 
  fc_model rho f.
Proof.
  intros.
  gen rho0.
  induction H.
  - 
  intros.
  rewrite  concate_trace_fc_bot in H0. 
  invert H0.
  intros.  subst.  
  invert H2.
  - 
  intros. 
  unfold concate_trace_fc in H1. 
  fold concate_trace_fc in H1.
  invert H1.
  intros. subst. 
  specialize (IHfutureSubtraction1 rho0 H5).
  specialize (IHfutureSubtraction2 rho0 H6).
  constructor.
  exact IHfutureSubtraction1. exact IHfutureSubtraction2.
  -
  intros.   
  rewrite  concate_trace_fc_emp in H0.
  exact H0.
  - 
  intros.
  pose proof concate_trace_fc_ev. 
  specialize (H4 t res rho0 ev0 t_der H3 H1). 
  destr H4. 
  subst. 
  specialize (IHfutureSubtraction rho0' H4). 
  pose proof fc_model_rev.
  specialize (H5 f ev0 f_der rho0' H IHfutureSubtraction). 
  exact H5.  
  -
  intros.
  pose proof  concate_trace_fc_model.
  specialize (H2 f2 f1 rho0 t H0 H1). 
  specialize (IHfutureSubtraction rho0 H2). 
  exact IHfutureSubtraction.
  -
  intros.
  specialize (IHfutureSubtraction rho0 H1). 
  pose proof futureCond_sound.
  specialize (H2 f1 f3 rho0 H0 IHfutureSubtraction). 
  exact H2.
  -
  intros.
  pose proof concate_trace_inclusion_sound. 
  specialize ( H2 f2 rho0 t t' H0 H1). 
  specialize (IHfutureSubtraction rho0 H2). 
  exact IHfutureSubtraction.
Qed. 

     

Axiom subtractFromTrueISTrue: forall ev f, 
  futureSubtraction fc_default
(theta_singleton ev) f -> f = fc_default.

Axiom subtract_linear_FromTrueISTrue: forall ev f, 
  futureSubtraction_linear fc_default
(ev::nil) f -> f = fc_default.

  
Axiom all_future_condition_has_futureSubtraction_linear: forall f rho, 
  exists f', futureSubtraction_linear f rho f'. 




Lemma futureCondEntail_fc_model_indicate : forall f2 f1 t rho0, 
  futureCondEntail f2 f1 -> 
  fc_model rho0 (concate_trace_fc t f2) ->
  fc_model rho0 (concate_trace_fc t f1). 
Proof. 
  intros.
  gen rho0 t. 
  induction H.   
  -
  intros. 
  unfold concate_trace_fc in H0. 
  fold concate_trace_fc in H0.  
  invert H0.
  intros. subst. 
  unfold concate_trace_fc. fold concate_trace_fc. 
  constructor. 
  invert H3. 
  intros. subst. 
  constructor.
  exact H4.  pose proof inclusion_sound. 
  specialize (H0 t1 t2 rho2 H H5). exact H0.
  -
  intros. 
  unfold concate_trace_fc in H0. 
  fold concate_trace_fc in H0. 
  invert H0.
  intros. subst. 
  specialize (IHfutureCondEntail rho0 t H4). 
  exact IHfutureCondEntail.
  -
  intros. 
  unfold concate_trace_fc in H0. 
  fold concate_trace_fc in H0. 
  invert H0.
  intros. subst. 
  specialize (IHfutureCondEntail rho0 t H5). 
  exact IHfutureCondEntail.
  -
  intros. 
  specialize (IHfutureCondEntail1 rho0 t H1). 
  specialize (IHfutureCondEntail2 rho0 t H1).
  unfold concate_trace_fc. fold concate_trace_fc.
  constructor.
  exact IHfutureCondEntail1.
  exact IHfutureCondEntail2.
  -
  intros. 
  specialize (IHfutureCondEntail1 rho0 t H1). 
  specialize (IHfutureCondEntail2 rho0 t IHfutureCondEntail1). 
  unfold concate_trace_fc. fold concate_trace_fc.
  exact IHfutureCondEntail2.
Qed.


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
    futureSubtraction_linear f (ev::nil) f' -> 
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

  | eval_malloc : forall h r f loc v f',
    ~ Fmap.indom h loc ->
    futureSubtraction_linear f ((ev "malloc" (vloc loc))::nil) f' -> 
    bigstep h r f (pref (pval v)) (Fmap.update h loc v) (r++((ev "malloc" (vloc loc))::nil)) (fc_conj f' (fc_finally (ev "free" (vloc loc)))) (vloc loc)
. 



Inductive forward : hprop -> theta -> futureCond -> expr -> (val -> hprop) -> theta -> futureCond -> Prop := 


  | fw_consequence: forall P1 P2 P3 P4 t' f' t f e, 
    forward P3 emp fc_default e P4 t' f' -> 
    P1 ==> P3 -> 
    P4 ===> P2 -> 
    inclusion t' t -> 
    futureCondEntail f f' -> 
    forward P1 emp fc_default e P2 t f

  | fw_let : forall x e1 e2 P Q Q1 t2 t3 f2 f3, 
    forward P emp fc_default e1 Q t2 f2  -> 
    (forall v, forward (Q v) t2 f2 (subst x v e2) Q1 t3 f3 ) -> 
    forward P emp fc_default (plet x e1 e2) Q1 t3 f3
  
  | fw_val: forall v P ,
    forward P emp fc_default (pval v) (fun res => P \* \[res = v]) emp fc_default

  | fw_event: forall P (ev:event) ,
    forward P emp fc_default (pevent ev) (fun res => P \* \[res = vunit]) (theta_singleton ev) fc_default

  | fw_cond : forall (b:bool) e1 e2 t f P Q, 
    forward P emp fc_default (if b then e1 else e2) Q t f -> 
    forward P emp fc_default (pif (pval (vbool b)) e1 e2) Q t f

  | fw_deref : forall loc v, 
    forward (loc ~~> v) emp fc_default (pderef (pval(vloc loc))) (fun res => (loc ~~> v) \* \[res = v]) emp fc_default

  | fw_assign : forall loc v v', 
    forward (loc ~~> v') emp fc_default (passign (pval(vloc loc)) (pval v)) (fun res => (loc ~~> v) \* \[res = vunit])  emp fc_default

  | fw_assume : forall P f1, 
    forward P emp fc_default (passume f1) (fun res => P \* \[res = vunit]) emp f1

  | fw_app : forall fromal_arg e actual_arg P Q t f, 
    forward P emp fc_default (subst fromal_arg actual_arg e) Q t f  -> 
    forward P emp fc_default (papp (pval (vfun fromal_arg e)) (pval actual_arg)) Q t f

  | fw_structural: forall P Q t f f_ctx t_ctx f_ctx' e, 
    forward P emp fc_default e Q t f -> 
    futureSubtraction f_ctx t f_ctx' -> 
    forward P t_ctx f_ctx e Q (seq t_ctx t) (fc_conj f_ctx' f)

  | fw_malloc : forall P v h, 
    forward P emp fc_default (pref (pval (v))) (fun res => P \* h ~~> v \* \[res = (vloc h)]) (theta_singleton (ev "malloc" (vloc h))) (fc_singleton(seq (trace_default) (theta_singleton (ev "free" (vloc h)))))

.




Lemma strenthen_futureCond_big_step : forall h1 r1 f1 e h2 r2 f2 v f3, 
  bigstep h1 r1 f1 e h2 r2 f2 v -> 
  futureCondEntail f3 f1 -> 
  exists f4,  
  bigstep h1 r1 f3 e h2 r2 (fc_conj f4 f2) v. 
Proof.
  intros. 
  gen f3.
  induction H.
  -
  intros.
  specialize (IHbigstep1 f0 H1). 
  destr IHbigstep1.
  specialize (IHbigstep2 (fc_conj f4 f2)). 
  pose proof futureCondEntail_conj_LHS_2.
  specialize (H3 f4 f2 f2 (futureCondEntail_exact f2) ). 
  specialize (IHbigstep2 H3). 
  destr IHbigstep2.
  exists f5.
  pose proof eval_plet. 
  specialize (H5 h1 h2 h3 x e1 e2 v r rho1 rho2 rho3 f0 (fc_conj f4 f2) (fc_conj f5 f3) H2 H4). 
  exact H5.
  -
  intros.
  pose proof eval_const.
  specialize (H h r f3 v). 
  pose futureCondEntail_indicate.
  specialize (e f3 f H0 ). 
  destr e.
  subst.
  exists f0.     
  constructor.
  -
  intros.
  specialize (IHbigstep f3 H0). 
  destr IHbigstep. 
  pose futureCondEntail_indicate.
  specialize (e f3 f H0 ). 
  destr e.
  subst.
  exists f4. 
  constructor.
  exact H1.   
  -
  intros.
  specialize (IHbigstep f3 H0). 
  destr IHbigstep. 
  pose futureCondEntail_indicate.
  specialize (e f3 f H0 ). 
  destr e.
  subst.
  exists f4. 
  constructor.
  exact H1.   
  -
  intros.
  pose futureCondEntail_indicate.
  specialize (e f3 f H0 ). 
  destr e. subst.
  exists f0. 
  rewrite (fc_assio f0 f f_assume). 
  constructor.   
  -
  intros. 
  pose proof futureCondEntail_indicate. 
  specialize (H1 f3 f H0). 
  destr H1. subst.

  pose all_future_condition_has_futureSubtraction_linear.
  specialize (e f0 (ev0 :: nil)).
  destr e.
  exists f'0.
  constructor.
  constructor.
  exact H1.
  exact H.  

  -
  intros.
  pose futureCondEntail_indicate.
  specialize (e f3 f H0 ). 
  destr e. subst.
  exists f0. constructor. exact H.
  -
  intros.
  pose futureCondEntail_indicate.
  specialize (e f3 f H0 ). 
  destr e. subst.
  exists f0. constructor. exact H.
  -
  intros. 
  specialize (IHbigstep f3 H0).  
  destr IHbigstep.
  exists f4.
  constructor.
  exact H1.
  -
  intros.
  pose futureCondEntail_indicate.
  specialize (e f3 f H1). 
  destr e. subst.
  pose proof all_future_condition_has_futureSubtraction_linear.
  specialize (H2 f0 (ev "malloc" (vloc loc0) :: nil)).
  destr H2.  
  exists (f'0).  
  rewrite <- futureCond_distr. 
  constructor. exact H. 
  rewrite fc_comm.  
  constructor. 
  exact H0.
  exact H3.  

Qed. 



Lemma forward_only_appending_trace: forall P t1 f1 e Q t2 f3, 
  forward P t1 f1 e Q t2 f3 -> 
  exists t3, 
  t2 = seq t1 t3.
Proof. 
  intros.
  induction H.
  -
  exists t. 
  rewrite normal_emp.
  reflexivity.
  -
  destr IHforward.
  exists t3.
  rewrite normal_emp.
  reflexivity.
  -
  exists emp. rewrite normal_emp. reflexivity.
  -
  exists (theta_singleton ev0).
  rewrite normal_emp. reflexivity.
  -
  destr IHforward. exists t.
  rewrite normal_emp.
  reflexivity.
  -
  exists emp. rewrite normal_emp. reflexivity.
  -
  exists emp. rewrite normal_emp. reflexivity.
  -
  exists emp. rewrite normal_emp. reflexivity.
  -
  destr IHforward. exists t.
  rewrite normal_emp. reflexivity.
  -
  exists t. reflexivity.
  - 
  exists (theta_singleton (ev "malloc" (vloc h))).
  rewrite normal_emp.
  reflexivity.   
Qed. 


Lemma future_frame_big_step_aux_aux : forall h1 rho1 f1 e h2 rho2 f2 v rho f, 
  bigstep h1 rho1 f1 e h2 rho2 f2 v -> 
  exists rho3 f3, 
  bigstep h1 rho f e h2 (rho++rho3) f3 v /\ 
  rho2 = rho1 ++ rho3 . 
Proof. 
  intros. 
  gen rho0 f.
  induction H.
  -
  intros. 
  specialize (IHbigstep1 rho0 f).
  destr IHbigstep1.  
  specialize (IHbigstep2 (rho0 ++ rho4) f0).
  destr  IHbigstep2. 
  exists (rho4++rho5) f4.
  subst.
  split. 
  pose proof eval_plet. 
  specialize (H3 h1 h2 h3 x e1 e2 v r rho0 (rho0 ++ rho4) ((rho0 ++ rho4) ++ rho5) f f0 f4 H1 H2).
  (* Search ((_ ++ _) ++ _ ). *)
  rewrite List.app_assoc.
  exact H3.
  rewrite List.app_assoc. reflexivity.
  -   
  intros.
  exists (nil:rho) f0.
  split.
  rewrite List.app_nil_r. 
  constructor. 
  rewrite List.app_nil_r. reflexivity.
  -  
  intros. 
  specialize (IHbigstep rho0 f0). 
  destr IHbigstep. subst. 
  exists rho3 f3.
  split. 
  constructor. exact H0. 
  reflexivity. 
  -  
  intros. 
  specialize (IHbigstep rho0 f0). 
  destr IHbigstep. subst. 
  exists rho3 f3.
  split. 
  constructor. exact H0. 
  reflexivity. 
  -
  intros. 
  exists (nil:rho) (fc_conj f0 f_assume). 
  split. 
  rewrite List.app_nil_r.
  constructor.
  rewrite List.app_nil_r. reflexivity.
  -
  intros.
  pose proof all_future_condition_has_futureSubtraction_linear. 
  specialize (H0 f0 (ev0::nil)).
  destr H0.  
  exists (ev0::nil) f'0.
  split.
  constructor. 
  exact H1.   
  reflexivity. 
  -
  intros. 
  exists (nil:rho) f0.
  split. rewrite List.app_nil_r. 
  constructor. exact H.  rewrite List.app_nil_r. reflexivity.
  - 
  intros. 
  exists (nil:rho) f0.
  split. rewrite List.app_nil_r. 
  constructor. exact H.  rewrite List.app_nil_r. reflexivity.
  -
  intros.
  specialize (IHbigstep rho0 f). 
  destr IHbigstep. subst. 
  exists (rho3) (f3).
  split. constructor. exact H0.  
  reflexivity.
  - 
  intros. 
  exists (ev "malloc" (vloc loc0) :: nil).
  pose proof all_future_condition_has_futureSubtraction_linear.
  specialize (H1 f0 (ev "malloc" (vloc loc0) :: nil)).
  destr H1. 
  exists (fc_conj f'0 (fc_finally (ev "free" (vloc loc0)))). 
  split.    
  constructor. exact H. exact H2. reflexivity.
Qed. 

Axiom identity : forall [A: Type] (x:A), x = x.
Axiom identity1 : forall  (x:Prop) (y:Prop), (x = y) -> y -> x.


Lemma all_future_Cond_can_be_split_into_two_conjunctive_cases: forall f, 
  exists f1 f2, 
  f = (fc_conj f1 f2).
Proof.
  intros. 
  induction f.
  - exists (fc_singleton t) fc_default. 
  rewrite fc_comm. 
  rewrite f_conj_kleene_any_is_f. 
  reflexivity.
  -
  destr IHf1.
  destr IHf2.
  subst.
  exists (fc_conj f0 f3) (fc_conj f4 f5).
  reflexivity.
Qed.   

Axiom distribute_futureSubtraction: forall f1 f2 t f3, 
  futureSubtraction_linear (fc_conj f1 f2) t
f3 -> 
exists f4 f5, 
    futureSubtraction_linear f1 t f4 /\ 
    futureSubtraction_linear f2 t f5 /\ 
    f3 = fc_conj f4 f5. 


  
Lemma futureCondEntail_linear_distrbute: forall f f' f1 f2 rho, 
  futureSubtraction_linear f rho f' ->
  f = (fc_conj f1 f2) ->
  exists f1' f2',
  futureSubtraction_linear f1 rho f1' /\
  futureSubtraction_linear f2 rho f2' /\
  f' = (fc_conj f1' f2').
Proof.  
  intros.
  gen f1 f2.
  induction H.
  - 
  intros.  
  invert H1.
  intros. subst. 
  pose proof identity. 
  pose all_future_Cond_can_be_split_into_two_conjunctive_cases. 
  specialize (e f0). 
  destr e.
  pose all_future_Cond_can_be_split_into_two_conjunctive_cases. 
  specialize (e f5). 
  destr e.
  subst. 
  specialize (IHfutureSubtraction_linear1 f1 f2 (H1 futureCond (fc_conj f1 f2))).
  destr IHfutureSubtraction_linear1.
  specialize (IHfutureSubtraction_linear2 f6 f7 (H1 futureCond (fc_conj f6 f7))). 
  destr IHfutureSubtraction_linear2.
  exists f3 f4.
  split. exact H. split. exact H0. reflexivity. 
  -

  intros. subst.
  exists f1 f2.
  split. constructor. split. constructor. reflexivity.
  -
  intros. subst.
  pose proof all_future_Cond_can_be_split_into_two_conjunctive_cases.
  specialize (H1 f_der). 
  destr H1.
  specialize (IHfutureSubtraction_linear f0 f3 H1). 
  subst.  
  pose fc_conj_not_bot. 
  specialize (a  f0 f3 H0). 
  destr a.
  destr IHfutureSubtraction_linear.  
  pose proof futureSubtraction_linear_induc. 
  invert H.
  intros. subst.
    pose identity. 
  exists f1' f2'.
  split.
  specialize (H6 ev0 f1 f0 (ev0 :: t_der) t_der f1' H12 H1 (e rho (ev0 :: t_der)) H4). 
  exact H6.
  split.
  specialize (H6 ev0 f2 f3 (ev0 :: t_der) t_der f2' H14 H3 (e rho (ev0 :: t_der)) H5). 
  exact H6. 
  reflexivity.
Qed.   
    

Lemma distrbuteBigStepLHS: forall h1 rho1 f f1 f2 e h2 rho2 f0 v, 
  bigstep h1 rho1 f e h2 rho2 f0 v -> 
  f = (fc_conj f1 f2) ->
  exists f3 f4, 
  bigstep h1 rho1 f1 e h2 rho2 f3 v /\  
  bigstep h1 rho1 f2 e h2 rho2 f4 v  /\ f0 = fc_conj f3 f4.
Proof. 
  intros.
  gen f1 f2. 
  induction H.
  - 
  intros.
  specialize (IHbigstep1 f0 f4 H1).  
  destr IHbigstep1.
  specialize (IHbigstep2 f5 f6 H5). 
  destr IHbigstep2. 
  subst.
  exists f7 f8. 
  pose proof eval_plet.
  specialize (H1 h1 h2 h3 x e1 e2 v r rho1 rho2 rho3 f0 f5 f7 H2 H4).   
  pose proof eval_plet.
  specialize (H5 h1 h2 h3 x e1 e2 v r rho1 rho2 rho3 f4 f6 f8 H3 H6). 
  split. exact H1. split. exact H5. reflexivity.
  -
  intros.
  subst.
  exists f1 f2.
  split. constructor. split. constructor. reflexivity.
  - 
  intros. subst.
  pose proof (identity ). 
  specialize (IHbigstep f1 f2 (H0 futureCond (fc_conj  f1 f2))). 
  destr IHbigstep.
  subst. 
  exists f3 f4.
  split. constructor. exact H1. split. constructor. exact H2. reflexivity.
  - 
  intros. subst. 
  pose proof (identity ). 
  specialize (IHbigstep f1 f2 (H0 futureCond (fc_conj  f1 f2))). 
  destr IHbigstep.
  subst.  
  exists f3 f4.
  split. constructor. exact H1. split. constructor. exact H2. reflexivity.
  -
  intros. subst.
  exists (fc_conj f1 f_assume) (fc_conj f2 f_assume). 
  split. constructor. split. constructor. 
  rewrite futureCond_distr2. reflexivity.
  - 
  intros. subst. 
  pose proof futureCondEntail_linear_distrbute. 
  pose proof (identity ). 

  specialize (H0 (fc_conj f1 f2) f' f1 f2 (ev0 :: nil)%mylist H (H1 futureCond (fc_conj f1 f2))). 
  destr H0. subst.
  exists f1' f2'.
  split. constructor. exact H2. split. constructor. exact H0. reflexivity.   
  -
  intros. subst. 
  exists f1 f2. 
  split. constructor. exact H.  split. constructor. exact H.  reflexivity.
  -
  intros. subst. 
  exists f1 f2.  
  split. constructor. exact H.  split. constructor. exact H.  reflexivity.
  -
  intros. subst.
  pose proof (identity ). 
  specialize (IHbigstep f0 f3 (H0 futureCond (fc_conj f0 f3))). 
  destr IHbigstep. subst. 
  exists f1 f4.
  split. constructor. exact H1. split. constructor. exact H2. reflexivity.
  - 
  intros. subst. 
  pose proof distribute_futureSubtraction. 
  specialize (H1 f1 f2 (ev "malloc" (vloc loc0) :: nil) f' H0). destr H1. 
  subst.    
  exists (fc_conj f4 (fc_finally (ev "free" (vloc loc0)))) (fc_conj f5 (fc_finally (ev "free" (vloc loc0)))).  
  split. constructor. exact H.  exact H2. split. constructor. exact H.
  exact H1. rewrite futureCond_distr2.  reflexivity.

Qed.  


Axiom big_step_nil_context: forall h1 rho1 f_ctx e h2 h3 rho2 f3 v rho3 f0  f_ctx', 
  bigstep h1 rho1 f_ctx e h2 rho2 f3 v -> 
  rho2 = (rho1 ++ rho3) -> 
  bigstep h1 nil fc_default e h3 rho3 f0 v -> 
  futureSubtraction_linear f_ctx rho3 f_ctx' ->
  f3 = fc_conj f0 f_ctx'.



Axiom futureCondEntail_fc_der_indicate: forall f f3 ev0 f_der, 
  futureCondEntail f f3 ->  fc_der f ev0 f_der -> 
  f_der <> fc_singleton bot -> 
  exists deriv, fc_der f3 ev0 deriv /\ deriv <> fc_singleton bot. 

Axiom fc_singleton_is_not_conj : forall t f1 f2, 
  fc_singleton t <> fc_conj f1 f2. 

Axiom futureCondEntail_conj_left_indicates: forall f f0 f1 f2, 
  futureCondEntail f f0 ->  f = (fc_conj f1 f2) -> 
  futureCondEntail f1 f0 \/ futureCondEntail f2 f0.


Lemma weakening_futureSubtraction_linear : forall  f1 rho3 f2 f3, 
  futureSubtraction_linear f1 rho3 f2 -> 
  futureCondEntail f1 f3 -> 
  exists f4, 
  futureSubtraction_linear f3 rho3 f4 /\ futureCondEntail f2 f4 . 
Proof. 
  intros. 
  gen f3.
  induction H. 
  -
  intros. 
  pose identity.
  pose proof futureCondEntail_conj_left_indicates. 
  specialize ( H2 (fc_conj f1 f2) f0 f1 f2 H1 (e futureCond (fc_conj f1 f2))). 
  invert H2.
  intros. 
  specialize (IHfutureSubtraction_linear1 f0 H3). 
  destr IHfutureSubtraction_linear1.
  exists f5.
  split. exact H4. 
  apply futureCondEntail_conj_LHS_1. exact H5.
  intros.
  specialize (IHfutureSubtraction_linear2 f0 H3). 
  destr IHfutureSubtraction_linear2.
  exists f5.
  split. exact H4. 
  apply futureCondEntail_conj_LHS_2. exact H5.
  -
  intros.
  exists f3.
  split. constructor. exact H0.
  -
  intros.
  pose proof futureCondEntail_fc_der_indicate.
  specialize (H4 f f3 ev0 f_der H3 H H0).
  destr H4.
  specialize (IHfutureSubtraction_linear deriv). 
  pose proof futureCondEntail_rev.
  specialize (H5 f f3 ev0 f_der deriv H3 H H).    
  specialize (IHfutureSubtraction_linear H5). 
  destr IHfutureSubtraction_linear.
  pose futureSubtraction_linear_induc.
  pose identity. 
  specialize (f0 ev0 f3 deriv (ev0::t_der) t_der f4 H4 H6 (e rho (ev0::t_der)) H8).  
  exists f4.
  split.
  subst.
  exact f0. exact H9.
Qed. 

Lemma futureSubtraction_strengthing_linear_res : 
  forall f_ctx t f_ctx' rho3,
  futureSubtraction f_ctx t f_ctx' -> 
  trace_model rho3 t -> 
  exists f_ctx'0,
  futureSubtraction_linear f_ctx rho3 f_ctx'0  /\ futureCondEntail f_ctx' f_ctx'0.
Proof. 
  intros.
  gen rho3. 
  induction H.
  -  
  intros. invert H0.
  -
  intros. 
  specialize (IHfutureSubtraction1 rho3 H1).    
  specialize (IHfutureSubtraction2 rho3 H1).     
  destr IHfutureSubtraction1.
  destr IHfutureSubtraction2.
  exists (fc_conj f_ctx'0 f_ctx'1).
  split.
  constructor. exact H3. exact H5. 
  apply futureCondEntail_conj_RHS.
  apply futureCondEntail_conj_LHS_1. exact H4.  
  apply futureCondEntail_conj_LHS_2. exact H6.
  -
  intros. 
  invert H0.
  intros. subst. 
  exists (fc_singleton t).
  split. constructor. constructor. exact (inclusion_exact t).
  -
  intros.
  pose proof (case_spliting_helper_bot t_der). 
  invert H4.
  intros. subst.
  pose proof derivative_model_false.
  specialize (H4 t ev0 H1). 
  false.  
  intros. subst.
  pose proof  derivative_model.
  specialize (H4 t ev0 t_der rho3 H1 H5 H3). 
  destr H4.
  specialize (IHfutureSubtraction rho1 H7). 
  destr IHfutureSubtraction.
  pose proof futureSubtraction_linear_induc.
  specialize (H6 ev0 f f_der rho3 rho1 f_ctx'0 H H0 H4 H8).   
  exists f_ctx'0. 
  split. exact H6. exact H9.
  -
  intros.
  specialize (IHfutureSubtraction rho3 H1).
  destr IHfutureSubtraction.
  exists f_ctx'0. 
  split. exact H3. 
  pose (futureCondEntail_trans ).
  specialize (f0 f2 f1 f_ctx'0 H0 H4).
  exact f0.
  -
  intros.
  specialize (IHfutureSubtraction rho3 H1).
  destr IHfutureSubtraction.
  pose proof weakening_futureSubtraction_linear. 
  specialize (H2 f1 rho3 f_ctx'0 f3 H3 H0 ).
  destr H2.
  exists f4.
  split. exact H2. 
  pose proof (futureCondEntail_trans).
  exact (H5 f2 f_ctx'0 f4 H4 H6). 

  -
  intros.
  pose proof inclusion_sound.
  specialize (H2 t' t rho3 H0 H1). 
  specialize (IHfutureSubtraction rho3 H2).
  destr IHfutureSubtraction. 
  exists f_ctx'0. 
  split. exact H4. 
  exact H5.
Qed. 


Lemma futureSubtraction_trace_model_futureSubtraction_linear:
forall f_ctx t f_ctx' rho3 h1 e h2 rho1 f3 v f0, 
  futureSubtraction f_ctx t f_ctx' -> 
  trace_model rho3 t ->
  bigstep h1 rho1 f_ctx e h2 (rho1 ++ rho3) f3 v -> 
  bigstep h1 nil fc_default e h2 rho3 f0 v -> 
  futureCondEntail (fc_conj f_ctx' f0) f3. 
Proof. 
  intros.
  pose proof big_step_nil_context.
  pose identity. 
  pose proof futureSubtraction_strengthing_linear_res. 
  specialize (H4 f_ctx t f_ctx' rho3 H H0). 
  destr H4. 
  specialize (H3 h1 rho1 f_ctx e h2 h2 (rho1 ++ rho3) f3 v rho3 f0 f_ctx'0 H1 (e0 rho (rho1++rho3)) H2 H4). subst.
  apply futureCondEntail_conj_RHS.
  apply futureCondEntail_conj_LHS_2. exact (futureCondEntail_exact f0) .
  apply futureCondEntail_conj_LHS_1. exact H6. 
Qed. 

Lemma bigstep_framing_trace: forall h3 e h2 rho0 f3 v rho3 rho1 f, 
  bigstep h3 rho1 f e h2 rho0 f3 v -> 
  bigstep h3 (rho3++rho1) f e h2 (rho3 ++ rho0) f3 v. 
Proof. 
  intros. 
  gen rho3. 
  induction H.
  - 
  intros. 
  specialize (IHbigstep1 rho0). 
  specialize (IHbigstep2 rho0). 
  pose proof eval_plet.
  specialize (H1 h1 h2 h3 x e1 e2 v r (rho0 ++ rho1) (rho0 ++ rho2) (rho0 ++ rho3) f1 f2 f3 IHbigstep1 IHbigstep2). 
  exact H1.
  -
  intros.
  constructor.
  - intros. constructor. exact (IHbigstep rho3).
  - intros. constructor. exact (IHbigstep rho3).
  - intros. constructor. 
  - intros. rewrite List.app_assoc. constructor. exact H.
  - intros. constructor. exact H.
  - intros. constructor. exact H.
  - intros. constructor. exact (IHbigstep rho3).
  - intros. 
    rewrite List.app_assoc. 
   constructor. exact H. exact H0. 
Qed.      


Lemma heap_disjoint_consequence_aux: forall [A B : Type] (h1:Fmap.fmap A B) h2 h3, 
  Fmap.disjoint h1 h2 -> 
  Fmap.disjoint h2 h3 -> 
  Fmap.disjoint h1 h3-> 
  Fmap.disjoint h1 (h2 \u h3). 
Proof. 
  intros.
    pose proof  disjoint_union_eq_r. 
  (* info_eauto. *)
  eauto.
Qed. 

Axiom h_subst_pure: forall (t1:loc) t2, t1 = t2.  




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
  pose proof futureCondEntail_trans.
  specialize (H8 f f' f3 H3 H10). 
  exact H8. 


  - (* let *)
  intros.
  invert H4. intros. subst.
  specialize (IHforward h1 H2 v0 h3 rho1).
  specialize (IHforward H3 rho3 f4 H15).
  destr IHforward.
  specialize (H0 v0). 
  pose proof strenthen_futureCond_big_step.
  specialize (H5 h3 rho3 f4 (subst x v0 e2) h2 rho2 f0 v f2 H16 H7). 
  destruct H5 as (x0&H5). 
  specialize(H1 v0 h3 H4 v h2 rho3 H6 rho2 (fc_conj x0 f0) H5).
  destruct H1. destruct H8.
  split.
  exact H1.
  split.
  exact H8. 
  pose proof (f_entail_conj_indicate ).
  specialize (H10 f3 x0 f0 H9). destr H10. exact H12.   


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
  (* Search (nil ++ _).  *)
  rewrite List.app_nil_l. 
  constructor. reflexivity.
  pose subtract_linear_FromTrueISTrue as H. 
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
  (* Search (Fmap.single _ _ ).  *)
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
  specialize (IHforward h1 H1 v).  
  pose proof future_frame_big_step_aux_aux. 
  specialize (H4 h1 rho1 f_ctx e h2 rho2 f3 v nil fc_default H3).  
  destr H4.  
  specialize (IHforward h2 nil tm_emp rho3 f0 H5). 
  destr IHforward.
  split.
  exact H4.
  split.
  subst.   
  constructor.
  exact H2. exact H8.
  subst.
  pose proof futureSubtraction_trace_model_futureSubtraction_linear.
  rewrite List.app_nil_l in H5.
  specialize (H6 f_ctx t f_ctx'  rho3 h1 e h2 rho1 f3 v f0 H0 H8 H3 H5). 
  pose proof futureCondEntail_trans. 
  specialize (H7 (fc_conj f_ctx' f) (fc_conj f_ctx' f0) f3 ).  
  apply H7. 
  apply futureCondEntail_conj_RHS. 
  apply futureCondEntail_conj_LHS_1. exact (futureCondEntail_exact f_ctx'). 
  apply futureCondEntail_conj_LHS_2. exact H9.   
  exact H6.  

  - 
  intros.
  invert H2.
  intros. subst.
  pose proof h_subst_pure.
  specialize (H loc0 h).
  subst.  
  split.
  (* Search (~ Fmap.indom _ _). *)
  unfold Fmap.update.
  (* Search (_ \u _).  *)
  pose proof Fmap.union_comm_of_disjoint. 
  specialize (H loc val (Fmap.single h v) h1). 
  (* Search (~ Fmap.indom _ _). *)
  pose proof Fmap.disjoint_single_of_not_indom.
  specialize (H2 loc val h1 h v H3). 
  specialize (H H2). 
  (* Search ( _ \* _ = _ \* _). *)
  rewrite hstar_comm. 
  apply* hstar_intro.
  (* Search (Fmap.single _ _).  *)
  pose proof hsingle_intro. 
  specialize (H4 h v). 
  (* Search (_ \* _). *)
  pose proof hstar_hpure_l. 
  (* Search (_ \* _).  *)
  rewrite hstar_comm. 
  specialize (H5 (vloc h = vloc h) (h ~~> v) (Fmap.single h v)).
  pose proof identity1.
  specialize (H6 ((\[vloc h = vloc h] \* h ~~> v) (Fmap.single h v)) (vloc h = vloc h /\
(h ~~> v) (Fmap.single h v)) H5).  
  apply H6. 
  split. reflexivity. 
  exact H4.      
  split.
  rewrite <- normal_emp.
  constructor.
  exact H1. 
  constructor. 
  reflexivity.
  pose proof subtract_linear_FromTrueISTrue.
  specialize (H (ev "malloc" (vloc h)) f' H7).
  subst.
  constructor.
  pose proof anything_future_entail_default.
  exact (H (fc_singleton (seq trace_default (theta_singleton (ev "free" (vloc h)))))).
  unfold  fc_finally. unfold trace_finally. 
  exact (futureCondEntail_exact (fc_singleton (seq trace_default (theta_singleton (ev "free" (vloc h)))))).          

Qed. 

Module Examples.

Definition e1 := (pval vunit). 

Example forward_e1: 
  forward hempty emp fc_default e1 (fun res : val => \[] \* \[res = vunit]) emp fc_default. 
Proof.
  pose proof fw_val.
  specialize (H vunit \[] ). 
  exact H.  
Qed. 

Definition e2 := (pval vunit). 

End Examples.