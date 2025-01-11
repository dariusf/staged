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


Definition compare_event (ev1:event) (ev2:event) : bool := 
  let (s1, v1) := ev1 in 
  let (s2, v2) := ev2 in 
  (String.eqb s1 s2).




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

  | tm_any : forall ev, 
    trace_model (ev::nil) (any)

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

  | tm_kleene_emp : forall rho t, 
    trace_model rho emp -> 
    trace_model rho (kleene t)

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
  - apply tm_kleene_emp. constructor.
Qed.   

Lemma trace_model_emp_must_nil : forall rho, 
  trace_model rho emp -> rho = nil.
Proof.
  intros.
  induction H.
  - reflexivity.
Admitted. 



Inductive fst : theta -> fstEvs -> Prop :=
  | fst_bot: fst bot nil 
  | fst_emp: fst emp nil 
  | fst_any: 
    fst (any) ((ev "_" vunit) :: nil)

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
  | derivative_bot : forall ev, theta_der bot ev bot
  | derivative_emp : forall ev, theta_der emp ev bot
  | derivative_any : forall ev, theta_der any ev emp

  | derivative_event_emp : forall ev1 ev2, 
    ev1 = ev1 -> 
    theta_der (theta_singleton ev1) ev2 emp 
  | derivative_event_bot : forall ev1 ev2, 
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


Inductive inclusion : theta -> theta -> Prop := 

  | inc_emp: forall t, 
    nullable t -> 
    inclusion emp t 

  | (* Reoccur *)
    inc_reoccur: forall t1 t2, 
    inclusion t1 t2 -> 
    inclusion t1 t2  


  | inc_exact: forall t, 
    inclusion t t

  | inc_kleene_any: forall t, 
    inclusion t (kleene any) 

  | (* Unfold *)
    inc_unfold: forall t1 t2 ev deriv1 deriv2,
    theta_der t1 ev deriv1 -> 
    theta_der t2 ev deriv2 -> 
    inclusion deriv1 deriv2 -> 
    inclusion t1 t2
. 

Lemma trace_model_derivatives : forall rho rho1 t ev t_der, 
  trace_model rho t -> 
  theta_der t ev t_der -> 
  rho = ev :: rho1 -> 
  trace_model rho1 t_der
.
Admitted. 


Theorem inclusion_sound: forall t1 t2 rho, 
  inclusion t1 t2 -> 
  trace_model rho t1 -> 
  trace_model rho t2.
Proof.
  intros. 
  gen rho0. 
  induction H.
  - intros. 
    pose proof empty_rho_model_nullable_trace.
    specialize (H1 t H).
    pose proof trace_model_emp_must_nil.
    specialize (H2 rho0 H0).
    subst.
    exact H1.
  - intros. exact (IHinclusion rho0 H0).
  - intros. exact H0.
  - intros.  
    
Admitted. 


Lemma trace_model_prefix : forall rho t rho1 t1, 
  trace_model rho t -> 
  trace_model rho1 t1 -> 
  trace_model (rho++rho1) (seq t t1).
Proof.
  intros.
  invert H.
  intros. 
  - econstructor.
    eauto.
    constructor.
    exact H0.
  - econstructor.
    eauto.
    constructor.
    exact H1.
    exact H0.
  - econstructor.
    eauto.
    constructor.
    exact H0.
  - econstructor.
    eauto.
    subst.
    econstructor. eauto.
    exact H2.
    exact H0.
  - econstructor.
    eauto.
    econstructor.
    exact H1.
    exact H0.
  - econstructor.
    subst.
    eauto. subst. 
    apply tm_disj_right. exact H1.
    exact H0.
  - econstructor.
    eauto.
    apply tm_kleene_emp.
    exact H1.
    exact H0.
  - econstructor.
    eauto.
    apply tm_kleene_rec.
    exact H1.
    exact H0.
Qed.

Inductive futureCondEntail1 : futureCond -> futureCond -> Prop := 
  | futureCondEntail1_empty : forall t1 t2, 
    inclusion t1 t2 -> 
    futureCondEntail1 (fc_singleton t1) (fc_singleton t2)

  | futureCondEntail1_conj_LHS : forall f1 f2 f, 
    futureCondEntail1 f1 f -> 
    futureCondEntail1 f2 f -> 
    futureCondEntail1 (fc_conj f1 f2) f 

  | futureCondEntail1_conj_RHS_1 : forall f1 f2 f, 
    futureCondEntail1 f f1 -> 
    futureCondEntail1 f (fc_conj f1 f2) 


  | futureCondEntail1_conj_RHS_2 : forall f1 f2 f, 
    futureCondEntail1 f f2 -> 
    futureCondEntail1 f (fc_conj f1 f2) 
 .




Inductive futureCondEntail : futureCond -> futureCond -> futureCond -> Prop := 
  | futureCondEntail_empty : forall t1 t2, 
    inclusion t1 t2 -> 
    futureCondEntail (fc_singleton t1) (fc_singleton t2)  (fc_singleton (kleene any))

  | futureCondEntail_conj_LHS : forall f1 f2 f fR1 fR2, 
    futureCondEntail f1 f fR1 -> 
    futureCondEntail f2 f fR2 -> 
    futureCondEntail (fc_conj f1 f2) f (fc_conj fR1 fR2) 

  | futureCondEntail_conj_frame_left : forall f f1 f2 fR1, 
    futureCondEntail f1 f fR1 -> 
    futureCondEntail (fc_conj f1 f2) f  (fc_conj fR1 f2)
  
  | futureCondEntail_conj_frame_right : forall f f1 f2 fR1, 
    futureCondEntail f2 f fR1 -> 
    futureCondEntail (fc_conj f1 f2) f  (fc_conj fR1 f1)


  | futureCondEntail_conj_RHS : forall f f1 f2 fR1 fR2, 
    futureCondEntail f f1 fR1 -> 
    futureCondEntail fR1 f2 fR2 -> 
    futureCondEntail f (fc_conj f1 f2) (fR2) 
 .



Theorem futureCond1_sound : forall f1 f2 rho, 
  futureCondEntail1 f1 f2 -> 
  fc_model rho f1 -> 
  fc_model rho f2.
Proof. 
  intros.
  invert H0.
  induction H. 
  - 
  intros.   
  invert H3. 
  intros.
  subst.   
  constructor.
  pose proof inclusion_sound.
  specialize (H0 t1 t2 rho0 H). 
  eapply H0. 
  exact H1.
  - intros. false.
  - intros. subst. 
  

Admitted. 


Theorem futureCond1_trans : forall f1 f2 f3, 
  futureCondEntail1 f1 f2 -> 
  futureCondEntail1 f2 f3 -> 
  futureCondEntail1 f1 f3.
Proof using. introv M1. induction M1; introv M2. 
  -  
  pose proof inclusion_sound.
  specialize (H0 t1 t2).
  pose proof futureCond1_sound.

Admitted. 


Theorem strong_LHS_futureEnatil : forall f1 f2 f3, 
  futureCondEntail1 f1 f2 -> 
  futureCondEntail1 (fc_conj f3 f1) f2.
Proof.
Admitted. 

Axiom conj_kleene_any : 
   (fc_singleton(kleene any)) = 
   fc_conj (fc_singleton(kleene any)) (fc_singleton(kleene any)). 
  
Axiom f_conj_kleene_any_is_f : forall f, 
   f = fc_conj (fc_singleton(kleene any)) f . 

Axiom f_conj_kleene_any_is_f_reverse : forall f, 
   fc_conj (fc_singleton(kleene any)) f = f. 

  

Lemma futureCondEntail1_exact : forall f,  
  futureCondEntail1 f f .
Proof.
Admitted. 

Lemma anything_future_entail_default : forall f,  
  futureCondEntail1 f  (fc_singleton(kleene any)).
Proof.
Admitted. 


Lemma futureCondEntail_exact : forall f,  
  futureCondEntail f f (fc_singleton(kleene any)).
Proof.
  intros.
  induction f. 
  - constructor.
    apply inc_exact.
  - pose proof  futureCondEntail_conj_RHS.
    specialize (H (fc_conj f1 f2) f1 f2 f2 (fc_singleton (kleene any))).  
    apply H.
    pose proof futureCondEntail_conj_frame_left. 
    specialize (H0 f1 f1 f2 (fc_singleton (kleene any)) IHf1).
    rewrite  f_conj_kleene_any_is_f.
    exact H0.
    exact IHf2.  
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
  - intros. subst. constructor. 
    constructor. exact H0. exact H1.
  - intros. subst. constructor. constructor. exact H0.
  - intros. subst. constructor. apply tm_disj_right. exact H0.
  - intros. subst. constructor. constructor. exact H0.
  - intros. subst. constructor. apply tm_kleene_rec. exact H0. 
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

Lemma every_rho_models_kleene_any : forall rho , 
  trace_model rho (kleene any).
Proof. 
  intros. 
  induction rho0.
  - constructor. constructor. 
  - apply tm_kleene_rec. 
    pose proof tm_seq.
    Search ((_ :: _) ++ _). 
    pose proof List.app_comm_cons.
    specialize (H0 event nil rho0 a). 
    pose proof tm_any.
    specialize (H1 a). 

    specialize (H (a::nil) rho0 any (kleene any) H1 IHrho0). 
    Search (nil ++ _).
    rewrite List.app_nil_l in H0.
    auto.
Qed. 


Theorem futureCond_sound : forall f1 f2 fR rho, 
  futureCondEntail f1 f2 fR -> 
  fc_model rho f1 -> 
  fc_model rho (fc_conj f2 fR).
Proof. 
  intros.
  induction H.
  - intros. subst. 
    pose proof inclusion_sound. 
    specialize (H1 t1 t2 rho0). 
    pose proof fc_singleton_to_trace. 
    specialize (H2 rho0 t1 H0).  
    specialize (H1 H H2).
    constructor.   
    pose proof trace_to_fc_singleton. 
    specialize (H3 rho0 t2 H1).
    exact H3.
    pose proof trace_to_fc_singleton. 
    specialize (H3 rho0 (kleene any)). 
    apply H3. 
    pose proof every_rho_models_kleene_any.
    specialize (H4 rho0 ).
    exact H4.  
  - pose proof fc_conj_to_trace.
    specialize (H2 rho0 f1 f2 H0). 
    destr H2.
    specialize (IHfutureCondEntail1 H3).
    specialize (IHfutureCondEntail2 H4).
    pose proof fc_conj_to_trace.
    specialize (H2 rho0 f fR1 IHfutureCondEntail1). 
    pose proof fc_conj_to_trace.
    specialize (H5 rho0 f fR2 IHfutureCondEntail2).  
    destr H2.     destr H5.
    constructor. exact H6.
    constructor. exact H7. exact H8.     

  - pose proof fc_conj_to_trace.
    specialize (H1 rho0 f1 f2 H0).     
    destr H1. 
    constructor.
    specialize (IHfutureCondEntail H2).
    pose proof fc_conj_to_trace.
    specialize (H1 rho0 f fR1 IHfutureCondEntail).
    destr H1. 
    exact H4.
    pose proof every_rho_models_kleene_any.
    specialize (H1 rho0 ).
    constructor.   
    specialize (IHfutureCondEntail H2). 
    pose proof fc_conj_to_trace.
    specialize (H4 rho0 f fR1 IHfutureCondEntail ). 
    destr H4.  
    exact H6.
    exact H3.  
  - pose proof fc_conj_to_trace.
    specialize (H1 rho0 f1 f2 H0). 
    destr H1.
    specialize (IHfutureCondEntail H3). 
    pose proof fc_conj_to_trace.
    specialize (H1 rho0 f fR1 IHfutureCondEntail).
    destr H1.
    constructor.
    exact H4.
    constructor.
    exact H5.
    exact H2.
  - 
    specialize (IHfutureCondEntail1 H0).  
    pose proof fc_conj_to_trace.
    specialize (H2 rho0 f1 fR1 IHfutureCondEntail1). 
    destr H2.
    specialize (IHfutureCondEntail2 H4).
    pose proof fc_conj_to_trace.
    specialize (H2 rho0 f1 fR1 IHfutureCondEntail1).
    destr H2.
    pose proof fc_conj_to_trace.
    specialize (H2 rho0 f2 fR2 IHfutureCondEntail2).
    destr H2.
    constructor.
    constructor.
    exact H3.
    exact H7.
    exact H8.
    
Qed. 




Inductive futureSubtraction : futureCond -> theta -> futureCond -> Prop :=  
  | futureSubtraction_conj : forall f1 f2 f3 f4 t, 
    futureSubtraction f1 t f3 ->
    futureSubtraction f2 t f4 -> 
    futureSubtraction (fc_conj f1 f2) t (fc_conj f3 f4)

  | futureSubtraction_base : forall t, 
    futureSubtraction (fc_singleton t) emp (fc_singleton t)
  .   

Inductive futureSubtraction_linear : futureCond -> rho -> futureCond -> Prop :=  

  | futureSubtraction_linear_base : forall t, 
    futureSubtraction_linear (fc_singleton t) nil (fc_singleton t)
  .   



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
    forward P3 emp (fc_singleton (kleene any)) e P4 t' f' -> 
    P1 ==> P3 -> 
    P4 ===> P2 -> 
    inclusion t' t -> 
    futureCondEntail1 f f' -> 
    forward P1 emp (fc_singleton (kleene any)) e P2 t f

  | fw_frame: forall P Q t F e P_frame, 
    forward P emp (fc_singleton (kleene any)) e Q t F -> 
    forward (P\*P_frame) emp (fc_singleton (kleene any)) e (Q\*+P_frame) t F 


  | fw_let : forall x e1 e2 P Q Q1 t2 t3 f2 f3, 
    forward P emp (fc_singleton (kleene any)) e1 Q t2 f2  -> 
    (forall v, forward (Q v) t2 f2 (subst x v e2) Q1 t3 f3 ) -> 
    forward P emp (fc_singleton (kleene any)) (plet x e1 e2) Q1 t3 f3
  
  | fw_val: forall v P ,
    forward P emp (fc_singleton (kleene any)) (pval v) (fun res => P \* \[res = v]) emp (fc_singleton (kleene any))

  | fw_event: forall P (ev:event) ,
    forward P emp (fc_singleton (kleene any)) (pevent ev) (fun res => P \* \[res = vunit]) (theta_singleton ev) (fc_singleton (kleene any))

  | fw_cond : forall (b:bool) e1 e2 t f P Q, 
    forward P emp (fc_singleton (kleene any)) (if b then e1 else e2) Q t f -> 
    forward P emp (fc_singleton (kleene any)) (pif (pval (vbool b)) e1 e2) Q t f

  | fw_deref : forall loc v, 
    forward (loc ~~> v) emp (fc_singleton (kleene any)) (pderef (pval(vloc loc))) (fun res => (loc ~~> v) \* \[res = v]) emp (fc_singleton (kleene any))

  | fw_assign : forall loc v v', 
    forward (loc ~~> v') emp (fc_singleton (kleene any)) (passign (pval(vloc loc)) (pval v)) (fun res => (loc ~~> v) \* \[res = vunit])  emp (fc_singleton (kleene any))

  | fw_assume : forall P f1, 
    forward P emp (fc_singleton (kleene any)) (passume f1) (fun res => P \* \[res = vunit]) emp f1

  | fw_app : forall fromal_arg e actual_arg P Q t f, 
    forward P emp (fc_singleton (kleene any)) (subst fromal_arg actual_arg e) Q t f  -> 
    forward P emp (fc_singleton (kleene any)) (papp (pval (vfun fromal_arg e)) (pval actual_arg)) Q t f

  | fw_structural: forall P Q t f f_ctx t_ctx f_ctx' e, 
    forward P emp (fc_singleton (kleene any)) e Q t f -> 
    futureSubtraction f_ctx t f_ctx' -> 
    forward P t_ctx f_ctx e Q (seq t_ctx t) (fc_conj f_ctx' f)

(*
  | fw_ref : forall v, 
    forward \[] emp (fc_singleton (kleene any)) (pref (pval v)) (fun res => \exists p, \[res = vloc p] \* p ~~> v) emp (fc_singleton (kleene any))
    *)
.


Lemma subtractTheSame: forall f t f1 f2, 
  futureSubtraction f t f1 -> 
  futureSubtraction f t f2 -> 
  f1 = f2. 
Proof. Admitted. 

Lemma subtractFromTrueISTrue: forall ev f, 
  futureSubtraction (fc_singleton (kleene any))
(theta_singleton ev) f -> f = (fc_singleton (kleene any)).
Proof. Admitted. 
   
Lemma futureCondEntail1TrueISTrue: forall f, 
  futureCondEntail1 (fc_singleton (kleene any)) f -> f = (fc_singleton (kleene any)).
Proof. Admitted. 

Lemma weaken_futureCond_big_step : forall h1 r1 f1 e h2 r2 f2 v f3, 
  bigstep h1 r1 f1 e h2 r2 f2 v -> 
  futureCondEntail1 f1 f3 -> 
  exists f4,  
  bigstep h1 r1 f3 e h2 r2 f4 v /\ 
  futureCondEntail1 f4 f2.
Proof. Admitted.   

Lemma strenthen_futureCond_big_step : forall h1 r1 f1 e h2 r2 f2 v f3, 
  bigstep h1 r1 f1 e h2 r2 f2 v -> 
  futureCondEntail1 f3 f1 -> 
  exists f4,  
  bigstep h1 r1 f3 e h2 r2 (fc_conj f4 f2) v. 
Proof. Admitted.  

(* to prove the let rule *)
Lemma strengthening_futureCond_from_pre: forall h3 rho3 f4 e h2 rho2 f0 v Q t2 f2 Q1 t3 f3 , 
  bigstep h3 rho3 f4 e h2 rho2 f0 v -> 
  forward Q t2 f2 e Q1 t3 f3 -> 
  futureCondEntail1 f2 f4 -> 
  exists x0, 
  bigstep h3 rho3 f2 e h2 rho2 (fc_conj x0 f0) v /\ futureCondEntail1 f3 f0. 
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
  pose proof futureCond1_trans.
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
  exists ((fc_singleton (kleene any))).
  split.
  pose proof futureCondEntail1TrueISTrue.
  specialize (H3 f4 H2). subst. 
  rewrite  f_conj_kleene_any_is_f_reverse.
  exact H4. exact H7.
  - 
  intros.
  pose proof futureCondEntail1TrueISTrue.
  specialize (H0 f4 H1). subst. 
  exists ((fc_singleton (kleene any))).
  split.
  rewrite  f_conj_kleene_any_is_f_reverse.
  exact H. invert H.
  intros. subst.
  apply futureCondEntail1_exact.
  - 
  intros.
  pose proof futureCondEntail1TrueISTrue.
  specialize (H0 f4 H1). subst.
  exists ((fc_singleton (kleene any))).
  split.
  rewrite  f_conj_kleene_any_is_f_reverse.
  exact H. invert H.
  intros. subst.
  pose proof subtractFromTrueISTrue.
  specialize (H ev0 f0 H5). subst.  
  apply futureCondEntail1_exact.
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
  pose proof futureCondEntail1TrueISTrue.
  specialize (H f0 H1). subst. 
  exists ((fc_singleton (kleene any))).
  split.
  rewrite  f_conj_kleene_any_is_f_reverse.
  constructor. exact H5.
  apply futureCondEntail1_exact.

  - intros.
  invert H. intros. subst. 
  exists ((fc_singleton (kleene any))).
  rewrite  f_conj_kleene_any_is_f_reverse.
  split. 
  pose proof futureCondEntail1TrueISTrue.
  specialize (H f0 H1). subst. 
  constructor.  exact H10.
  exact H1.
  - intros.
  invert H. intros. subst. 
  exists ((fc_singleton (kleene any))).
  rewrite  f_conj_kleene_any_is_f_reverse.
  pose proof futureCondEntail1TrueISTrue.
  specialize (H f4 H1). subst. 
  split. 
  constructor.
  rewrite  f_conj_kleene_any_is_f_reverse. 
  apply futureCondEntail1_exact. 

  - 
  intros.  
  invert H.  
  intros. subst.   
  specialize (IHforward h3 rho3 f4 H1 h2 rho2 f0 v H12). 
  destr IHforward. 
  exists x0.
  pose proof futureCondEntail1TrueISTrue.
  specialize (H f4 H1). subst. 
  split. 
  constructor. 
  exact H2. exact H3.       

  - intros.
  pose proof futureCondEntail1_exact.
  specialize (H3 (fc_singleton (kleene any))).
  pose proof weaken_futureCond_big_step.
  pose proof anything_future_entail_default. 
  specialize (H5 f4). 
  specialize (H4 h3 rho3 f4 e h2 rho2 f0 v (fc_singleton (kleene any)) H2 H5).   
  destr H4. 
  specialize (IHforward h3 rho3 (fc_singleton (kleene any)) H3 h2 rho2 f1 v H4). 
  destr IHforward.

  pose proof strenthen_futureCond_big_step.
  specialize (H6 h3 rho3 f4 e h2 rho2 f0 v f_ctx H2 H1 ). 
  destr H6.
  exists f2.
  split. exact H10. 
  pose proof futureCond1_trans.
  specialize (H6 f f1 f0 H9 H7).
  pose proof strong_LHS_futureEnatil.
  specialize (H11 f f0 f_ctx' H6).
  exact H11.  
Qed. 


(* to prove the frame rule *)
Lemma frame_big_step: forall h1 h2 h3 h_frame e t f1 f2 v P Q rho1 rho2 F , 
  forward P emp (fc_singleton (kleene any)) e Q t F -> 
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
  specialize (IHforward h1 rho1 f1 h2 rho2 f2 v H0 ).
  Search (Fmap.disjoint _ _). 
  pose proof Fmap.disjoint_empty_r. 
  specialize (H6 loc Val.value h0).  
  specialize (IHforward h0 H4 Fmap.empty H6).


Admitted.  



Lemma prefix_bigstep: forall h1 h2 rho1 rho2 f1 f2 e v, 
  bigstep h1 rho1 f1 e h2 rho2 f2 v -> 
  exists rho3 f3, 
  bigstep h1 nil (fc_singleton (kleene any)) e h2 rho3 f3 v /\ 
  rho2 = rho1 ++ rho3 /\ futureCondEntail1 f2 f3. 
Proof. 
Admitted. 




Theorem soundness : forall P e Q t1 t2 rho1 rho2 h1 v h2 f1 f2 f3,
  forward P t1 f1 e Q t2 f2 ->  
  P h1 -> 
  trace_model rho1 t1 -> 
  bigstep h1 rho1 f1 e h2 rho2 f3 v ->  
  Q v h2 /\ trace_model rho2 t2 /\ futureCondEntail1 f2 f3.  
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
  pose proof futureCond1_trans.
  specialize (H8 f f' f3 H3 H10). 
  exact H8. 
  - (* frame *)
  intros.
  apply hstar_inv in H0. 
  destruct H0 as (h0&h4&H8&H9&H10&H11).  
  pose proof frame_big_step.
  specialize (H0 h1 h2 h0 h4 e t (fc_singleton (kleene any)) f3 v P Q rho1 rho2 F H H2 H8 H10 H11). 
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
  apply futureCondEntail1_exact.

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
  pose proof subtractFromTrueISTrue. 
  specialize (H ev0 f3 H6). 
  subst.
  apply futureCondEntail1_exact. 

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
  apply futureCondEntail1_exact.



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
  apply futureCondEntail1_exact.

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
  rewrite  f_conj_kleene_any_is_f_reverse. 
  apply futureCondEntail1_exact.

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
  pose proof prefix_bigstep.  
  specialize (H4 h1 h2 rho1 rho2 f_ctx f3 e v H3 ). 
  destr H4. 
  specialize (IHforward h1 H1 v h2 nil tm_emp rho3 f0 H5). 
  destr IHforward.
  split. 
  exact H6.
  split. 
  rewrite H4.
  constructor.
  exact H2. exact H9.       


Admitted. 