(*

$ opam pin add coq 8.18.0
$ opam install vscoq-language-server

$ which vscoqtop

opam pin add vscoq-language-server.2.2.1  https://github.com/coq/vscoq/releases/download/v2.2.1/vscoq-language-server-2.2.1.tar.gz
*)

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

Fixpoint normalization (t:theta) : theta := 
  match t with 
  | seq emp t1 => normalization t1
  | _ => t 
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

Definition inclusionCTX : Type := list (theta * theta).

Fixpoint re_eq (t1:theta) (t2:theta) : bool := 
  match t1, t2 with 
  | emp, emp => true 
  | bot, bot => true 
  | any, any => true 
  | theta_singleton ev1, theta_singleton ev2 => 
    if compare_event ev1 ev2 then true else false 
  | seq t1 t2, seq t3 t4 => 
    if (re_eq t1 t3) && (re_eq t2 t4) then true else false 
  | _, _ => false 
  end. 

Fixpoint memberof (t1:theta) (t2:theta) (ctx:inclusionCTX) : bool := 
  match ctx with 
  | nil => false 
  | (t11, t22) :: rest => 
    if (re_eq t1 t11) && re_eq t2 t22 then true 
    else memberof t1 t2 rest
    
  end.


Inductive inclusion : inclusionCTX -> theta -> theta -> bool -> Prop := 
  | (* Disprove *)
    inc_emp: forall ctx t1 t2, 
    nullable t1 -> 
    not (nullable t2) -> 
    inclusion ctx t1 t2 false 

  | (* Reoccur *)
    inc_reoccur: forall ctx t1 t2, 
    memberof t1 t2 ctx -> 
    inclusion ctx t1 t2 true  

  | (* Unfold *)
    inc_unfold: forall ctx t1 t2 ev,
    let deriv1 := theta_der t1 ev in 
    let deriv2 := theta_der t2 ev in 
    let ctx' := (t1, t2) :: ctx in 
    inclusion ctx' deriv1 deriv2 true -> 
    inclusion ctx t1 t2 true

  | inc_exact: forall ctx t, 
    inclusion ctx t t true

  | inc_singleton: forall ctx t1 t2, 
    fst t1 = nil -> 
    inclusion ctx t1 t2 true 
    
  | inc_kleene_any: forall t, 
    inclusion nil t (kleene any) true . 

Theorem inclusion_sound: forall t1 t2 rho, 
  inclusion nil t1 t2 true -> 
  trace_model rho t1 -> 
  trace_model rho t2.
Proof.
  intros.
  invert H.
  - induction ctx. 
    intros. subst.    
    invert H1. 
    intros. subst.
    eapply IHctx.
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


Inductive futureCondEntail : futureCond -> futureCond -> futureCond -> Prop := 
  | futureCondEntail_empty : forall t1 t2, 
    inclusion nil t1 t2 true -> 
    futureCondEntail (fc_singleton t1) (fc_singleton t2)  (fc_singleton (kleene any))
  | futureCondEntail_conj_left : forall f f1 f2 fR1 fR2, 
    futureCondEntail f1 f fR1 -> 
    futureCondEntail f2 f fR2 -> 
    futureCondEntail (fc_conj f1 f2) f  (fc_singleton (kleene any))
  | futureCondEntail_conj_right : forall f f1 f2 fR1 fR2, 
    futureCondEntail f f1 fR1 -> 
    futureCondEntail f f2 fR2 -> 
    futureCondEntail f (fc_conj f1 f2) (fc_conj fR1 fR2) 

  .

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
  inclusion nil t1 t2 true ->
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
    constructor.
    specialize (IHfutureCondEntail1 H3).
    specialize (IHfutureCondEntail2 H4).
    pose proof fc_conj_to_trace.
    specialize (H2 rho0 f fR1 IHfutureCondEntail1).
    destr H2. 
    exact H5.
    pose proof every_rho_models_kleene_any.
    specialize (H2 rho0 ).
    apply trace_to_fc_singleton.  
    exact H2. 
  - specialize (IHfutureCondEntail1 H0).
    specialize (IHfutureCondEntail2 H0).
    pose proof fc_conj_to_trace.
    specialize (H2 rho0 f1 fR1 IHfutureCondEntail1). 
    pose proof fc_conj_to_trace.
    specialize (H3 rho0 f2 fR2 IHfutureCondEntail2).
    destr H2. destr H3. 
    constructor. 
    constructor. 
    exact H4. exact H2. 
    constructor.
    exact H5. exact H6. 
Qed. 


  


Lemma futureCondEntail_exact : forall f, 
  futureCondEntail f f.
Proof.
  intros.
  induction f.
  - constructor.
    apply inc_exact.
  - eapply futureCondEntail_conj_left.
    eapply futureCondEntail_conj_right.
    eauto.
  
Admitted.

Inductive futureSubtraction : futureCond -> theta -> futureCond -> Prop :=  
  | futureSubtraction_empty : forall f, 
    futureSubtraction f emp f.  


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

Inductive forward : hprop -> theta -> futureCond -> expr -> (val -> hprop) -> theta -> futureCond -> Prop := 
  | fw_let : forall x e1 e2 P Q Q1 t1 t2 t3 f1 f2 f3, 
    forward P t1 f1 e1 Q t2 f2  -> 
    (forall v, forward (Q v) t2 f2 (subst x v e2) Q1 t3 f3 ) -> 
    forward P t1 f1 (plet x e1 e2) Q1 t3 f3
  
  | fw_val: forall t f v P ,
    forward P t f (pval v) (fun res => P \* \[res = v]) t f

  | fw_cond : forall (b:bool) e1 e2 t t1 f f1 P Q, 
    forward P t f (if b then e1 else e2) Q t1 f1 -> 
    forward P t f (pif (pval (vbool b)) e1 e2) Q t1 f1

  | fw_event: forall t f P (ev:event) f',
    futureSubtraction f (theta_singleton ev) f' -> 
    forward P t f (pevent ev) (fun res => P \* \[res = vunit]) (seq t (theta_singleton ev)) f'

  | fw_ref : forall t f v, 
    forward \[] t f (pref (pval v)) (fun res => \exists p, \[res = vloc p] \* p ~~> v) t f
  
  | fw_deref : forall t f loc v, 
    forward (loc ~~> v) t f (pderef (pval(vloc loc))) (fun res => (loc ~~> v) \* \[res = v])  t f

  | fw_assign : forall t f loc v v', 
    forward (loc ~~> v') t f (passign (pval(vloc loc)) (pval v)) (fun res => (loc ~~> v) \* \[res = vunit])  t f

  | fw_assume : forall P t f f1, 
    forward P t f (passume f1) (fun res => P \* \[res = vunit])  t (fc_conj f f1) 

  | fw_app : forall vf fromal_arg e actual_arg P t f Q t1 f1 f' fR fR', 
    vf = vfun fromal_arg e  ->
    forward P emp f (subst fromal_arg actual_arg e) Q t1 f1  -> 
    futureCondEntail f' f fR -> 
    futureSubtraction fR t1 fR' -> 
    forward P t f' (papp (pval vf) (pval actual_arg)) Q t1 (fc_conj fR' f1) 
.

Lemma strengthening_futureCond_from_pre: forall f1 f2 fR h1 rho1 e h2 rho2 f v, 
  futureCondEntail f1 f2 fR -> 
  bigstep h1 rho1 f2 e h2 rho2 f v -> 
  bigstep h1 rho1 f1 e h2 rho2 f v. 
Proof. 
  intros.
Admitted. 

Lemma subtractTheSame: forall f t f1 f2, 
  futureSubtraction f t f1 -> 
  futureSubtraction f t f2 -> 
  f1 = f2. 
Proof. Admitted. 


Theorem soundness : forall P e Q t1 t2 rho1 rho2 h1 v h2 f1 f2 f3,
  forward P t1 f1 e Q t2 f2 ->  
  P h1 -> 
  trace_model rho1 t1 -> 
  bigstep h1 rho1 f1 e h2 rho2 f3 v ->  
  Q v h2 /\ trace_model rho2 t2 /\ exists f_Res, futureCondEntail f2 f3 f_Res.  
Proof. 
  introv.
  intros. 
  gen h1 v h2 rho1 rho2 f3.
  induction H.
  - (* let *)
  intros.
  invert H4. intros. subst.
  specialize (IHforward h1).
  specialize (IHforward H2).
  specialize (IHforward v0 h3 rho1).
  specialize (IHforward H3).
  specialize (IHforward rho3 f5).
  specialize (IHforward H15).
  destr IHforward.
  eapply H1.
  exact  H4.
  exact H6.
  eapply strengthening_futureCond_from_pre. 
  exact H5.
  exact H16.
  - (* val *)
  intros.
  invert H2.
  intros. subst.
  split.
  rewrite hstar_hpure_r.
  split. subst. auto.
  reflexivity.
  split. subst. auto.
  exists (fc_singleton(kleene any)).
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
  apply trace_model_prefix.
  exact H1.
  constructor. reflexivity.
  exists (fc_singleton(kleene any)).
  pose proof (subtractTheSame).
  specialize (H2 f (theta_singleton ev0) f' f3).
  specialize (H2 H H7).
  subst. 
  apply futureCondEntail_exact.
  -  (* ref *)
  intros.
  invert H2.
  intros. 
  split. 
  exists loc0. subst.  
  rewrite hstar_hpure_l.
  split.
  reflexivity.
  Search (\[]).
  apply hempty_inv in H0. 
  rewrite H0.
  Search (Fmap.update).
  rewrite (update_empty).
  apply hsingle_intro.
  split.
  subst. exact H1.
  exists (fc_singleton(kleene any)).
  apply futureCondEntail_exact.

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
  exists (fc_singleton(kleene any)).
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
  exists (fc_singleton(kleene any)).
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
  exists (fc_singleton(kleene any)).
  apply futureCondEntail_exact.

  - (* fun call *)
  intros.
  invert H2.
  intros. subst.
  invert H5.
Qed.   



