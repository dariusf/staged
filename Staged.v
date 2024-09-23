
From Coq Require Import Classes.RelationClasses.
(* From Coq Require Setoid Morphisms Program.Basics. *)
From Coq Require Morphisms Program.Basics.

From SLF Require LibSepFmap.
Module Fmap := LibSepFmap.

From SLF Require Export Extra Heap Tactics.

Local Open Scope string_scope.
(* Local Open Scope nat_scope. *)
Local Open Scope Z_scope.
Local Open Scope list_scope.

Set Implicit Arguments.

(** * Programs *)
(** The representation of programs, substitution, and the big-step semantics are mostly reused from SLF. *)
Definition ident : Type := string.
Definition ident_eq := String.string_dec.

Inductive val :=
  | vunit : val
  | vint : Z -> val
  | vfun : ident -> expr -> val
  | vfix : ident -> ident -> expr -> val

with expr : Type :=
  | pvar (x: ident)
  | pval (v: val)
  | plet (x: ident) (e1 e2: expr)
  | pfix (f: ident) (x: ident) (e: expr)
  | pfun (x: ident) (e: expr)
  | padd (x y: val)
  | pminus (x y: val)
  (* | pref (x: ident) *)
  (* | pderef (x: ident) *)
  (* | passign (x1: ident) (x2: ident) *)
  | pif (x: val) (e1: expr) (e2: expr)
  | pcall (x: val) (a: val).

Global Instance Inhab_val : Inhab val.
Proof.
  constructor.
  exists vunit.
  constructor.
Qed.

Fixpoint subst (y:ident) (w:val) (e:expr) : expr :=
  let aux t := subst y w t in
  let if_y_eq x t1 t2 := if ident_eq x y then t1 else t2 in
  match e with
  | pval v => pval v
  | padd x y => padd x y
  | pminus x y => pminus x y
  | pvar x => if_y_eq x (pval w) e
  | pfun x t1 => pfun x (if_y_eq x t1 (aux t1))
  | pfix f x t1 => pfix f x (if_y_eq f t1 (if_y_eq x t1 (aux t1)))
  | pcall t1 t2 => pcall t1 t2
  | plet x t1 t2 => plet x (aux t1) (if_y_eq x t2 (aux t2))
  | pif t0 t1 t2 => pif t0 (aux t1) (aux t2)
  end.

(** SLF's heap theory as a functor *)
Module Val.
  Definition val := val.
End Val.

Module Export Heap := Heap.HeapSetup(Val).

Inductive eresult : Type :=
  | enorm : val -> eresult.

Inductive bigstep : heap -> expr -> heap -> eresult -> Prop :=
  | eval_pval : forall h v,
    bigstep h (pval v) h (enorm v)

  | eval_padd : forall h x y,
    bigstep h (padd (vint x) (vint y)) h (enorm (vint (x + y)))

  | eval_pminus : forall h x y,
    bigstep h (pminus (vint x) (vint y)) h (enorm (vint (x - y)))

  | eval_pfun : forall h x e,
    bigstep h (pfun x e) h (enorm (vfun x e))

  | eval_pfix : forall h x e f,
    bigstep h (pfix f x e) h (enorm (vfix f x e))

  | eval_app_fun : forall v1 v2 h x e r,
    v1 = vfun x e ->
    bigstep h (subst x v2 e) h r ->
    bigstep h (pcall v1 v2) h r

  | eval_app_fix : forall v1 v2 h x e r f,
    v1 = vfun x e ->
    bigstep h (subst x v2 (subst f v1 e)) h r ->
    bigstep h (pcall v1 v2) h r.

  (* there is no var rule *)

  (* | eval_plet : forall x e1 e2 v s h h2 s2 s1 h1 r,
    eval[ s, h, e1 ] => [ s1, h1, enorm v] ->
    eval[ supdate x v s1, h1, e2 ] => [ s2, h2, r] ->
    eval[ s, h, plet x e1 e2 ] => [ s2, h2, r ] *)

  (* | eval_pref : forall x s (h:heap) l,
    h l = None ->
    eval[ s, h, pref x ] => [ s, hupdate l (s x) h, enorm l]
  | eval_deref : forall x s (h:heap) v,
    h (s x) = Some v ->
    eval[ s, h, pderef x ] => [ s, h, enorm v]
  | eval_assign : forall x1 x2 s h,
    eval[ s, h, passign x1 x2 ] => [ s, hupdate (s x1) (s x2) h, enorm 0] *)

Definition empty_heap : heap := Fmap.empty.

Definition precond := hprop.
Definition postcond := val -> hprop.

Inductive result : Type :=
  | norm : val -> result.

Definition compatible r1 r2 :=
  match (r1, r2) with
  | (norm r3, enorm r4) => r3 = r4
end.

(** * Staged formulae *)
(** Deeply embedded due to uninterpreted functions, which cannot immediately be given a semantics without an environment. *)
Inductive flow :=
  | req : precond -> flow
  | ens : postcond -> flow
  | seq : flow -> flow -> flow
  | fex : forall A, (A -> flow) -> flow
  | fall : forall A, (A -> flow) -> flow
  | unk : ident -> val -> val -> flow
  | disj : flow -> flow -> flow.

(** An [ens] which doesn't have a useful return value *)
Definition ens_ H := ens (fun r => \[r = vunit] \* H).

(* Definition empty := ens_ \[True]. *)
Definition empty := ens (fun r => \[True]).

(** Function environments, for interpreting unknown functions. [ufun] is a HOAS way of substituting into a staged formula, which otherwise doesn't support this due to the shallow embedding that [hprop] uses. *)
Definition ufun := val -> val -> flow.
Definition env := fmap ident (option ufun).

Definition empty_env : env := Fmap.empty.

Declare Scope flow_scope.
Open Scope flow_scope.

Infix ";;" := seq (at level 80, right associativity) : flow_scope.

Notation "'∃' x1 .. xn , H" :=
  (fex (fun x1 => .. (fex (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '∃' '/ '  x1  ..  xn , '/ '  H ']'",
   only printing) : flow_scope.

Notation "f '$' '(' x ',' r ')'" := (unk f x r)
  (at level 80, format "f '$' '(' x ','  r ')'", only printing) : flow_scope.

(* Notation "'ens' '[' r ']' Q" := (ens (fun r => Q))
  (at level 80, format "'ens' '\[' r '\]' Q" , only printing) : flow_scope. *)
(* square brackets will conflict with format notation for boxes https://coq.inria.fr/doc/V8.20.0/refman/user-extensions/syntax-extensions.html#displaying-symbolic-notations:~:text=well%2Dbracketed%20pairs%20of%20tokens%20of%20the%20form%20%27%5B%20%27%20and%20%27%5D%27 *)

Notation "'ens' r '.' Q" := (ens (fun r => Q))
  (at level 80, format "'ens'  r '.'  Q" , only printing) : flow_scope.

Notation "'ens' Q" := (ens_ Q)
  (at level 80, format "'ens'  Q" , only printing) : flow_scope.

(** * Interpretation of a staged formula *)
(** Differs from the paper's definition in:
    
- the addition of an environment, to give interpretations for unknown functions
- the removal of stores, to sidestep impredicativity problems

An [Inductive] definition is used because the rule for unknown functions is not structurally recursive. *)
Inductive satisfies : env -> flow -> heap -> heap -> result -> Prop :=

  | s_req env p h1 h2 r
    (H: exists h3,
      h1 = Fmap.union h2 h3 /\
      Fmap.disjoint h2 h3 /\
      p h3)
    (Hr: r = norm vunit) :
    satisfies env (req p) h1 h2 r

  | s_ens env q h1 h2 r
    (H: exists v h3,
      r = norm v /\
      q v h3 /\
      h2 = Fmap.union h1 h3 /\
      Fmap.disjoint h1 h3) :
    satisfies env (ens q) h1 h2 r

  | s_seq env f1 f2 h1 h2 r
    (H: exists h3 r1,
      satisfies env f1 h1 h3 r1 /\
      satisfies env f2 h3 h2 r) :
    satisfies env (seq f1 f2) h1 h2 r

  | s_fex env h1 h2 r (A:Type) (f:A->flow)
    (H: exists v,
      satisfies env (f v) h1 h2 r) :
    satisfies env (@fex A f) h1 h2 r

  | s_fall env h1 h2 r (A:Type) (f:A->flow)
    (H: forall v,
      satisfies env (f v) h1 h2 r) :
    satisfies env (@fall A f) h1 h2 r

  | s_unk env fn h1 h2 r f x
    (He: Fmap.read env fn = Some f)
    (Hr: satisfies env (f x r) h1 h2 (norm r)) :
    satisfies env (unk fn x r) h1 h2 (norm r)

  | s_disj_l env h1 h2 r f1 f2
    (H: satisfies env f1 h1 h2 r) :
    satisfies env (disj f1 f2) h1 h2 r

  | s_disj_r env h1 h2 r f1 f2
    (H: satisfies env f2 h1 h2 r) :
    satisfies env (disj f1 f2) h1 h2 r.

Notation "env ','  h1 ','  h2 ','  r  '|=' f" :=
  (satisfies env f h1 h2 r) (at level 30, only printing).

(** The result of a staged formula, written in the paper as [Φ[r]]. *)
Definition flow_res (f:flow) (v:val) : Prop :=
  exists h1 h2 env, satisfies env f h1 h2 (norm v).

(** * Entailment *)
(** This is defined directly in terms of the semantics, in contrast to the paper's syntactic definition. *)
(* TODO the paper's definition should later be implemented as an Inductive here and proved sound with respect to the lemmas we can write using this semantic definition *)
Definition entails_under env (f1 f2:flow) : Prop :=
  forall h1 h2 r,
    satisfies env f1 h1 h2 r -> satisfies env f2 h1 h2 r.

Definition entails (f1 f2:flow) : Prop :=
  forall env, entails_under env f1 f2.

Infix "⊑" := entails (at level 90, right associativity) : flow_scope.

Definition entailed_by f1 f2 := entails f2 f1.

Notation "env '⊢' f1 '⊑' f2" :=
  (entails_under env f1 f2) (at level 90, only printing) : flow_scope.

(* Unset Printing Notations. Set Printing Coercions. Set Printing Parentheses. *)
(* Check (forall f1 f2 f3, f1 ;; f3 ⊑ f2). *)

Definition bientails (f1 f2:flow) : Prop :=
  forall h1 h2 r env,
    satisfies env f1 h1 h2 r <-> satisfies env f2 h1 h2 r.

(** * Rewriting *)

Instance entails_refl : Reflexive entails.
Proof.
  unfold Reflexive.
  unfold entails.
  unfold entails_under.
  intros.
  exact H.
Qed.

Instance entails_trans : Transitive entails.
Proof.
  unfold Transitive.
  intros.
  unfold entails in *.
  unfold entails_under in *.
  intros.
  apply H0.
  apply H.
  apply H1.
Qed.

Instance bientails_equiv : Equivalence bientails.
Proof.
  constructor.
  - unfold Reflexive.
    unfold bientails.
    reflexivity.
  - unfold Symmetric.
    unfold bientails.
    symmetry.
    auto.
  - unfold Transitive.
    unfold bientails.
    intros.
    split.
    + intros. apply H0. apply H. easy.
    + intros. apply H. apply H0. easy.
Qed.

(** Incantations for setoid rewriting *)
Section Proprium.

  (* for sanity *)
  Local Infix "====>" := Morphisms.respectful (at level 80, right associativity).

  Local Notation Proper := Morphisms.Proper.
  Local Notation respectful := Morphisms.respectful.
  Local Notation impl := Program.Basics.impl.

  (** This reflects how entailment is contravariant in the antecedent and covariant in the consequent *)
  #[global]
  Instance Proper_entails : Proper
    (entailed_by ====> entails ====> impl)
    entails.
  Proof.
    unfold entailed_by, entails, entails_under, Proper, respectful, impl.
    intros.
    auto.
  Qed.

  #[global]
  Instance Proper_bientails : Proper
    (bientails ====> bientails ====> iff)
    entails.
  Proof.
    unfold bientails, entailed_by, entails, entails_under, Proper, respectful, impl.
    split; intros.
    { apply H0. apply H1. apply H. auto. }
    { apply H0. apply H1. apply H. auto. }
  Qed.

  #[global]
  Instance Proper_satisfies : Proper
    (eq ====> entails ====> eq ====> eq ====> eq ====> impl)
    satisfies.
  Proof.
    unfold entails, entails_under, Proper, respectful, impl.
    intros. subst.
    auto.
  Qed.

  #[global]
  Instance Proper_seq : Proper (entails ====> entails ====> entails) seq.
  Proof.
      unfold Proper, entails, entails_under, respectful.
      intros.
      inverts H1 as H1; destr H1.
      constructor. exists h3. exists r1.
      eauto.
  Qed.

  #[global]
  Instance Proper_seq_bi : Proper (bientails ====> bientails ====> bientails) seq.
  Proof.
      unfold Proper, bientails, entails, entails_under, respectful.
      intros.
      split; intros.
      { inverts H1 as H1; destr H1.
        constructor. exists h3. exists r1.
        split.
        apply H; auto.
        apply H0; auto. }
      { inverts H1 as H1; destr H1.
        constructor. exists h3. exists r1.
        split.
        apply H; auto.
        apply H0; auto. }
  Qed.

End Proprium.

(** * Reasoning about flows *)
(** Covariance of ens *)
Lemma satisfies_ens : forall Q1 Q2 env h1 h2 r,
  (forall v, Q1 v ==> Q2 v) ->
  satisfies env (ens Q1) h1 h2 r ->
  satisfies env (ens Q2) h1 h2 r.
Proof.
  intros.
  inverts H0.
  constructor.
  destruct H3 as (v&h3&?&?&?&?).
  exists v.
  exists h3.
  intuition.
  apply H.
  easy.
Qed.

Lemma entail_ens : forall Q1 Q2,
  (forall v, Q1 v ==> Q2 v) -> entails (ens Q1) (ens Q2).
Proof.
  unfold entails.
  unfold entails_under.
  intros.
  applys* satisfies_ens.
Qed.

(* TODO contravariance *)

Lemma extract_pure : forall P env h1 h2 r,
  satisfies env (ens (fun _ => \[P])) h1 h2 r -> P /\ h1 = h2.
Proof.
  intros.
  inverts H as H.
  destr H.
  inverts H.
  inverts H2.
  intuition.
Qed.

(* the next two are technically just inversion lemmas but are less tedious *)
Lemma ens_ret_unit : forall env h1 h2 H r,
  satisfies env (ens_ H) h1 h2 r ->
  r = norm vunit.
Proof.
  intros.
  inverts H0 as H0.
  destruct H0 as (v&h3&H1&H2&H3&H4).
  rewrite hstar_hpure_l in H2.
  destruct H2.
  congruence.
Qed.

Lemma req_ret_unit : forall env h1 h2 H r,
  satisfies env (req H) h1 h2 r ->
  r = norm vunit.
Proof.
  intros.
  inverts H0.
  reflexivity.
Qed.

Lemma req_emp_inv : forall env h1 h2 r,
  satisfies env (req \[]) h1 h2 r ->
  h1 = h2 /\ r = norm vunit.
Proof.
  intros.
  inverts H.
  split; only 2: reflexivity.
  destruct H2 as (h3&H1&H2&H3).
  inverts H3.
  rewrite <- Fmap.union_empty_r.
  exact H1.
Qed.

Lemma satisfies_fn_in_env : forall env h1 h2 r1 x f1 f r,
  satisfies env (unk f x r1) h1 h2 r ->
  Fmap.read env f = Some f1 ->
  satisfies env (f1 x r1) h1 h2 r.
Proof.
  intros.
  inverts H as H.
  rewrite H in H0.
  inj H0.
  easy.
Qed.

Lemma embed_pure : forall P env h r,
  P -> satisfies env (ens (fun _ => \[P])) h h r.
Proof.
  intros.
  constructor.
  destruct r.
  exists v.
  exists empty_heap.
  intuition.
  apply hpure_intro; easy.
  fmap_eq.
Qed.

Lemma req_emp_intro : forall env h1,
  satisfies env (req \[]) h1 h1 (norm vunit).
Proof.
  intros.
  constructor.
  exists empty_heap.
  intuition fmap_eq.
  constructor.
  reflexivity.
Qed.

Lemma ens_emp_intro : forall env h1 r,
  satisfies env (ens (fun r => \[])) h1 h1 r.
Proof.
  intros.
  constructor.
  destruct r.
  exists v.
  exists empty_heap.
  intuition fmap_eq.
  constructor.
Qed.

Lemma seq_req_emp_elim_l : forall env h1 h2 r Q,
  satisfies env (req \[];; ens Q) h1 h2 r ->
  satisfies env (ens Q) h1 h2 r.
Proof.
  intros.
  inverts H.
  destruct H6 as (h3&r1&H1&H2).
  apply req_emp_inv in H1; destruct H1; subst.
  exact H2.
Qed.

Lemma seq_req_emp_intro_l : forall env h1 h2 r Q,
  satisfies env (ens Q) h1 h2 r ->
  satisfies env (req \[];; ens Q) h1 h2 r.
Proof.
  intros.
  constructor.
  exists h1.
  exists (norm vunit).
  split.
  apply req_emp_intro.
  exact H.
Qed.

Lemma seq_assoc : forall env h1 h2 r f1 f2 f3,
  satisfies env (f1;; f2;; f3) h1 h2 r <->
  satisfies env ((f1;; f2);; f3) h1 h2 r.
Proof.
  intros.
  split; intros H.
  { inverts H as H. destruct H as (h3&r1&H1&H2).
    inverts H2 as H2. destruct H2 as (h0&r0&H3&H4).
    constructor.
    exists h0. exists r0.
    split; auto.
    constructor.
    exists h3. exists r1.
    intuition. }
  { inverts H as H. destruct H as (h3&r1&H1&H2).
    inverts H1 as H1. destruct H1 as (h0&r0&H3&H4).
    constructor.
    exists h0. exists r0.
    split; auto.
    constructor.
    exists h3. exists r1.
    intuition. }
Qed.

Lemma norm_seq_assoc : forall f1 f2 f3,
  bientails (f1;; f2;; f3) ((f1;; f2);; f3).
Proof.
  intros.
  split; intros H; now apply seq_assoc.
Qed.

Ltac felim H :=
  match type of H with
  | satisfies _ (fex _) _ _ _ => inverts H as H
  | satisfies _ (_ ;; _) _ _ _ => inverts H as H
  | satisfies _ (ens (fun _ => \[_])) _ _ _ => apply extract_pure in H
  | satisfies _ (req \[]) _ _ _ => apply req_emp_inv in H; subst
  (* | satisfies _ (unk _ _ _) _ _ _ => inverts H as H *)
  end.

Ltac fintro :=
  match goal with
  | |- satisfies _ (ens (fun _ => \[_])) _ _ _ => apply embed_pure
  | |- satisfies _ (ens (fun _ => \[])) _ _ _ => apply ens_emp_intro
  | |- satisfies _ (req \[]) _ _ _ => apply req_emp_intro
  | |- satisfies _ (req \[];; _) _ _ _ => apply seq_req_emp_intro_l
  end.

(* Ltac fexists v :=
  match goal with
  | |- satisfies _ (fex _) _ _ _ => unfold fex; exists v
  end. *)

(** * Normalization rules and biabduction *)

Lemma norm_req_sep_combine : forall H1 H2,
  entails (req H1;; req H2) (req (H1 \* H2)).
Proof.
  unfold entails.
  unfold entails_under.
  intros.
  inverts H as H.
  destruct H as (h3 & r1 & H3 & H4).

  inverts H3 as H3.
  inverts H4 as H4.
  destruct H3 as (h4 & ? & ? & ?).
  destruct H4 as (h5 & ? & ? & ?).
  (* h4 is the part satisfying P, same for h5/Q *)
  constructor.
  (* union h4/h5 to get the part satisfying P*Q *)

  exists (h4 \+ h5).
  subst h1 h3.
  rew_disjoint.
  (* fmap_disjoint. *)
  intuition.
  fmap_eq.
  apply hstar_intro; easy.
  reflexivity.
Qed.

Lemma norm_req_sep_split : forall H1 H2,
  entails (req (H1 \* H2)) (req H1;; req H2).
Proof.
  unfold entails.
  unfold entails_under.
  intros.
  inverts H as H.
  (* h3 is the piece satisfying H1*H2 *)
  destruct H as (h3 & r1 & H3 & H4).
  apply hstar_inv in H4.
  destruct H4 as (h0 & h4 & ? & ? & ? & ?).
  (* split h3. h0 is for H1, h4 for H2 *)
  subst h1.
  constructor.
  exists (h2 \u h4).
  exists (norm vunit).
  split; constructor.
  exists h0. intuition fmap_eq.
  reflexivity.
  fmap_eq.
  exists h4. intuition fmap_eq.
  reflexivity.
Qed.

Lemma norm_req_req : forall H1 H2,
  bientails (req (H1 \* H2)) (req H1;; req H2).
Proof.
  intros.
  split.
  - apply norm_req_sep_split.
  - apply norm_req_sep_combine.
Qed.

Section Examples.
  Example ex1_rewrite : forall H H1,
    entails (req (H \* H1)) (req H;; req H1).
  Proof.
    intros.
    rewrite norm_req_req.
    apply entails_refl.
  Qed.

  Example ex3_rewrite : forall H H1,
    bientails (req (H \* H1)) (req H;; req H1).
  Proof.
    intros.
    unfold bientails; split.
    { rewrite norm_req_sep_split.
      trivial. }
    { rewrite norm_req_sep_combine.
      apply entails_refl. }
  Qed.

  Example ex2_rewrite : forall H H1 H2,
    entails (req (H \* H1);; req H2) (req H;; (req (H1 \* H2))).
  Proof.
    intros.
    rewrite norm_req_req.
    rewrite norm_req_req.
    rewrite norm_seq_assoc.
    apply entails_refl.
  Qed.
End Examples.

Lemma sat_ens_void_sep_combine : forall H1 H2 env h1 h2 r,
  satisfies env (ens_ H1;; ens_ H2) h1 h2 r <->
  satisfies env (ens_ (H1 \* H2)) h1 h2 r.
Proof.
  intros.
  split; intros.
  { inverts H as H.
    destruct H as (h3&r1&H3&H4).
    (* inverts H3 as H3. *)
    (* destruct H3 as (v&h0&H8&H5&H6&H7). *)
    (* give up on careful reasoning *)
    inv H3. destr H5. inv H4. destr H8. subst.
    constructor.
    exists v0.
    exists (h0 \u h3).
    rewrite hstar_hpure_l in H0.
    rewrite hstar_hpure_l in H3.
    intuition.
    subst.
    rewrite <- hstar_assoc.
    apply hstar_intro.
    rewrite hstar_hpure_l.
    intuition.
    intuition.
    fmap_disjoint.
    fmap_eq. }
  { inverts H as H. destruct H as (v&h3&H3&H4&H5&H6).
    rewrite hstar_hpure_l in H4. destruct H4 as (H4&H7).
    (* h3 is the heap that H1 and H2 together add *)
    (* find the intermediate heap *)
    apply hstar_inv in H7. destruct H7 as (h0&h4&H8&H9&H10&H11).
    (* H1 h0, H2 h4 *)
    constructor.
    exists (h1 \u h0).
    exists (norm vunit).
    split.
    { constructor. exists vunit. exists h0. intuition. rewrite hstar_hpure_l. intuition. }
    { constructor. exists v. exists h4. intuition. rewrite hstar_hpure_l. intuition. fmap_eq. } }
Qed.

Lemma sat_ens_sep_combine : forall Q1 Q2 env h1 h2 r,
  satisfies env (ens Q1;; ens Q2) h1 h2 r ->
  satisfies env (ens (fun r0 : val => \exists r1 : val, Q1 r1 \* Q2 r0)) h1 h2 r.
Proof.
  intros.
  felim H.
  destruct H as (h3 & r1 & H1 & H2).

  constructor. destruct r.
  exists v.
  inverts H1 as H1. destruct H1 as (v0 & h0 & ? & ? & ? & ?).
  inverts H2 as H2. destruct H2 as (v1 & h4 & ? & ? & ? & ?).
  exists (h0 \u h4).
  intuition.
  apply hexists_intro with (x := v0).

  apply hstar_intro; auto.
  subst. inj H2. assumption.
  subst. rew_fmap.
  reflexivity.
Qed.

Lemma ens_sep_combine : forall Q1 Q2,
  entails (ens Q1;; ens Q2) (ens (fun r => \exists r1, Q1 r1 \* Q2 r)).
Proof.
  unfold entails.
  unfold entails_under.
  apply sat_ens_sep_combine.
Qed.

Lemma sat_ens_sep_split : forall H Q env h1 h2 r,
  satisfies env (ens (Q \*+ H)) h1 h2 r  ->
  satisfies env (ens (fun _ : val => H);; ens Q) h1 h2 r.
Proof.
  intros.
  inverts H0 as H0.
  destruct H0 as (v & h3 & H1 & H2 & H3 & H4).
  (* h3 is the part satisfying both *)
  apply hstar_inv in H2.
  destruct H2 as (h0 & h4 & ? & ? & ? & ?).
  (* h0 is the part satisfying Q, h4 H *)

  constructor.
  exists (h1 \u h4).
  exists (norm v). (* anything? *)
  split.

  constructor.
  eexists.
  eexists.
  intuition.
  auto.

  constructor.
  exists v.
  exists h0.
  intuition.
  subst.
  rew_fmap.
  assert (h0 \u h4 = h4 \u h0). fmap_eq.
  rewrite H1.
  reflexivity.
Qed.

Lemma ens_sep_split : forall H Q,
  entails (ens (Q \*+ H)) (ens (fun _ => H);; ens Q).
Proof.
  unfold entails.
  unfold entails_under.
  apply sat_ens_sep_split.
Qed.

Inductive biab : hprop -> hprop -> hprop -> hprop -> Prop :=

  | b_pts_match : forall a b H1 H2 Ha Hf x,
    biab Ha H1 H2 Hf ->
    biab (\[a=b] \* Ha) (x~~>a \* H1) (x~~>b \* H2) Hf

  | b_base_empty : forall Hf,
    biab \[] Hf \[] Hf.

Module BiabductionExamples.

  (* (a=3) * x->a*y->b |- x->3 * (y->b) *)
  Example ex1_biab : forall x y,
    exists Ha Hf a, biab Ha (x~~>vint a \* y~~>vint 2) (x~~>vint 3) Hf.
  Proof.
    intros.
    eexists.
    eexists.
    eexists.
    rewrite <- (hstar_hempty_r (x ~~> vint 3)) at 2.
    apply b_pts_match.
    apply b_base_empty.
  Qed.

  (* we can see from the ex_intro constrs that the frame is y->2, and the abduced contraint is trivial but gives a value to a, which was immediately substituted *)
  (* Print ex1_biab. *)

  Example ex2_biab :
    exists Ha Hf,
    exists r, biab Ha (\[r = 1]) hempty Hf.
  Proof.
    intros.
    eexists.
    eexists.
    exists 1.
    apply b_base_empty.
  Qed.
  (* Print ex2_biab. *)

  Example ex3_wand : forall x y,
    (x ~~> vint 1 \* y ~~> vint 2) ==>
    (x~~>vint 1 \* (x~~>vint 1 \-* (x~~>vint 1 \* y ~~> vint 2))).
  Proof.
    xsimpl.
  Qed.

End BiabductionExamples.

Lemma seq_req_emp_equiv : forall env h1 h2 H,
  satisfies env (ens_ H) h1 h2 (norm vunit) <->
  satisfies env (ens_ H;; req \[]) h1 h2 (norm vunit).
Proof.
  intros.
  split.
  { intros. constructor.
  eexists. exists (norm vunit).
  split; only 2: apply req_emp_intro.
  constructor.
  inverts H0. destruct H3 as (v&h3&H1&H2&H3&H4).
  exists vunit.
  exists h3.
  intuition.
  inj H1.
  auto. }
  { intros.
    inverts H0 as H0.
    destruct H0 as (h3&r1&H1&H2).
    pose proof (ens_ret_unit H1); subst.
    inverts H2 as H2; destruct H2 as (h0&H4&H5&H6);
      inverts H6;
      rewrite Fmap.union_empty_r in H4;
      subst.
    inverts H1.
    destruct H3 as (v&h3&H1&H2&H3&H4).
    constructor.
    exists vunit.
    exists h3.
    intuition.
    inj H1; assumption.
  }
Qed.

(* biabduction for a single location, semantically *)
Lemma biab_sem : forall x a b env h1 h2 r,
  satisfies env (ens_ (x~~>a);; req (x~~>b)) h1 h2 r ->
  satisfies env (req \[a = b]) h1 h2 r.
Proof.
  intros.
  felim H.
  destruct H as (h3&r1&H1&H2).
  inverts H1 as H1.
  inverts H2 as H2.
  (* have to prove that a=b in h3 *)
  destr H1.
  destr H2.
  rewrite hstar_hpure_l in H0.
  destruct H0.
  apply hsingle_inv in H5.
  apply hsingle_inv in H6.

  assert (a = b).
  (* factor this out into a new map lemma *)
  { assert (Fmap.read h3 x = b) as ?.
    { rewrite H2.
      rewrite Fmap.read_union_r.
      subst.
      apply Fmap.read_single.
      pose proof (@Fmap.disjoint_inv_not_indom_both _ _ _ _ x H3).
      unfold not.
      intros.
      specialize (H7 H8).
      apply H7.
      subst h4.
      apply Fmap.indom_single. }

    assert (Fmap.read h3 x = a) as ?.
    { rewrite H1.
      rewrite Fmap.read_union_r.
      subst.
      apply Fmap.read_single.
      pose proof (@Fmap.disjoint_inv_not_indom_both _ _ _ _ x H4).
      unfold not.
      intros.
      specialize (H8 H9).
      apply H8.
      subst h0.
      apply Fmap.indom_single. }

    rewrite H8 in H7.
    assumption. }

  assert (h1 = h2).
  { subst.
    pose proof (Fmap.union_eq_inv_of_disjoint H4 H3).
    apply H.
    assumption. }

  constructor.
  exists empty_heap.
  intuition fmap_eq.
  apply hpure_intro; reflexivity.
  reflexivity.
Qed.

Lemma ens_req_transpose : forall H H1 Ha Hf (v:val),
  biab Ha (H1 v) H (Hf v) ->
  entails (ens_ (H1 v);; req H)
    (req Ha;; ens_ (Hf v)).
Proof.
  unfold entails.
  unfold entails_under.
  introv Hbi.
  induction Hbi.
  { intros.
    specialize (IHHbi env0).

    (* Check req_sep. *)
    (* assert (
       satisfies env0 (ens_ (x~~>a \* H0);; req (x~~>b \* H2)) h1 h2 r
       -> satisfies env0 (ens_ (x~~>a);; ens_ H0;; req (x~~>b \* H2)) h1 h2 r) as H4. admit. apply H4 in H. clear H4. *)

    (* need to know that x~~>b and H0 are disjoint *)

    (* swap req and ens if disjoint *)
    (* ens and req should collapse semantically to a=b? *)
    (* how do pure req and ens differ? condition holds of initial or final heap *)

    assert (
       satisfies env0 (ens_ (x~~>a \* H0);; req (x~~>b \* H2)) h1 h2 r
       -> satisfies env0 ((ens_ (x~~>a);; req (x~~>b));; ens_ H0;; req H2) h1 h2 r) as H4. admit. apply H4 in H. clear H4.
    inverts H.
    destruct H9 as (h3&r1&?&?).

    (* what can i get from an ens and req next to each other? *)
    apply biab_sem in H.

    Check norm_req_req.
    (* rewrite norm_req_req. *)

    inverts H.


    (* Check sat_ens_sep_split. *)
    (* rewrite sat_ens_sep_split in H3. *)
    (* rewrite <- sat_ens_void_sep_combine in H3. *)
    admit.
  }
  { introv H2.
    inverts H2 as H8.
    destr H8.
    felim H2.
    pose proof (ens_ret_unit H); subst.
    fintro.
    intuition. subst.
    unfold ens_ in H.
    assumption. }
Admitted.

(** * Tests *)

Module SemanticsExamples.

  Definition f1 : flow := ens (fun r => \[r=vint 1]).
  Definition f2 : flow := fex (fun x => req (fun h => x = vint 1)).
  Definition f3 : flow := f1 ;; f2.

  Example ex1: satisfies empty_env f1 Fmap.empty Fmap.empty (norm (vint 1)).
  Proof.
    intros.
    unfold f1.
    apply s_ens.
    econstructor. eexists. intuition.
    apply hpure_intro_hempty.
    apply hempty_intro.
    reflexivity.
    fmap_eq.
  Qed.

  Example ex2_ret: flow_res f1 (vint 1).
  Proof.
    unfold flow_res.
    exists empty_heap.
    exists empty_heap.
    exists empty_env.
    unfold f1.
    econstructor. eexists. eexists. intuition.
    apply hpure_intro_hempty.
    apply hempty_intro.
    reflexivity.
    fmap_eq.
  Qed.

  Example ex3_req_ret: flow_res f2 vunit.
  Proof.
    unfold flow_res.
    exists empty_heap.
    exists empty_heap.
    exists empty_env.
    unfold f2.
    apply (s_fex).
    eexists.
    constructor.
    eexists.
    intuition.
    fmap_eq.
    reflexivity.
  Qed.

  Definition f4 : flow := empty ;; fex (fun r => unk "f" (vint 1) r).
  Definition f4_env : env :=
    Fmap.update empty_env "f" (Some (fun _ r => ens (fun r1 => \[r = vint 2]))).

  (* has to be 2 *)
  Example ex5_f_ret: flow_res f4 (vint 2).
  Proof.
    unfold flow_res.
    exists empty_heap. exists empty_heap. exists f4_env.
    unfold f4.
    constructor. exists empty_heap. exists (norm (vint 7)). intuition.
    constructor.
    eexists.
    exists empty_heap.
    intuition.
    apply hpure_intro_hempty.
    apply hempty_intro.
    easy.
    fmap_eq.

    constructor.
    exists (vint 2).
    econstructor.
    unfold f4_env.

    rewrite fmap_read_update.
    reflexivity.
    apply fmap_indom_empty.

    simpl.
    fintro.
    reflexivity.
  Qed.

  Example ex4: forall h,
    satisfies (Fmap.update empty_env "f" (Some (fun x r1 => ens (fun r => \[r1 = r /\ r = x])))) f4 h h (norm (vint 1)).
  Proof.
    intros.
    constructor.
    exists h.
    exists (norm (vint 4)).
    split.

    - constructor.
      eexists.
      exists empty_heap.
      intuition.

      apply hpure_intro_hempty.
      apply hempty_intro.
      easy.
      fmap_eq.

    - eapply s_fex.
      exists (vint 1).
      eapply s_unk.
      rew_fmap.
      reflexivity.

      apply fmap_indom_empty.
      constructor.

      eexists.
      exists empty_heap.
      intuition.
      apply hpure_intro_hempty.
      apply hempty_intro.
      intuition.
      fmap_eq.
  Qed.

  Definition f5 : flow := ens (fun r => \[r = vint 2]).
  Definition f6 : flow := f1 ;; ens (fun r => \[r = vint 2]).

  Example ex6_ent : f5 ⊑ f6.
  Proof.
    unfold entails.
    unfold entails_under.
    unfold f5.
    unfold f6.
    intros.
    inv H.
    destruct H2 as (v & h3 & H1 & H2 & H3 & H4).
    subst r.
    constructor.
    exists h1.
    exists (norm (vint 1)).
    intuition.

    - unfold f1.
      constructor.
      exists (vint 1).
      exists empty_heap.
      intuition.
      apply hpure_intro_hempty.
      apply hempty_intro.
      intuition.
      fmap_eq.
    -
      constructor.
      eexists.
      exists empty_heap.
      intuition.
      apply hpure_intro_hempty.
      apply hempty_intro.
      apply hpure_inv in H2.
      intuition.
      apply hpure_inv in H2.
      intuition.
      fmap_eq.
  Qed.
 
  Example ex7_rewrite : f5 ⊑ f6.
  Proof.
    rewrite ex6_ent.
    apply entails_refl.
  Qed.

  (* lfp interpretation *)
  (*
    forall n res, sum(n, res) =
         n=0/\res=0
      \/ ex n1. ens n=n1/\n1>0; ex r1. sum(n-1,r1); ens res=1+r1
  *)
  Definition sum n res :=
    (* fall (fun n => fall (fun res => *)
    disj
      (ens (fun _ => \[exists n1, n = vint n1 /\ n1 <= 0 /\ res = vint 0]))
      (fex (fun n1 => ens (fun r => \[n = vint n1 /\ n1 > 0]);; fex (fun r1 =>
        (unk "sum" (vint (n1-1)) (vint r1);;
          ens (fun _ => \[res = vint (1 + r1)])))))
          (* )) *)
          .

  Definition sum_env := (Fmap.update empty_env "sum" (Some sum)).
  Definition sum_property (n res:val) := ens (fun _ => \[res = n]).

  (* Close Scope flow_scope. *)

  Lemma ex_sum : forall n1 n res, n1 >= 0 ->
    n = vint n1 ->
    entails_under sum_env (sum n res) (sum_property n res).
  Proof.
    unfold sum_property.
    (* do induction on the numeric value of n *)
    intros n.
    induction_wf IH: (downto 0) n.
    unfold sum.
    intros.
    unfold entails_under.
    intros.
    inverts H1 as H1.
    (* base case *)
    { felim H1. destr H1. subst. inj H2.
      fintro.
      f_equal.
      math. }
    (* recursive case *)
    { felim H1. destruct H1 as (v&H1).
      felim H1. destruct H1 as (h3&r1&H1&H2).

      felim H2. destruct H2 as (v0&H2).
      felim H2. destruct H2 as (h0&r0&H2&H3).
      (* H1: shape of input *)
      (* H2: call to sum *)
      (* H3: shape of res *)


    unfold sum_env in H2.
  (* inverts H2. *)
  (* rewrite fmap_read_update in H1. *)
  (* felim H2. *)
  inverts H2 as H4 Hr.
  rewrite fmap_read_update in H4. inj H4.

      (* felim H2. *)
        (* Check satisfies_fn_in_env. *)
        (* pose proof (@satisfies_fn_in_env _ _ _ _ _ sum _ _ H2) as H4.
        forward H4. rew_fmap. reflexivity.
        apply fmap_indom_empty. easy.
        clear H2.
        fold sum_env in H4. *)

        (* Hr: known call to sum *)

      felim H1. destr H1.
      subst.
      inj H1.

        unfold entails_under in IH.

        specialize (IH (v-1)).
        forward IH. unfold downto. math.
        specialize (IH (vint (v-1)) (vint v0)).
        forward IH. math.
        forward IH. reflexivity.
        specialize (IH _ _ _ Hr).

      felim IH. destr IH. inj H0.
      rewrite one_plus_minus_one_r in H3.
      exact H3.
      apply fmap_indom_empty.
      }
  Qed.

(* TODO *)
Definition foldr :=
  ens (fun _ => \[True]) ;;
  disj
    (unk "f" (vint 2) (vint 3))
    (unk "foldr" (vint 1) (vint 1);;
      unk "f" (vint 2) (vint 1)).

End SemanticsExamples.

(** * Hoare rules *)
(* TODO define semantic triples, then define these as lemmas *)
Inductive forward : expr -> flow -> Prop :=
  | fw_val: forall n,
    forward (pval n) (ens (fun res => \[res = n]))

  (* there is no need for fw_var/a store because substitution will take care of it before it is reached *)

  | fw_let: forall x e1 e2 f1 f2 v,
    forward e1 f1 ->
    flow_res f1 v ->
    forward (subst x v e2) f2 ->
    forward (plet x e1 e2) (f1 ;; f2).

  (* | fw_deref: forall x y,
    forward (pderef x) (fex y (req (pts x y);;
      ens (fun res s h => ((res = s y) //\\ pts x y) s h)))

  | fw_ref: forall x y,
    (* forward (pref x) (fex (fun y => ens (fun r s h => contains y (s x) s h))) *)
    forward (pref x) (fex y (ens (fun r s h => (r = s y) /\ (pts y x s h)))) *)

  (* | fw_get: forall l v, 
    forward (GET l)
      (req (contains l v) ;;
      (ens (fun r => (r = v) //\\ contains l v))) *)

Section ForwardExamples.

  (* let x = 1 in x *)
  Definition e1 := (plet "x" (pval (vint 1)) (pvar "x")).
  Definition f1 :=
    ens (fun v => \[v = vint 1]) ;;
    ens (fun r => \[r = vint 1]).

  Example ex1:
    forward e1 f1.
  Proof.
    eapply fw_let.
    - apply fw_val.
    - unfold flow_res.
      exists empty_heap.
      exists empty_heap.
      exists empty_env.
      constructor.
      intuition.
      eexists.
      eexists.
      eexists.
      auto.
      intuition.
      apply hpure_intro_hempty.
      apply hempty_intro.
      reflexivity.
      fmap_eq.
    - simpl.
      apply fw_val.
  Qed.

End ForwardExamples.