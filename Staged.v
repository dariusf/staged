
(* From Coq Require Import ZArith Lia Bool List String Program.Equality Classes.RelationClasses. *)
From Coq Require Import Classes.RelationClasses.

Set Implicit Arguments.
From SLF Require Export LibString LibCore.
(* From SLF Require Export LibSepFmap. *)
From SLF Require Export LibSepTLCbuffer LibSepFmap.
Module Fmap := LibSepFmap.
(* From SLF Require Heap. *)
(* From SLF Require Export Heap. *)
(* From SLF Require Export LibSepMinimal. *)

From SLF Require Import Tactics.

(* From CDF Require Import Common Sequences Separation Tactics HeapTactics. *)


Local Open Scope string_scope.
(* Local Open Scope nat_scope. *)
Local Open Scope Z_scope.
Local Open Scope list_scope.


Definition ident : Type := string.
Definition ident_eq := String.string_dec.


(* Definition var := string. *)
(* Definition var_eq := string_dec. *)

(* Definition val := Z. *)
Inductive val :=
  | vint : Z -> val
  | vfun : ident -> expr -> val
  | vfix : ident -> ident -> expr -> val

(* Inductive *)
with
expr : Type :=
  | pvar (x: ident)
  | pval (v: val)
  (* | pconst (n: val) *)
  | plet (x: ident) (e1: expr) (e2: expr)
  | pfix (f: ident) (x: ident) (e: expr)
  | pfun (x: ident) (e: expr)
  (* | pref (x: ident) *)
  (* | pderef (x: ident) *)
  (* | passign (x1: ident) (x2: ident) *)
  | pif (x: val) (e1: expr) (e2: expr)
  | pcall (x: val) (a: val)
  .


Fixpoint subst (y:ident) (w:val) (e:expr) : expr :=
  let aux t := subst y w t in
  let if_y_eq x t1 t2 := if ident_eq x y then t1 else t2 in
  match e with
  | pval v => pval v
  | pvar x => if_y_eq x (pval w) e
  | pfun x t1 => pfun x (if_y_eq x t1 (aux t1))
  | pfix f x t1 => pfix f x (if_y_eq f t1 (if_y_eq x t1 (aux t1)))
  | pcall t1 t2 => pcall t1 t2
  (* | trm_seq t1 t2 => trm_seq (aux t1) (aux t2) *)
  | plet x t1 t2 => plet x (aux t1) (if_y_eq x t2 (aux t2))
  | pif t0 t1 t2 => pif t0 (aux t1) (aux t2)
  end.

Inductive eresult : Type :=
  | enorm : val -> eresult
.

Definition loc : Type := nat.
Definition heap : Type := fmap loc val.



(* Reserved Notation " 'eval[' s ',' h ',' e ']' '=>' '[' s1 ',' h1 ',' r ']' " (at level 50, left associativity). *)

(* Definition store := store Z. *)

(* Inductive bigstep : store -> heap -> expr -> store -> heap -> eresult -> Prop := *)
Inductive bigstep : heap -> expr -> heap -> eresult -> Prop :=
  | eval_pval : forall h v,
    bigstep h (pval v) h (enorm v)

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
    bigstep h (pcall v1 v2) h r

    (* no var rule *)
  (* | eval_pvar : forall s h x v,
    (* Some v = s x -> *)
    bigstep s *)
    (* eval[ s, h, pvar x ]=>[ s, h, enorm v] *)
  (* | eval_pconst : forall s h x,
    eval[ s, h, pconst x ] => [ s, h, enorm x] *)
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

  (* where " 'eval[' s ',' h ',' e ']' '=>' '[' s1 ',' h1 ',' r ']' " := (bigstep s h e s1 h1 r) *)
.

Module ProgramExamples.

  (* Example ex_ref :
    eval[ sempty, hempty, plet "x" (pconst 1) (pref "x") ]=>[ sempty, hupdate 2 1 hempty, enorm 2 ].
  Proof.
    apply eval_plet with (v:=1) (s1:=sempty) (s2:=supdate "x" 1 sempty) (h1:=hempty).
    apply eval_pconst.
    apply eval_pref.
    constructor.
  Qed. *)

End ProgramExamples.

(* copied from LibSepMinimal *)

Implicit Types Q : val->heap->Prop.

(* ================================================================= *)
(** ** Automation for Heap Equality and Heap Disjointness *)

(** For goals asserting equalities between heaps, i.e., of the form [h1 = h2],
    we set up automation so that it performs some tidying: substitution,
    removal of empty heaps, normalization with respect to associativity. *)

#[global] Hint Rewrite union_assoc union_empty_l union_empty_r : fmap.
#[global] Hint Extern 1 (_ = _ :> heap) => subst; autorewrite with fmap.

(** For goals asserting disjointness between heaps, i.e., of the form
    [Fmap.disjoint h1 h2], we set up automation to perform simplifications:
    substitution, exploit distributivity of the disjointness predicate over
    unions of heaps, and exploit disjointness with empty heaps. The tactic
    [jauto_set] used here comes from the TLC library; essentially, it destructs
    conjunctions and existentials. *)

#[global] Hint Resolve Fmap.disjoint_empty_l Fmap.disjoint_empty_r.
#[global] Hint Rewrite disjoint_union_eq_l disjoint_union_eq_r : disjoint.
#[global] Hint Extern 1 (Fmap.disjoint _ _) =>
  subst; autorewrite with rew_disjoint in *; jauto_set.

(* ################################################################# *)
(** * Heap Predicates and Entailment *)

(* ================================================================= *)
(** ** Extensionality Axioms *)

(** Extensionality axioms are essential to assert equalities between heap
    predicates of type [hprop], and between postconditions, of type
    [val->hprop]. *)

Axiom functional_extensionality : forall A B (f g:A->B),
  (forall x, f x = g x) ->
  f = g.

Axiom propositional_extensionality : forall (P Q:Prop),
  (P <-> Q) ->
  P = Q.

(* ================================================================= *)
(** ** Core Heap Predicates *)

(** The type of heap predicates is named [hprop]. *)

Definition hprop := heap -> Prop.

(** We bind a few more meta-variables. *)

Implicit Types P : Prop.
Implicit Types H : hprop.

(** Core heap predicates, and their associated notations:

    - [\[]] denotes the empty heap predicate
    - [\[P]] denotes a pure fact
    - [p ~~> v] denotes a singleton heap
    - [H1 \* H2] denotes the separating conjunction
    - [Q1 \*+ H2] denotes the separating conjunction extending a postcondition
    - [\exists x, H] denotes an existential
    - [\forall x, H] denotes a universal. *)

Definition hempty : hprop :=
  fun h => (h = Fmap.empty).

Definition hsingle (p:loc) (v:val) : hprop :=
  fun h => (h = Fmap.single p v).

Definition hstar (H1 H2 : hprop) : hprop :=
  fun h => exists h1 h2, H1 h1
                              /\ H2 h2
                              /\ Fmap.disjoint h1 h2
                              /\ h = Fmap.union h1 h2.

Definition hexists A (J:A->hprop) : hprop :=
  fun h => exists x, J x h.

Definition hforall (A : Type) (J : A -> hprop) : hprop :=
  fun h => forall x, J x h.

Definition hpure (P:Prop) : hprop := (* encoded as [\exists (p:P), \[]] *)
  hexists (fun (p:P) => hempty).

Declare Scope hprop_scope.

Notation "\[]" := (hempty)
  (at level 0) : hprop_scope.

Notation "\[ P ]" := (hpure P)
  (at level 0, format "\[ P ]") : hprop_scope.

Notation "p '~~>' v" := (hsingle p v) (at level 32) : hprop_scope.

Notation "H1 '\*' H2" := (hstar H1 H2)
  (at level 41, right associativity) : hprop_scope.

Notation "Q \*+ H" := (fun x => hstar (Q x) H)
  (at level 40) : hprop_scope.

Notation "'\exists' x1 .. xn , H" :=
  (hexists (fun x1 => .. (hexists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\exists' '/ '  x1  ..  xn , '/ '  H ']'") : hprop_scope.

Notation "'\forall' x1 .. xn , H" :=
  (hforall (fun x1 => .. (hforall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\forall' '/ '  x1  ..  xn , '/ '  H ']'") : hprop_scope.

(* ================================================================= *)
(** ** Entailment *)

Declare Scope hprop_scope.
Open Scope hprop_scope.

(** Entailment for heap predicates, written [H1 ==> H2]. *)

Definition himpl (H1 H2:hprop) : Prop :=
  forall h, H1 h -> H2 h.

Notation "H1 ==> H2" := (himpl H1 H2) (at level 55) : hprop_scope.

(** Entailment between postconditions, written [Q1 ===> Q2] *)

Definition qimpl A (Q1 Q2:A->hprop) : Prop :=
  forall (v:A), Q1 v ==> Q2 v.

Notation "Q1 ===> Q2" := (qimpl Q1 Q2) (at level 55) : hprop_scope.

(** Entailment defines an order on heap predicates *)

Lemma himpl_refl : forall H,
  H ==> H.
Proof. introv M. auto. Qed.

Lemma himpl_trans : forall H2 H1 H3,
  (H1 ==> H2) ->
  (H2 ==> H3) ->
  (H1 ==> H3).
Proof. introv M1 M2. unfolds* himpl. Qed.

Lemma himpl_antisym : forall H1 H2,
  (H1 ==> H2) ->
  (H2 ==> H1) ->
  (H1 = H2).
Proof. introv M1 M2. applys pred_ext_1. intros h. iff*. Qed.

Lemma qimpl_refl : forall Q,
  Q ===> Q.
Proof. intros Q v. applys himpl_refl. Qed.

#[global] Hint Resolve himpl_refl qimpl_refl.

(* ================================================================= *)
(** ** Properties of [hstar] *)

Lemma hstar_intro : forall H1 H2 h1 h2,
  H1 h1 ->
  H2 h2 ->
  Fmap.disjoint h1 h2 ->
  (H1 \* H2) (Fmap.union h1 h2).
Proof. intros. exists* h1 h2. Qed.

Lemma hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.
Proof.
  unfold hprop, hstar. intros H1 H2. applys himpl_antisym.
  { intros h (h1&h2&M1&M2&D&U).
    rewrite* Fmap.union_comm_of_disjoint in U. exists* h2 h1. }
  { intros h (h1&h2&M1&M2&D&U).
    rewrite* Fmap.union_comm_of_disjoint in U. exists* h2 h1. }
Qed.

Lemma hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).
Proof.
  intros H1 H2 H3. applys himpl_antisym; intros h.
  { intros (h'&h3&(h1&h2&M3&M4&D'&U')&M2&D&U). subst h'.
    exists h1 (h2 \+ h3). splits*. { applys* hstar_intro. } }
  { intros (h1&h'&M1&(h2&h3&M3&M4&D'&U')&D&U). subst h'.
    exists (h1 \+ h2) h3. splits*. { applys* hstar_intro. } }
Qed.

Lemma hstar_hempty_l : forall H,
  \[] \* H = H.
Proof.
  intros. applys himpl_antisym; intros h.
  { intros (h1&h2&M1&M2&D&U). hnf in M1. subst. rewrite* Fmap.union_empty_l. }
  { intros M. exists (@Fmap.empty loc val) h. splits*. { hnfs*. } }
Qed.

Lemma hstar_hexists : forall A (J:A->hprop) H,
  (hexists J) \* H = hexists (fun x => (J x) \* H).
Proof.
  intros. applys himpl_antisym; intros h.
  { intros (h1&h2&(x&M1)&M2&D&U). exists* x h1 h2. }
  { intros (x&(h1&h2&M1&M2&D&U)). exists h1 h2. splits*. { exists* x. } }
Qed.

Lemma hstar_hforall : forall H A (J:A->hprop),
  (hforall J) \* H ==> hforall (J \*+ H).
Proof.
  intros. intros h M. destruct M as (h1&h2&M1&M2&D&U). intros x. exists* h1 h2.
Qed.

Lemma himpl_frame_l : forall H2 H1 H1',
  H1 ==> H1' ->
  (H1 \* H2) ==> (H1' \* H2).
Proof. introv W (h1&h2&?). exists* h1 h2. Qed.

(** Additional, symmetric results, useful for tactics *)

Lemma hstar_hempty_r : forall H,
  H \* \[] = H.
Proof.
  applys neutral_r_of_comm_neutral_l. applys* hstar_comm. applys* hstar_hempty_l.
Qed.

Lemma himpl_frame_r : forall H1 H2 H2',
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1 \* H2').
Proof.
  introv M. do 2 rewrite (@hstar_comm H1). applys* himpl_frame_l.
Qed.

(* ================================================================= *)
(** ** Properties of [hpure] *)

Lemma hstar_hpure_l : forall P H h,
  (\[P] \* H) h = (P /\ H h).
Proof.
  intros. apply prop_ext. unfold hpure.
  rewrite hstar_hexists. rewrite* hstar_hempty_l.
  iff (p&M) (p&M). { split*. } { exists* p. }
Qed.

Lemma himpl_hstar_hpure_r : forall P H H',
  P ->
  (H ==> H') ->
  H ==> (\[P] \* H').
Proof. introv HP W. intros h K. rewrite* hstar_hpure_l. Qed.

Lemma himpl_hstar_hpure_l : forall P H H',
  (P -> H ==> H') ->
  (\[P] \* H) ==> H'.
Proof. introv W Hh. rewrite hstar_hpure_l in Hh. applys* W. Qed.

(* ================================================================= *)
(** ** Properties of [hexists] *)

Lemma himpl_hexists_l : forall A H (J:A->hprop),
  (forall x, J x ==> H) ->
  (hexists J) ==> H.
Proof. introv W. intros h (x&Hh). applys* W. Qed.

Lemma himpl_hexists_r : forall A (x:A) H J,
  (H ==> J x) ->
  H ==> (hexists J).
Proof. introv W. intros h. exists x. apply* W. Qed.

Lemma himpl_hexists : forall A (J1 J2:A->hprop),
  J1 ===> J2 ->
  hexists J1 ==> hexists J2.
Proof.
  introv W. applys himpl_hexists_l. intros x. applys himpl_hexists_r W.
Qed.

(* ================================================================= *)
(** ** Properties of [hforall] *)

Lemma himpl_hforall_r : forall A (J:A->hprop) H,
  (forall x, H ==> J x) ->
  H ==> (hforall J).
Proof. introv M. intros h Hh x. apply* M. Qed.

Lemma himpl_hforall_l : forall A x (J:A->hprop) H,
  (J x ==> H) ->
  (hforall J) ==> H.
Proof. introv M. intros h Hh. apply* M. Qed.

Lemma himpl_hforall : forall A (J1 J2:A->hprop),
  J1 ===> J2 ->
  hforall J1 ==> hforall J2.
Proof.
  introv W. applys himpl_hforall_r. intros x. applys himpl_hforall_l W.
Qed.

(* ================================================================= *)
(** ** Properties of [hsingle] *)

Lemma hstar_hsingle_same_loc : forall p v1 v2,
  (p ~~> v1) \* (p ~~> v2) ==> \[False].
Proof.
  intros. unfold hsingle. intros h (h1&h2&E1&E2&D&E). false.
  subst. applys* Fmap.disjoint_single_single_same_inv.
Qed.

(* ================================================================= *)
(** ** Basic Tactics for Simplifying Entailments *)

(** [xsimpl] performs immediate simplifications on entailment relations. *)

#[global] Hint Rewrite hstar_assoc hstar_hempty_l hstar_hempty_r : hstar.

Tactic Notation "xsimpl" :=
  try solve [ apply qimpl_refl ];
  try match goal with |- _ ===> _ => intros ? end;
  autorewrite with hstar; repeat match goal with
  | |- ?H \* _ ==> ?H \* _ => apply himpl_frame_r
  | |- _ \* ?H ==> _ \* ?H => apply himpl_frame_l
  | |- _ \* ?H ==> ?H \* _ => rewrite hstar_comm; apply himpl_frame_r
  | |- ?H \* _ ==> _ \* ?H => rewrite hstar_comm; apply himpl_frame_l
  | |- ?H ==> ?H => apply himpl_refl
  | |- ?H ==> ?H' => is_evar H'; apply himpl_refl end.

Tactic Notation "xsimpl" "*" := xsimpl; auto_star.

(** [xchange] helps rewriting in entailments. *)

Lemma xchange_lemma : forall H1 H1',
  H1 ==> H1' -> forall H H' H2,
  H ==> H1 \* H2 ->
  H1' \* H2 ==> H' ->
  H ==> H'.
Proof.
  introv M1 M2 M3. applys himpl_trans M2. applys himpl_trans M3.
  applys himpl_frame_l. applys M1.
Qed.

Tactic Notation "xchange" constr(M) :=
  forwards_nounfold_then M ltac:(fun K =>
    eapply xchange_lemma; [ eapply K | xsimpl | ]).

(* end LibSepMinimal *)

Definition precond := hprop.
Definition postcond := val -> hprop.
(* Definition env := val -> flow. *)

Inductive result : Type :=
  | norm : val -> result.

  Definition compatible r1 r2 :=
    match (r1, r2) with
    | (norm r3, enorm r4) => r3 = r4
  end.

Inductive flow :=
| req : precond -> flow
| ens : postcond -> flow
| seq : flow -> flow -> flow
(* | ffex : forall (A:Type), (A -> flow) -> flow *)
| ffex : (val -> flow) -> flow
| unk : ident -> val -> val -> flow (* f(x, r) *)
| disj : flow -> flow -> flow
.

Infix ";;" := seq (at level 80, right associativity).

(* Definition fex {A:Type} (f:A -> flow) : flow :=
  ffex A f. *)

Definition fex (f:val -> flow) : flow :=
  ffex f.


(* Fixpoint satisfies (env:env) (f:flow) (h1 h2:heap) (r:result) : Prop :=
  match f with
  | req p => exists h3, h1 = hunion h2 h3 /\ hdisjoint h2 h3 /\ p h3
  | ens q => exists v h3, r = norm v /\ q v h3 /\ h2 = hunion h1 h3 /\ hdisjoint h1 h3
  | seq f1 f2 => exists h3 r1, satisfies env f1 h1 h3 r1 /\ satisfies env f2 h3 h2 r
  | ffex a f => exists v, satisfies env (f v) h1 h2 r
  | unk f => satisfies env (env f) h1 h2 r
  end
  . *)

Definition ufun := val -> val -> flow.
Definition env := ident -> option ufun.

Inductive satisfies : env -> flow -> heap -> heap -> result -> Prop :=

  | s_req : forall env p h1 h2 r,
    (exists h3, h1 = Fmap.union h2 h3 /\ Fmap.disjoint h2 h3 /\ p h3) ->
    satisfies env (req p) h1 h2 r

  | s_ens : forall env q h1 h2 r,
    (exists v h3, r = norm v /\ q v h3 /\ h2 = Fmap.union h1 h3 /\ Fmap.disjoint h1 h3) ->
    satisfies env (ens q) h1 h2 r

  | s_seq : forall env f1 f2 h1 h2 r,
    (exists h3 r1, satisfies env f1 h1 h3 r1 /\ satisfies env f2 h3 h2 r) -> satisfies env (seq f1 f2) h1 h2 r

  (* | s_ffex (a:Type) (f:a->flow) : forall env h1 h2 r x, *)
  | s_ffex : forall env f h1 h2 r,
    (exists v, satisfies env (f v) h1 h2 r) ->
    satisfies env (ffex f) h1 h2 r

  | s_unk : forall env fn h1 h2 r f x,
    env fn = Some f ->
    satisfies env (f x r) h1 h2 (norm r) ->
    satisfies env (unk fn x r) h1 h2 (norm r)

  | s_disj_l : forall env h1 h2 r f1 f2,
    satisfies env f1 h1 h2 r ->
    satisfies env (disj f1 f2) h1 h2 r

  | s_disj_r : forall env h1 h2 r f1 f2,
    satisfies env f2 h1 h2 r ->
    satisfies env (disj f1 f2) h1 h2 r

  .

Definition entails (f1 f2:flow) : Prop :=
  forall h1 h2 r env,
    satisfies env f1 h1 h2 r -> satisfies env f2 h1 h2 r.

Infix "⊑" := entails (at level 90, right associativity
  , only parsing
  ).

(* Unset Printing Notations. Set Printing Coercions. Set Printing Parentheses. *)
(* Check (forall f1 f2 f3, f1 ;; f3 ⊑ f2). *)

Instance entails_refl : Reflexive entails.
Proof.
  unfold Reflexive.
  unfold entails. intros.
  exact H.
Qed.

Instance entails_trans : Transitive entails.
Proof.
  unfold Transitive.
  intros.
  unfold entails in *.
  intros.
  apply H0.
  apply H.
  apply H1.
Qed.

Definition bientails (f1 f2:flow) : Prop :=
  forall h1 h2 r env,
    satisfies env f1 h1 h2 r <-> satisfies env f2 h1 h2 r.

Lemma req_sep_combine : forall H1 H2,
  entails (req H1;; req H2) (req (H1 \* H2)).
Proof.
  unfold entails.
  intros.
  inv H.
  destruct H6 as (h3 & r1 & H1 & H2).
  (* h3 is the heap after taking away the part satisfying P *)
  
  inv H1.
  inv H2.
  destruct H3 as (h4 & ? & ? & ?).
  destruct H1 as (h5 & ? & ? & ?).
  (* h4 is the part satisfying P, same for h5/Q *)
  constructor.
  (* union h4/h5 to get the part satisfying P*Q *)
  (* TODO *)
  assert (hdisjoint h4 h5).
  (* Search hdisjoint. *)
  (* Search hunion. *)
  (* Search (hunion ?a _ = hunion ?a _). *)
  subst h3.
  rewrite hdisjoint_union_l in H0.
  destruct H0.
  rewrite hdisjoint_sym in H1.
  easy.

  exists (hunion h4 h5).
  intuition.
  subst h3.
  rewrite hunion_assoc in H.
  rewrite H.
  (* rewrite <- hunion_invert_r. *)
  assert (hunion h4 h5 = hunion h5 h4). rewrite hunion_comm. reflexivity.
  apply hdisjoint_sym.
  easy.
  
  rewrite H1.
  reflexivity.

  
  rewrite hdisjoint_union_r.

  intuition.

  subst h3.
  rewrite hdisjoint_union_l in H0.
  intuition.

  unfold sepconj.
  exists h4. exists h5.

  intuition.

  (* unfold bientails. *)
  (* split. *)
  (* intros. *)
  (* h1 is initial heap *)
  (* h2 is final *)
  (* h3 is the part taken off by P * Q *)
  (* { inv H. destruct H2 as (h3 & H1 & H2 & H3).
    constructor.
    admit. } *)
  (* { admit. } *)
Qed.

(* Lemma req_sep : forall P Q,
  bientails (req (P ** Q)) (req P;; req Q).
Proof.
  intros.
  unfold bientails.
  split.
  intros.
  (* h1 is initial heap *)
  (* h2 is final *)
  (* h3 is the part taken off by P * Q *)
  { inv H. destruct H2 as (h3 & H1 & H2 & H3).
    constructor.
    admit. }
  { admit. }
Qed. *)

Definition flow_res (f:flow) (v:val) : Prop :=
  exists h1 h2 env, satisfies env f h1 h2 (norm v).

(* Definition replace_ret (v:val) (f:flow) : flow :=
  f ;; ens (fun r => pure (r = v)). *)

Definition empty := ens (fun r => pure True).

Definition empty_env : env := fun _ => None.

Definition eupdate (x: ident) (v: ufun) (s: env) : env :=
  fun y => if string_dec x y then Some v else s y.


  Lemma eupdate_same: forall env v l,
    (eupdate l v env) l = Some v.
  Proof.
    intros; cbn.
    unfold eupdate.
    destruct (string_dec l l); congruence.
  Qed.


(* For reasoning forward from flows in the context *)
(* Ltac felim :=
  match goal with
  | H : seq _ _ _ _ _ _ _ |- _ => unfold seq in H; destr H
  | H : req _ _ _ _ _ _ |- _ => unfold req in H; destr H; subst
  | H : ens _ _ _ _ _ _ |- _ => unfold ens in H; destr H; subst
  | H : pureconj _ _ _ _ |- _ => unfold pureconj in H; destr H; subst
  end. *)

(* Ltac fintro :=
  match goal with
  (* | |- ens _ _ _ (norm ?v) => unfold ens; do 2 eexists; intuition *)
  | |- satisfies (ens _) _ _ _ (norm ?v) => econstructor; eexists; intuition
  | |- pure _ _ => unfold pure; intuition
  end.

Ltac fexists v :=
  match goal with
  | |- fex _ _ _ _ => unfold fex; exists v
  end. *)

(* Ltac fsteps :=
  match goal with
  | H : seq _ _ _ _ _ _ _ |- _ => felim; fsteps
  | H : req _ _ _ _ _ _ |- _ => felim; fsteps
  | H : ens _ _ _ _ _ _ |- _ => felim; fsteps
  | H : pureconj _ _ _ _ |- _ => felim; fsteps
  | _ => idtac
  end. *)

(* Definition satisfies s1 h1 s2 h2 r (f:flow) := f s1 h1 s2 h2 r. *)

(* Lemma empty_noop : forall s h r,
  empty s h s h (norm r).
Proof.
  intros.
  unfold empty.
  unfold ens.
  intuition.
  exists r.
  intuition.
  exists hempty.
  intuition heap.
  unfold pure.
  intuition.
Qed. *)


(* solve a heap goal.
  termination is guaranteed by ordering of lemmas to use *)
Ltac hstep :=
  match goal with
  (* | [ H: _ = hunion hempty _ |- _ ] =>
      rewrite hunion_empty in H
  | [ H: _ = hunion _ hempty |- _ ] =>
      rewrite hunion_comm in H;
      rewrite hunion_empty in H *)
  | [ |- ?h = hunion hempty ?h ] =>
      rewrite hunion_empty; reflexivity
  | [ |- ?h = hunion ?h hempty ] =>
      rewrite hunion_comm; hstep
  | [ |- hdisjoint hempty _ ] =>
      apply hdisjoint_empty
  | [ |- hdisjoint _ hempty ] =>
      rewrite hdisjoint_sym; hstep
  (* | [ |- hunion hempty _ = _ ] =>
      rewrite hunion_empty
  | [ |- _ = hunion _ hempty ] =>
      rewrite hunion_comm; rewrite hunion_empty
  | [ |- hunion _ hempty = _ ] =>
      rewrite hunion_comm;
      rewrite hunion_empty *)
  (* | [ |- ?g ] => idtac *)
  end.


Module SemanticsExamples.

  Definition f1 : flow := ens (fun r => pure (r=vint 1)).
  Definition f2 : flow := fex (fun x => req (fun h => x = vint 1)).
  Definition f3 : flow := f1 ;; f2.

  Example ex1: forall h, satisfies empty_env f1 h h (norm (vint 1)).
  Proof.
    intros.
    unfold f1.
    (* fintro. *)
    apply s_ens.
    econstructor. eexists. intuition.
    (* fintro. *)
    unfold pure. intuition.
    rewrite hunion_comm.
    rewrite hunion_empty.
    reflexivity.
    apply hdisjoint_empty.
    rewrite hdisjoint_sym.
    apply hdisjoint_empty.
    (* hstep. *)
    (* hstep. *)
  Qed.

  Example ex2_ret: flow_res f1 (vint 1).
  Proof.
    unfold flow_res.
    exists hempty. exists hempty.
    exists empty_env.
    unfold f1.
    (* fintro. *)
    econstructor. eexists. eexists. intuition.
    (* fintro. *)
    unfold pure. intuition.
    hstep.
    hstep.
  Qed.

  Example ex3_req_ret: flow_res f2 (vint 2).
  Proof.
    unfold flow_res.
    exists hempty.
    exists hempty.
    exists empty_env.
    unfold f2.
    (* eexists. *)
    (* fexists (vint 1). *)
    (* unfold req. *)
    apply (s_ffex).
    eexists.
    constructor.
    eexists.
    (* exists hempty. *)
    intuition.
    rewrite hunion_empty.
    auto.
    apply hdisjoint_empty.
    (* hstep. *)
    (* hstep. *)
  Qed.

  Definition f4 : flow := empty ;; fex (fun r => unk "f" (vint 1) r).
  Definition f4_env : env := eupdate "f" (fun _ r => ens (fun r1 => pure (r = vint 2))) empty_env.

  (* has to be 2 *)
  Example ex5_f_ret: flow_res f4 (vint 2).
  Proof.
    unfold flow_res.
    exists hempty. exists hempty. exists f4_env.
    unfold f4.
    (* fintro. *)
    constructor. exists hempty. exists (norm (vint 7)). intuition.
    (* fintro. *)
    constructor.
    eexists.
    exists hempty.
    unfold pure. intuition.
    hstep.
    hstep.
    constructor.
    exists (vint 2).
    econstructor.
    unfold f4_env.
    apply eupdate_same.
    constructor.
    exists (vint 2).
    exists hempty.
    intuition.
    unfold pure.
    intuition.
    hstep.
    hstep.
  Qed.

  Example ex4: forall h, satisfies (eupdate "f" (fun x r1 => ens (fun r => pure (r1 = r /\ r = x))) empty_env) f4 h h (norm (vint 1)).
  Proof.
    intros.
    constructor.
    exists h.
    exists (norm (vint 4)).
    split.
    - constructor.
    eexists.
    exists hempty.
    intuition.
    unfold pure. intuition.
    hstep.
    hstep.
    -
    eapply s_ffex.
    exists (vint 1).
    eapply s_unk.
    (* with (fl := (fun _ _ => ens (fun x : val => pure (x = vint 1)))). *)
    (* Check eupdate_same. *)
    (* rewrite eupdate_same. *)
    eapply eupdate_same.
    (* auto. *)

    constructor.
    eexists.
    exists hempty.
    intuition.
    unfold pure.
    intuition.
    hstep.
    hstep.
  Qed.

  Definition f5 : flow := ens (fun r => pure (r = vint 2)).
  Definition f6 : flow := f1 ;; ens (fun r => pure (r = vint 2)).

  Example ex6_ent : f5 ⊑ f6.
  Proof.
    unfold entails.
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
      exists hempty.
      intuition.
      unfold pure.
      intuition.
      hstep.
      hstep.

    -
      constructor.
      eexists.
      exists hempty.
      intuition.
      unfold pure.
      intuition.
      unfold pure in H2.
      intuition auto.
      unfold pure in H2.
      destruct H2.
      subst.
      auto.
      hstep.
  Qed.
 
  Example ex7_rewrite : f5 ⊑ f6.
  Proof.
    rewrite ex6_ent.
    apply entails_refl.
  Qed.

  Definition foldr :=
  ens (fun _ => pure True) ;;
  disj
    (unk "f" (vint 2) (vint 3))
    (unk "foldr" (vint 1) (vint 1);;
      unk "f" (vint 2) (vint 1))
  .

End SemanticsExamples.


(** * Hoare rules *)

(* forward rules say how to produce a staged formula from a program *)
Inductive forward : expr -> flow -> Prop :=
  | fw_val: forall n,
    forward (pval n) (ens (fun res => pure (res = n)))

  (* there is no need for fw_var/a store because substitution will take care of it before it is reached *)

  | fw_let: forall x e1 e2 f1 f2 v,
    forward e1 f1 ->
    flow_res f1 v ->
    forward (subst x v e2) f2 ->
    forward (plet x e1 e2) (f1 ;; f2)

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
.

Section ForwardExamples.

  (* let x = 1 in x *)
  Definition e1 := (plet "x" (pval (vint 1)) (pvar "x")).
  Definition f1 :=
    ens (fun v => pure (v = vint 1)) ;;
    ens (fun r => pure (r = vint 1)).

  Example ex1:
    forward e1 f1.
  Proof.
    eapply fw_let.
    - apply fw_val.
    - unfold flow_res.
      exists hempty.
      exists hempty.
      exists empty_env.
      constructor.
      intuition.
      eexists.
      eexists.
      eexists.
      auto.
      unfold pure. intuition.
      rewrite hunion_empty.
      reflexivity.
      apply hdisjoint_empty.
      (* fintro.
      fintro.
      hstep.
      hstep. *)
    - simpl.
      apply fw_val.
  Qed.

End ForwardExamples.