
From Coq Require Import Classes.RelationClasses.
From Coq Require Morphisms Program.Basics.

From SLF Require LibSepFmap.
Module Fmap := LibSepFmap.

Set Warnings "-notation-incompatible-prefix".
From SLF Require Export Extra Heap Tactics.
Set Warnings "notation-incompatible-prefix".

Local Open Scope string_scope.
(* Local Open Scope nat_scope. *)
Local Open Scope Z_scope.
Local Open Scope list_scope.

Set Implicit Arguments.

(** * Programs *)
(** The representation of programs and the use of substitution are mostly reused from SLF. *)
Definition ident : Type := string.
Definition ident_eq := String.string_dec.

Definition loc := nat.

Inductive val :=
  | vunit : val
  | vint : Z -> val
  | vfun : ident -> expr -> val
  | vfix : ident -> ident -> expr -> val
  | vloc : loc -> val
  | vtup : val -> val -> val
  | vstr : string -> val
  | vbool : bool -> val
  | vlist : list val -> val

with expr : Type :=
  | pvar (x: ident)
  | pval (v: val)
  | plet (x: ident) (e1 e2: expr)
  | pfix (f: ident) (x: ident) (e: expr)
  | pfun (x: ident) (e: expr)
  | padd (x y: val)
  | pminus (x y: val)
  | passert (b: val)
  (* | ptup (x y: val) *)
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
  (* | ptup x y => ptup x y *)
  | pvar x => if_y_eq x (pval w) e
  | passert b => passert b
  | pfun x t1 => pfun x (if_y_eq x t1 (aux t1))
  | pfix f x t1 => pfix f x (if_y_eq f t1 (if_y_eq x t1 (aux t1)))
  | pcall t1 t2 => pcall t1 t2
  | plet x t1 t2 => plet x (aux t1) (if_y_eq x t2 (aux t2))
  | pif t0 t1 t2 => pif t0 (aux t1) (aux t2)
  end.

Module Val.
  Definition val := val.
End Val.

(** SLF's heap theory as a functor. *)
Module Export Heap := Heap.HeapSetup(Val).

Definition empty_heap : heap := Fmap.empty.

Definition precond := hprop.
Definition postcond := val -> hprop.

Inductive result : Type :=
  | norm : val -> result.

(** * Staged formulae *)
(** Deeply embedded due to uninterpreted functions, which cannot immediately be given a semantics without an environment. *)
Inductive flow :=
  | req : precond -> flow -> flow
  | ens : postcond -> flow
  | seq : flow -> flow -> flow
  | fex : forall A, (A -> flow) -> flow
  | fall : forall A, (A -> flow) -> flow
  | unk : ident -> val -> val -> flow
  | disj : flow -> flow -> flow.

(** An [ens] which doesn't have a useful return value.*)
Definition ens_ H := ens (fun r => \[r = vunit] \* H).
(** This carries more information than [ens (fun _ => H)], which has an #<i>arbitrary</i># return value. *)

Definition empty := ens_ \[True].

Notation req_ H := (req H empty).

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

Notation "'∀' x1 .. xn , H" :=
  (fall (fun x1 => .. (fall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '∀' '/ '  x1  ..  xn , '/ '  H ']'",
   only printing) : flow_scope.

Notation "f '$' '(' x ',' r ')'" := (unk f x r)
  (at level 80, format "f '$' '(' x ','  r ')'", only printing) : flow_scope.

(* Notation "'ens' '[' r ']' Q" := (ens (fun r => Q))
  (at level 80, format "'ens' '\[' r '\]' Q" , only printing) : flow_scope. *)
(* square brackets will conflict with format notation for boxes https://coq.inria.fr/doc/V8.20.0/refman/user-extensions/syntax-extensions.html#displaying-symbolic-notations:~:text=well%2Dbracketed%20pairs%20of%20tokens%20of%20the%20form%20%27%5B%20%27%20and%20%27%5D%27 *)

Notation "'ens' r '.' Q" := (ens (fun r => Q))
  (at level 80, format "'ens'  r '.'  Q" , only printing) : flow_scope.

(** * Interpretation of a staged formula *)
(** Differs from the paper's definition in:
    
- the addition of an environment, to give interpretations for unknown functions
- the removal of stores, to sidestep impredicativity problems
- the definition of [req], whose variance has been fixed

An [Inductive] definition is used because the rule for unknown functions is not structurally recursive. *)
Inductive satisfies : env -> heap -> heap -> result -> flow -> Prop :=

  | s_req env p (h1 h2:heap) r f
    (H: forall hp hr, (* the heap satisfying p, and the remaining heap *)
      p hp ->
      h1 = Fmap.union hr hp ->
      Fmap.disjoint hr hp ->
      satisfies env hr h2 r f) :
    satisfies env h1 h2 r (req p f)

  | s_ens env q h1 h2 r
    (H: exists v h3,
      r = norm v /\
      q v h3 /\
      h2 = Fmap.union h1 h3 /\
      Fmap.disjoint h1 h3) :
    satisfies env h1 h2 r (ens q)

  | s_seq env f1 f2 h1 h2 r
    (H: exists h3 r1,
      satisfies env h1 h3 r1 f1 /\
      satisfies env h3 h2 r f2) :
    satisfies env h1 h2 r (seq f1 f2)

  | s_fex env h1 h2 r (A:Type) (f:A->flow)
    (H: exists v,
      satisfies env h1 h2 r (f v)) :
    satisfies env h1 h2 r (@fex A f)

  | s_fall env h1 h2 r (A:Type) (f:A->flow)
    (H: forall v,
      satisfies env h1 h2 r (f v)) :
    satisfies env h1 h2 r (@fall A f)

  | s_unk env fn h1 h2 r f x
    (He: Fmap.read env fn = Some f)
    (Hr: satisfies env h1 h2 (norm r) (f x r)) :
    satisfies env h1 h2 (norm r) (unk fn x r)

  | s_disj_l env h1 h2 r f1 f2
    (H: satisfies env h1 h2 r f1) :
    satisfies env h1 h2 r (disj f1 f2)

  | s_disj_r env h1 h2 r f1 f2
    (H: satisfies env h1 h2 r f2) :
    satisfies env h1 h2 r (disj f1 f2).

Notation "env ','  h1 ','  h2 ','  r  '|=' f" :=
  (satisfies env h1 h2 r f) (at level 30, only printing).

(** The result of a staged formula, written in the paper as [Φ[r]]. Because it relates a formula and a value here (and not a variable, as in the paper), we need a model for the formula to talk about the value. *)
Definition flow_res (f:flow) (v:val) : Prop :=
  forall h1 h2 env v1, satisfies env h1 h2 (norm v1) f -> v1 = v.

Definition flow_res_in_env (f:flow) (v:val) env : Prop :=
  forall h1 h2 v1, satisfies env h1 h2 (norm v1) f -> v1 = v.

(** * Entailment *)
(** This is defined directly in terms of the semantics, in contrast to the paper's syntactic definition. *)
(* TODO the paper's definition should later be implemented as an Inductive here and proved sound with respect to the lemmas we can write using this semantic definition *)
Definition entails_under env f1 f2 :=
  forall h1 h2 r,
    satisfies env h1 h2 r f1 -> satisfies env h1 h2 r f2.

Definition entails (f1 f2:flow) : Prop :=
  forall env h1 h2 r, satisfies env h1 h2 r f1 -> satisfies env h1 h2 r f2.

Infix "⊑" := entails (at level 90, right associativity) : flow_scope.

Notation "env '⊢' f1 '⊑' f2" :=
  (entails_under env f1 f2) (at level 90, only printing) : flow_scope.

(* Unset Printing Notations. Set Printing Coercions. Set Printing Parentheses. *)
(* Check (forall f1 f2 f3, f1 ;; f3 ⊑ f2). *)

Definition bientails (f1 f2:flow) : Prop :=
  forall h1 h2 r env,
    satisfies env h1 h2 r f1 <-> satisfies env h1 h2 r f2.

(** * Rewriting *)

Instance entails_refl : Reflexive entails.
Proof.
  unfold Reflexive, entails.
  intros.
  exact H.
Qed.

Instance entails_trans : Transitive entails.
Proof.
  unfold Transitive, entails.
  intros.
  auto.
Qed.

Instance entails_preorder : PreOrder entails.
Proof.
  constructor.
  apply entails_refl.
  apply entails_trans.
Qed.

Instance entails_under_refl : forall env, Reflexive (entails_under env).
Proof.
  unfold Reflexive, entails_under.
  intros.
  exact H.
Qed.

Instance entails_under_trans : forall env, Transitive (entails_under env).
Proof.
  unfold Transitive, entails_under.
  intros.
  auto.
Qed.

Instance entails_under_preorder : forall env, PreOrder (entails_under env).
Proof.
  constructor.
  apply entails_under_refl.
  apply entails_under_trans.
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
  Local Notation flip := Basics.flip.

  (** This reflects how entailment is contravariant in the antecedent and covariant in the consequent *)
  #[global]
  Instance Proper_entails : Proper
    (flip entails ====> entails ====> impl)
    entails.
  Proof.
    unfold entails, Proper, respectful, impl.
    intros.
    auto.
  Qed.

  #[global]
  Instance Proper_entails_under : forall env, Proper
    (flip (entails_under env) ====> entails_under env ====> impl)
    (entails_under env).
  Proof.
    unfold entails_under, Proper, respectful, impl.
    intros.
    auto.
  Qed.

  #[global]
  Instance Proper_bientails : Proper
    (bientails ====> bientails ====> iff)
    entails.
  Proof.
    unfold bientails, entails, Proper, respectful, impl.
    split; intros.
    { apply H0. apply H1. apply H. auto. }
    { apply H0. apply H1. apply H. auto. }
  Qed.

  (** entails is proper wrt satisfies *)
  #[global]
  Instance Proper_satisfies : Proper
    (eq ====> eq ====> eq ====> eq ====> entails ====> impl)
    satisfies.
  Proof.
    unfold entails, Proper, respectful, impl.
    intros. subst.
    auto.
  Qed.

  #[global]
  Instance Proper_satisfies_bi : Proper
    (eq ====> eq ====> eq ====> eq ====> bientails ====> impl)
    satisfies.
  Proof.
    unfold bientails, entails, Proper, respectful, impl.
    intros. subst.
    apply H3.
    auto.
  Qed.

  #[global]
  Instance Proper_satisfies_under : forall env, Proper
    (eq ====> eq ====> eq ====> entails_under env ====> impl)
    (satisfies env).
  Proof.
    unfold entails_under, Proper, respectful, impl.
    intros. subst.
    auto.
  Qed.

  #[global]
  Instance Proper_seq : Proper (entails ====> entails ====> entails) seq.
  Proof.
    unfold Proper, entails, respectful.
    intros.
    inverts H1 as H1; destr H1.
    constructor. exists h3. exists r1.
    eauto.
  Qed.

  #[global]
  Instance Proper_seq_entails_under : forall env,
    Proper (entails_under env ====> entails_under env ====> entails_under env) seq.
  Proof.
    unfold Proper, entails_under, respectful.
    intros.
    inverts H1 as H1; destr H1.
    constructor. exists h3. exists r1.
    split; auto.
  Qed.

  #[global]
  Instance Proper_seq_bi : Proper (bientails ====> bientails ====> bientails) seq.
  Proof.
    unfold Proper, bientails, entails, respectful.
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

(** * Inversion/introduction lemmas *)
Lemma ens_ret_inv : forall env h1 h2 H r,
  satisfies env h1 h2 r (ens_ H) ->
  r = norm vunit.
Proof.
  intros.
  inverts H0 as H0.
  destruct H0 as (v&h3&H1&H2&H3&H4).
  rewrite hstar_hpure_l in H2.
  destruct H2.
  congruence.
Qed.

Lemma req_pure_ret_inv : forall env h1 h2 P r,
  P ->
  satisfies env h1 h2 r (req_ \[P]) ->
  r = norm vunit.
Proof.
  intros.
  inverts H0 as H0.

  forwards: H0 empty_heap h1.
  apply hpure_intro.
  assumption.
  fmap_eq.
  fmap_disjoint.

  inverts H1 as H1. destr H1.
  rewrite hstar_hpure_l in H1.
  destruct H1.
  congruence.
Qed.

Lemma ens_empty_inv : forall env h1 h2 r,
  satisfies env h1 h2 r (ens (fun r => \[])) -> h1 = h2.
Proof.
  intros.
  inverts H as H.
  destr H.
  apply hempty_inv in H.
  subst.
  fmap_eq.
Qed.

Lemma ens_empty_intro : forall env h1 r,
  satisfies env h1 h1 r (ens (fun r => \[])).
Proof.
  intros.
  constructor.
  destruct r.
  exists v.
  exists empty_heap.
  intuition fmap_eq.
  constructor.
Qed.

Lemma ens_pure_inv : forall P env h1 h2 r,
  satisfies env h1 h2 r (ens (fun _ => \[P])) -> P /\ h1 = h2.
Proof.
  intros.
  inverts H as H.
  destr H.
  inverts H.
  inverts H2.
  intuition.
Qed.

Lemma ens_pure_inv_dep : forall P env h1 h2 v,
  satisfies env h1 h2 (norm v) (ens (fun a => \[P a])) ->
  P v /\ h1 = h2.
Proof.
  intros.
  inverts H as H. destr H.
  inverts H.
  inverts H2.
  inj H0.
  intuition.
Qed.

Lemma ens_pure_intro : forall P env h r,
  P -> satisfies env h h r (ens (fun _ => \[P])).
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

Lemma ens_pure_intro_dep : forall P env h r,
  P r -> satisfies env h h (norm r) (ens (fun v => \[P v])).
Proof.
  intros.
  constructor.
  exists r.
  exists empty_heap.
  intuition.
  apply hpure_intro; easy.
  fmap_eq.
Qed.

Lemma ens_void_inv : forall env h1 h2 r H,
  satisfies env h1 h2 r (ens_ H) ->
  r = norm vunit.
Proof.
  unfold empty, ens_.
  intros.
  inverts H0 as H0. destr H0.
  rewrite hstar_hpure_l in H0.
  subst.
  intuition.
  f_equal. assumption.
Qed.

Lemma ens_void_pure_inv : forall P env h1 h2 r,
  satisfies env h1 h2 r (ens_ \[P]) -> P /\ h1 = h2 /\ r = norm vunit.
Proof.
  intros.
  inverts H as H. destr H.
  rewrite hstar_hpure_l in H. destr H.
  apply hpure_inv in H4. destr H4. subst.
  intuition.
Qed.

Lemma ens_void_pure_intro : forall P env h,
  P -> satisfies env h h (norm vunit) (ens_ \[P]).
Proof.
  intros.
  unfold ens_.
  constructor.
  exists vunit.
  exists empty_heap.
  intuition.
  rewrite hstar_hpure_r.
  intuition.
  apply hpure_intro.
  reflexivity.
  fmap_eq.
Qed.

Lemma empty_inv : forall env h1 h2 r,
  satisfies env h1 h2 r empty ->
  h1 = h2 /\ r = norm vunit.
Proof.
  unfold empty.
  intros.
  apply ens_void_pure_inv in H.
  intuition.
Qed.

Lemma empty_intro : forall env h1,
  satisfies env h1 h1 (norm vunit) empty.
Proof.
  intros.
  unfold empty, ens_.
  constructor.
  exists vunit.
  exists empty_heap.
  intuition.
  rewrite hstar_hpure_l.
  intuition.
  apply hpure_intro.
  constructor.
  fmap_eq.
Qed.

Lemma seq_ens_pure_inv : forall P env h1 h2 r f,
  satisfies env h1 h2 r (ens (fun _ => \[P]);; f) ->
  P /\ satisfies env h1 h2 r f.
Proof.
  intros.
  inverts H as H. destr H.
  apply ens_pure_inv in H0. destr H0. subst.
  intuition.
Qed.

Lemma seq_ens_pure_inv_dep : forall P env h1 h2 v f,
  satisfies env h1 h2 (norm v) (ens (fun a => \[P a]);; f) ->
  exists v1, P v1 /\ satisfies env h1 h2 (norm v) f.
Proof.
  intros.
  inverts H as H. destr H.
  destruct r1.
  lets H2: ens_pure_inv_dep P H0.
  exists v0.
  intuition.
  subst.
  intuition.
Qed.

Lemma seq_ens_void_pure_inv : forall P env h1 h2 r f,
  satisfies env h1 h2 r (ens_ \[P];; f) ->
  P /\ satisfies env h1 h2 r f.
Proof.
  intros.
  inverts H as H. destr H.
  apply ens_void_pure_inv in H0. destr H0. subst.
  intuition.
Qed.

(** * Tactics for reasoning about entailments *)
Ltac felim H :=
  match type of H with
  | satisfies _ _ _ _ (fex _) => inverts H as H
  | satisfies _ _ _ _ (_ ;; _) => inverts H as H
  | satisfies _ _ _ _ (ens (fun _ => \[_])) => apply ens_pure_inv in H
  (* | satisfies _ (req \[]) _ _ _ => apply req_empty_inv in H; subst *)
  (* | satisfies _ (unk _ _ _) _ _ _ => inverts H as H *)
  end.

Ltac finv H :=
  match type of H with
  | \[] _ => apply hempty_inv in H
  | \[_] _ => apply hpure_inv in H as (?&?)
  | (_~~>_) _ => apply hsingle_inv in H
  | (_ \* _) _ => apply hstar_inv in H as (?&?&?&?&?&?)
  | (\[_] \* _) _ => rewrite hstar_hpure_l
  | (_ \* \[_]) _ => rewrite hstar_hpure_r
  end.

Ltac fintro :=
  match goal with
  | |- satisfies _ _ _ _ (ens (fun _ => \[_])) => apply ens_pure_intro
  | |- satisfies _ _ _ _ (ens (fun _ => \[])) => apply ens_empty_intro
  | |- \[] _ => apply hempty_intro
  | |- \[_] _ => apply hpure_intro
  | |- (_ \* _) (_ \u _) => apply hstar_intro
  | |- (\[_] \* \[_]) _ => idtac "use rewrite hstar_hpure_l or hstar_hpure_r"
  | |- (\[_] \* _) _ => rewrite hstar_hpure_l
  | |- (_ \* \[_]) _ => rewrite hstar_hpure_r
  (* | |- satisfies _ (req \[]) _ _ _ => apply req_empty_intro *)
  (* | |- satisfies _ (req \[];; _) _ _ _ => apply seq_req_emp_intro_l *)
  end.

  Ltac resolve_fn_in_env :=
    match goal with
    | |- Fmap.read (Fmap.update _ ?k (Some _)) ?k = _ =>
      rewrite fmap_read_update; auto
    | |- Fmap.read (Fmap.single ?k (Some _)) ?k = _ =>
      rewrite Fmap.read_single; reflexivity
    | |- ?g => idtac "resolve_fn_in_env could not solve:"; idtac g
    end.

(* Ltac fexists v :=
  match goal with
  | |- satisfies _ (fex _) _ _ _ => unfold fex; exists v
  end. *)

(** * Entailment/normalization rules *)
(** Covariance of ens *)
Lemma satisfies_ens : forall Q1 Q2 env h1 h2 r,
  (forall v, Q1 v ==> Q2 v) ->
  satisfies env h1 h2 r (ens Q1)->
  satisfies env h1 h2 r (ens Q2).
Proof.
  intros.
  inverts H0 as H3.
  constructor.
  destruct H3 as (v&h3&?&?&?&?).
  exists v.
  exists h3.
  intuition.
  apply H.
  easy.
Qed.

Lemma entails_ens : forall Q1 Q2,
  (forall v, Q1 v ==> Q2 v) -> entails (ens Q1) (ens Q2).
Proof.
  unfold entails.
  intros.
  applys* satisfies_ens.
Qed.

Lemma satisfies_ens_void : forall H1 H2 env h1 h2 r,
  H1 ==> H2 ->
  satisfies env h1 h2 r (ens_ H1) ->
  satisfies env h1 h2 r (ens_ H2).
Proof.
  intros.
  inverts H0 as H3. destruct H3 as (v&h3&?&?&?&?).
  constructor. exists v. exists h3.
  intuition.
  rewrite hstar_hpure_l in H3.
  rewrite hstar_hpure_l.
  intuition.
Qed.

Lemma entails_ens_void : forall H1 H2,
  H1 ==> H2 -> entails (ens_ H1) (ens_ H2).
Proof.
  unfold entails.
  intros.
  applys* satisfies_ens_void H.
Qed.

(** Rule EntEns from the paper *)
Lemma ent_ens_seq : forall H1 H2 f1 f2,
  H1 ==> H2 ->
  entails f1 f2 ->
  entails (ens_ H1;; f1) (ens_ H2;; f2).
Proof.
  unfold entails.
  intros.
  inverts H3 as H3. destr H3.
  apply (satisfies_ens_void H) in H4.
  constructor. exists h3. exists r1.
  intuition.
Qed.

(** Contravariance of req *)
Lemma satisfies_req : forall H1 H2 env h1 h2 r f,
  H2 ==> H1 ->
  satisfies env h1 h2 r (req H1 f) ->
  satisfies env h1 h2 r (req H2 f).
Proof.
  intros.
  inverts H0 as H0.
  apply s_req.
  intros hH1 hr H3.
  (* hH1 is the heap that satisfies H1 *)
  (* hr is the starting heap of the continuation *)
  apply H in H3.
  specialize (H0 _ hr H3).
  intuition.
Qed.

Lemma entails_req : forall H1 H2 f,
  (H2 ==> H1) -> entails (req H1 f) (req H2 f).
Proof.
  unfold entails.
  intros.
  applys* satisfies_req H1.
Qed.

(** Rule EntReq from the paper *)
Lemma ent_req_seq : forall H1 H2 f1 f2,
  H2 ==> H1 ->
  entails f1 f2 ->
  entails (req H1 f1) (req H2 f2).
Proof.
  unfold entails.
  intros.
  constructor. intros hH2 h3. intros.
  inverts H3 as H3. specializes H3 hH2 h3.
Qed.

(** seq is associative *)
Lemma seq_assoc : forall env h1 h2 r f1 f2 f3,
  satisfies env h1 h2 r (f1;; f2;; f3) <->
  satisfies env h1 h2 r ((f1;; f2);; f3).
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
  split; intros; now apply seq_assoc.
Qed.

Lemma unk_inv : forall env h1 h2 r1 x f1 f r,
  Fmap.read env f = Some f1 ->
  satisfies env h1 h2 r (unk f x r1) ->
  satisfies env h1 h2 r (f1 x r1).
Proof.
  intros.
  inverts H0 as H0.
  rewrite H in H0.
  inj H0.
  easy.
Qed.

Lemma norm_unk : forall env f x r1 f1,
  Fmap.read env f = Some f1 ->
  entails_under env (unk f x r1) (f1 x r1).
Proof.
  unfold entails_under.
  intros.
  eapply unk_inv.
  exact H.
  assumption.
Qed.

Lemma norm_forall : forall (A:Type) f1 f2_ctx,
  entails
    (f1;; fall (fun (a:A) => f2_ctx a))
    (fall (fun (a:A) => f1;; f2_ctx a)).
Proof.
  unfold entails.
  intros.
  constructor. intros v.
  inverts H as H. destruct H as (h3&r1&?&?).
  constructor.
  exists h3. exists r1.
  intuition.
  inverts H0 as H0.
  specializes H0 v.
  auto.
Qed.

(** Compaction rule 1 from the paper *)
Lemma norm_ens_false_l : forall f,
  bientails (ens_ \[False]) (ens_ \[False];; f).
Proof.
  unfold bientails.
  iff H.
  { apply ens_void_pure_inv in H.
    intuition. }
  { inverts H as H. destr H.
    apply ens_void_pure_inv in H0.
    intuition. }
Qed.

Lemma norm_ens_false : forall f,
  entails (ens_ \[False]) f.
Proof.
  unfold entails. intros.
  apply ens_void_pure_inv in H.
  intuition.
Qed.

Lemma norm_req_false : forall f f1,
  entails f (req \[False] f1).
Proof.
  unfold entails. intros.
  constructor. intros.
  apply hpure_inv in H0.
  intuition.
Qed.

Lemma norm_req_pure : forall P f,
  P -> entails (req \[P] f) f.
Proof.
  unfold entails. intros.
  inverts H0 as H0.
  specializes H0 empty_heap h1.
  forward H0. fintro. assumption.
  rew_fmap *.
Qed.

(* The converse is not true as the result would change *)
Lemma norm_seq_ens_empty : forall f,
  entails (ens_ \[];; f) f.
Proof.
  unfold entails. intros.
  inverts H as H. destruct H as (h3&r1&?&?).
  inverts H as H.
  destr H.
  rew_heap in H.
  finv H.
  subst.
  rew_fmap *.
Qed.

(** Compaction rule 2 from the paper *)
Lemma norm_empty_l : forall f,
  bientails (empty;; f) f.
Proof.
  unfold bientails, empty.
  iff H.
  { inverts H as H. destr H.
    apply ens_void_pure_inv in H0. destr H0. subst.
    assumption. }
  { constructor.
    exists h1. exists (norm vunit).
    intuition.
    apply ens_void_pure_intro; constructor. }
Qed.

Lemma norm_ens_empty_r : forall H,
  bientails (ens_ H;; empty) (ens_ H).
Proof.
  iff H1.
  { inverts H1 as H1. destr H1.
    apply empty_inv in H2. destr H2. subst.
    pose proof (ens_void_inv H0). subst.
    assumption. }
  { constructor.
    exists h2. exists r.
    intuition.
    apply ens_void_inv in H1.
    subst.
    apply empty_intro. }
Qed.

(** Compaction rule 3 from the paper *)
Lemma norm_empty_r : forall f H,
  bientails (f;; ens_ H;; empty) (f;; ens_ H).
Proof.
  unfold bientails, empty.
  iff H1.
  { rewrite norm_ens_empty_r in H1.
    assumption. }
  { rewrite norm_ens_empty_r.
    assumption. }
Qed.

Lemma norm_seq_req_emp : forall f,
  entails (req \[] f) f.
Proof.
  unfold entails. intros.
  inverts H as H.
  specializes H empty_heap h1 ___. fintro.
Qed.

(** Reassociating req *)
Lemma satisfies_reassoc : forall H f1 f2 env h1 h2 r,
  satisfies env h1 h2 r (req H f1;; f2) ->
  satisfies env h1 h2 r (req H (f1;; f2)).
Proof.
  intros.
  inverts H0 as H0. destr H0.

  (* find out about req *)
  constructor. intros hp hr. intros.

  (* prove the req *)
  inverts H1 as H1.
  specialize (H1 hp hr H0).
  forward H1. fmap_eq.
  forward H1. fmap_disjoint.
  
  constructor.
  exists h3.
  exists r1.
  split; auto.
Qed.

Lemma norm_reassoc : forall H f1 f2,
  entails (req H f1;; f2) (req H (f1;; f2)).
Proof.
  unfold entails.
  apply satisfies_reassoc.
Qed.

(** Splitting and combining [req]s *)
Lemma norm_req_sep_combine : forall H1 H2 f,
  entails (req H1 (req H2 f)) (req (H1 \* H2) f).
Proof.
  unfold entails.
  intros.
  (* contravariance means we start reasoning from the assumptions in the goal *)
  apply s_req.
  intros hb hr. intros.
  apply hstar_inv in H0 as (hH1&hH2&?&?&?&?).

  (* start reasoning forward *)
  inverts H as H.
  forwards: (H hH1 (hr \u hH2) H0).
  fmap_eq.
  fmap_disjoint.

  inverts H8 as H8.
  specialize (H8 _ hr H5).
  forward H8. fmap_eq.
  forward H8. fmap_disjoint.

  assumption.
Qed.

Lemma norm_req_sep_split : forall H1 H2 f,
  entails (req (H1 \* H2) f) (req H1 (req H2 f)).
Proof.
  unfold entails.
  intros.

  apply s_req.
  intros hH1 hH2r. intros.
  apply s_req.
  intros hH2 hr. intros.

  inverts H as H.
  specialize (H (hH1 \u hH2) hr ltac:(apply hstar_intro; auto)).
  forward H. fmap_eq.
  forward H. fmap_disjoint.

  auto.
Qed.

(** Compaction rule 4 from the paper *)
Lemma norm_req_req : forall H1 H2 f,
  bientails (req (H1 \* H2) f) (req H1 (req H2 f)).
Proof.
  intros.
  split.
  - apply norm_req_sep_split.
  - apply norm_req_sep_combine.
Qed.

(** Splitting and combining [ens_]s *)
Lemma satisfies_ens_ens_void : forall H1 H2 env h1 h2 r,
  satisfies env h1 h2 r (ens_ (H1 \* H2)) <->
  satisfies env h1 h2 r (ens_ H1;; ens_ H2).
Proof.
  intros.
  split; intros.
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
  { inverts H as H.
    destruct H as (h3&r1&H3&H4).
    (* give up on careful reasoning *)
    inverts H3 as H5. destr H5. inverts H4 as H8. destr H8.
    rewrite hstar_hpure_l in H0.
    rewrite hstar_hpure_l in H5.
    intuition.
    constructor.
    exists v0.
    exists (h0 \u h4).
    intuition.
    subst.
    rewrite <- hstar_assoc.
    apply hstar_intro.
    rewrite hstar_hpure_l.
    intuition.
    intuition.
    fmap_disjoint.
    fmap_eq. }
Qed.

Lemma norm_ens_ens_void : forall H1 H2,
  bientails (ens_ (H1 \* H2)) (ens_ H1;; ens_ H2).
Proof.
  intros; split; apply satisfies_ens_ens_void.
Qed.

(** Compaction rule 5 from the paper *)
Lemma norm_ens_ens_void_l : forall H Q,
  bientails (ens_ H;; ens Q) (ens (Q \*+ H)).
Proof.
  unfold entails.
  split; intros.
  { inverts H0 as H0. destr H0.
    inverts H1 as H1. destr H1.
    inverts H2 as H2. destr H2.
    constructor.
    exists v0.
    exists (h0 \u h4).
    intuition.
    rewrite hstar_hpure_l in H1.
    rewrite hstar_comm.
    apply hstar_intro; intuition auto.
    fmap_eq. }
  { inverts H0 as H0. destr H0.
    apply hstar_inv in H0. destr H0.
    constructor.
    exists (h1 \u h4).
    exists (norm vunit).
    split.
    { constructor.
      exists vunit.
      exists h4.
      intuition.
      rewrite hstar_hpure_l.
      intuition. }
    { constructor.
      exists v.
      exists h0.
      intuition.
      fmap_eq. } }
Qed.

(** Splitting and combining [ens] with results is more complex, and there does not seem to be a single equivalence. *)
Lemma satisfies_ens_sep_combine : forall Q1 Q2 env h1 h2 r,
  satisfies env h1 h2 r (ens Q1;; ens Q2) ->
  satisfies env h1 h2 r (ens (fun r0 : val => \exists r1 : val, Q1 r1 \* Q2 r0)).
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

Lemma norm_ens_ens_combine : forall Q1 Q2,
  entails (ens Q1;; ens Q2) (ens (fun r => \exists r1, Q1 r1 \* Q2 r)).
Proof.
  unfold entails.
  apply satisfies_ens_sep_combine.
Qed.

Lemma satisfies_ens_sep_split : forall H Q env h1 h2 r,
  satisfies env h1 h2 r (ens (Q \*+ H)) ->
  satisfies env h1 h2 r (ens (fun _ : val => H);; ens Q).
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

Lemma norm_ens_split : forall H Q,
  entails (ens (Q \*+ H)) (ens (fun _ => H);; ens Q).
Proof.
  unfold entails.
  apply satisfies_ens_sep_split.
Qed.

(** * Biabduction *)
(** Simplified definition following #<a href="http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/popl09.pdf">Compositional Shape Analysis by means of Bi-Abduction</a># (Fig 1). *)
Inductive biab : hprop -> hprop -> hprop -> hprop -> Prop :=

  | b_pts_match : forall a b H1 H2 Ha Hf x,
    biab Ha H1 H2 Hf ->
    biab (\[a=b] \* Ha) (x~~>a \* H1) (x~~>b \* H2) Hf

  | b_base_empty : forall Hf,
    biab \[] Hf \[] Hf.

Module BiabductionExamples.

  (** [(a=3) * x->a*y->b |- x->3 * (y->b)] *)
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

End BiabductionExamples.

Lemma biab_sound : forall Ha H1 H2 Hf,
  biab Ha H1 H2 Hf ->
  Ha \* H1 ==> H2 \* Hf.
Proof.
  intros.
  induction H.
  { xsimpl; auto. }
  { xsimpl. }
Qed.

(** Biabduction for a single location. *)
Lemma biab_single : forall x a env h1 h2 r H1 H2 f,
  satisfies env h1 h2 r (ens_ (x~~>a \* H1);; req (x~~>a \* H2) f)->
  satisfies env h1 h2 r (ens_ H1;; req H2 f).
Proof.
  intros.
  inverts H as H. destruct H as (h3&r1&H3&H4).
  (* ens adds a location to the heap *)
  inverts H3 as H3.
  (* use that to figure out what is in h3 *)
  destr H3. finv H0. finv H0. finv H5. subst h3 h0 x0 x1. rew_fmap *.

  (* prove just the first part *)
  rewrite norm_req_req in H4.
  inverts H4 as H4.
  specialize (H4 _ (h1 \u x3) H5).
  forward H4. fmap_eq.
  forward H4. fmap_disjoint.

  constructor.
  exists (h1 \u x3).
  exists r1.
  split.
  { constructor. eexists. exists x3. intuition. exact H. rewrite hstar_hpure_l. intuition. }
  { assumption. }
Qed.

(** The [Float Pre] rule (compaction 6) from the paper. *)
Lemma norm_ens_req_transpose : forall H1 H2 Ha Hf (v:val) f,
  biab Ha (H1 v) H2 (Hf v) ->
  entails (ens_ (H1 v);; (req H2 f))
    (req Ha (ens_ (Hf v);; f)).
Proof.
  unfold entails.
  introv Hbi.
  induction Hbi.

  { intros.
    specialize (IHHbi env0).

    rewrite norm_req_req.
    constructor. intros. finv H3. subst. rew_fmap.

    apply IHHbi.
    apply (biab_single H). }

  { introv H2.
    constructor. intros. finv H. subst hp. rew_fmap *. subst hr. clear H3.
    inverts H2 as H2. destr H2.
    constructor. exists h3. exists r1.
    intuition.

    inverts H2 as H2.
    specialize (H2 empty_heap h3).
    forward H2. fintro.
    forward H2. fmap_eq.
    forward H2. fmap_disjoint.

    assumption. }
Qed.

(** * Examples *)
(** Examples of everything defined so far, which is enough for entailments to be defined and proved. *)
Module Examples.

  Definition f1 : flow := ens (fun r => \[r=vint 1]).
  Definition f2 : flow := fall (fun x => req_ (\[x = vint 1])).
  Definition f3 : flow := f1 ;; f2.

  Example ex1: satisfies empty_env Fmap.empty Fmap.empty (norm (vint 1)) f1.
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
    unfold f1, flow_res.
    intros.
    inverts H as H. destr H.
    inj H0.
    inv H.
    reflexivity.
  Qed.

  Lemma flow_res_inv: forall v v1 f h1 h2 env,
    satisfies env h1 h2 (norm v) f ->
    flow_res f v1 ->
    v = v1.
  Proof.
    unfold flow_res.
    intros.
    specializes H0 H.
    assumption.
  Qed.

  Example ex2_ret1: forall v, flow_res f1 v -> v = vint 1.
  Proof.
    unfold f1, flow_res.
    intros.
    forwards: H empty_heap empty_heap empty_env (vint 1).
    { constructor.
      exists (vint 1). exists empty_heap.
      intuition.
      apply hpure_intro. reflexivity.
      fmap_eq. }
      congruence.
  Qed.

  Example ex3_req_ret: flow_res f2 vunit.
  Proof.
    unfold flow_res, f2.
    intros.
    inverts H as H.
    specializes H (vint 1).
    apply req_pure_ret_inv in H.
    congruence.
    reflexivity.
  Qed.

  Definition f4 : flow := empty;; fall (fun r => unk "f" (vint 1) r).
  Definition f4_env : env :=
    Fmap.update empty_env "f" (Some (fun _ r => ens_ \[r = vint 2])).

  (* has to be 2 *)
  Example ex5_f_ret:
    flow_res_in_env f4 (vint 2) f4_env.
  Proof.
    unfold flow_res_in_env, f4.
    intros.
    rewrite norm_empty_l in H.
    inverts H as H. specializes H v1.
    rewrite (@norm_unk f4_env) in H.
    2: { unfold f4_env. resolve_fn_in_env. }
    simpl in H.
    apply ens_void_pure_inv in H.
    intuition.
  Qed.

  Definition f5 : flow := ens (fun r => \[r = vint 2]).
  Definition f6 : flow := f1 ;; ens (fun r => \[r = vint 2]).

  Example ex6_ent : f5 ⊑ f6.
  Proof.
    unfold entails.
    unfold f5.
    unfold f6.
    intros.
    inverts H as H2.
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

  Example ex1_rewrite : forall H H1 f,
    entails (req (H \* H1) f) (req H (req H1 f)).
  Proof.
    intros.
    rewrite norm_req_req.
    apply entails_refl.
  Qed.

  Example ex3_rewrite : forall H H1 f,
    bientails (req (H \* H1) f) (req H (req H1 f)).
  Proof.
    intros.
    unfold bientails; split.
    { rewrite norm_req_sep_split.
      trivial. }
    { rewrite norm_req_sep_combine.
      apply entails_refl. }
  Qed.

  Example ex2_rewrite : forall H H1 H2 f,
    entails (req (H \* H1) (req H2 f)) (req H (req (H1 \* H2) f)).
  Proof.
    intros.
    rewrite <- norm_req_req.
    rewrite <- norm_req_req.
    rewrite hstar_assoc.
    apply entails_refl.
  Qed.

  (* ensure that this can be done semantically *)
  Example ex1_entail_co_contra : forall x y,
    entails (req \[x>0] (ens_ \[y=1])) (req \[x=1] (ens_ \[y>0])).
  Proof.
    unfold entails.
    intros.
    (* get the condition in the req from the right *)
    constructor.
    intros.
    finv H0.
    (* use it to satisfy the req on the left *)
    inverts H as H.
    specialize (H hp hr).
    forward H. subst hp. fintro. math.
    specialize (H H1 H2).
    (* do the same for ens, but from left to right, as per normal *)
    inverts H as H. destr H. finv H. finv H. finv H6.
    constructor. exists v. exists empty_heap.
    intuition.
    rewrite hstar_hpure_r.
    split. fintro; auto. math.
    fmap_eq.
  Abort.

  Example e1 : forall x,
    satisfies empty_env empty_heap empty_heap (norm vunit) (req_ \[x = 1]).
  Proof.
    intros.
    apply s_req.
    intros.
    apply hpure_inv in H as (?&?).
    intuition fmap_eq.
    constructor.
    eexists.
    eexists.
    intuition.
    rewrite hstar_hpure_l.
    split. auto.
    apply hpure_intro.
    constructor.
    assumption.
  Qed.

  Example e2 : forall x,
    satisfies empty_env (Fmap.single x (vint 1)) (Fmap.single x (vint 1)) (norm vunit) (req (x~~>vint 1) (ens_ (x~~>vint 1))).
  Proof.
    intros.
    apply s_req.
    intros hp H.
    intros.

    apply hsingle_inv in H0. rew_fmap *.

    constructor.
    eexists.
    exists (Fmap.single x (vint 1)).
    intuition.
    { rewrite hstar_hpure_l; split; auto.
    apply hsingle_intro. }
    { subst. assumption. }
  Qed.

  Example e3 : forall x,
    satisfies empty_env empty_heap empty_heap (norm vunit) ((ens_ (x~~>vint 1)) ;; req_ (x~~>vint 1)).
  Proof.
    intros.
    constructor.
    exists (Fmap.single x (vint 1)).
    exists (norm vunit).
    split.
    { constructor.
      exists vunit.
      exists (Fmap.single x (vint 1)).
      intuition.
      rewrite hstar_hpure_l; split; auto.
      apply hsingle_intro.
      fmap_eq. }
    {
      apply s_req.
      intros.
      {
        constructor.
        exists vunit.
        exists empty_heap.
        apply hsingle_inv in H.
        intuition.
        subst.
        rewrite hstar_hpure_l; split; auto.
        apply hpure_intro.
        constructor.
        fmap_eq.
        rewrite <- Fmap.union_empty_l in H0 at 1.
        apply Fmap.union_eq_inv_of_disjoint in H0.
        fmap_eq.
        unfold empty_heap; reflexivity.
        fmap_disjoint.
        fmap_disjoint.
      }
    }
  Qed.

  Example e4_req_false : forall x,
    satisfies empty_env
      (Fmap.single x (vint 1)) (Fmap.single x (vint 2)) (norm vunit)
      (req_ \[False]).
  Proof.
    intros.
    apply s_req.
    intros.
    apply hpure_inv in H.
    destr H.
    inv H0.
    inv H2.
  Qed.

  Example e5_rew : forall x y,
    entails (req (x~~>vint 1) (req_ (y~~>vint 2)))
      (req_ (x~~>vint 1 \* y~~>vint 2)).
  Proof.
    unfold entails.
    intros.

    (* reason backwrds *)
    apply s_req.
    intros.
    (* extract info from what we gained *)
    rew_fmap.
    apply hstar_inv in H0 as (hx&hy&Hx&Hy&?&?).

    (* start going forward *)
    inverts H as H.
    specialize (H _ (hy \u hr) Hx).
    forward H. fmap_eq.
    forward H. fmap_disjoint.

    inverts H as H12.
    specialize (H12 hy hr Hy).
    forward H12. fmap_eq.
    forward H12. fmap_disjoint.

    assumption.
  Qed.

  Definition e6_env : env :=
    Fmap.single "f" (Some (fun y r =>
    match y with
    | vloc x => req (x~~>vint 1) (ens_ (x~~>vint 2))
    | _ => empty
    end)).

  Example e6_fn_reassoc : forall x,
    entails_under e6_env
     (unk "f" (vloc x) vunit;; fall (fun a => req (x~~>vint a) (ens_ (x~~>vint a))))
     (req (x~~>vint 1) (ens_ (x~~>vint 2))).
  Proof.
    (* Set Mangle Names. *)

    unfold entails_under.
    intros x h1 h2 r H.

    (* first reason backward to access the req *)
    constructor. intros hp hr H0 H1 H2. intros.

    (* the function is unknown, so use its definition,
      make it known, then build back up into a sequence *)
    pose proof H as G.
    inverts G as G. destruct G as (h3&r1&Hf&Hr).
    (* resolve the function *)
    unfold e6_env in Hf;
    eapply unk_inv in Hf; only 2: resolve_fn_in_env; simpl;
    fold e6_env in Hf; simpl in Hf.
    pose proof (@s_seq e6_env _ _ h1 h2 r (ex_intro (fun h3 => _) h3 (ex_intro (fun x => _) r1 (conj Hf Hr)))) as G.
    clear Hr. clear Hf.

    (* this is quite inconvenient compared to rewriting, however *)
    rewrites (>> norm_unk e6_env) in H. { unfold e6_env; resolve_fn_in_env. } simpl in H.
    clear G.

    (* reassociate *)
    rewrite norm_reassoc in H.

    (* discharge the req *)
    pose proof (hsingle_inv H0) as H3.
    (* finv H0. *)
    rewrite H1 in H.
    rewrite H3 in H.
    inverts H as H.
    specialize (H hp hr H0).
    forward H. fmap_eq.
    forward H. fmap_disjoint.
    clear H3. clear H0. clear H1. clear H2.

    dup.
    (* a semantic proof *)
    { (* seq *)
      inverts H as H. destruct H as (h0&r2&He&Hr).

      (* assume the ens *)
      inverts He as He. destruct He as (?&h4&?&H3&H4&?).
      rewrite hstar_hpure_l in H3. destruct H3 as [_ H6].
      pose proof (hsingle_inv H6) as H5.
      rewrite H4 in Hr.
      rewrite H5 in Hr.
      clear H4.

      (* existential *)
      inverts Hr as Hr.
      (* destr H4. *)
      specialize (Hr 2).

      (* prove next req *)
      inverts Hr as Hr.
      specialize (Hr h4 hr H6).
      forward Hr. fmap_eq.
      forward Hr. fmap_disjoint.

      auto. }

    (* we can reason at a higher level with rewriting *)

    rewrite norm_forall in H.
    inverts H as H. specialize (H 2).

    rewrites (>> norm_ens_req_transpose) in H.
    { instantiate (1 := fun _ => hempty). simpl.
      rewrite <- (hstar_hempty_r (x ~~> vint 2)).
      apply b_pts_match.
      apply b_base_empty. }

    rew_heap in H.
    rewrite norm_req_pure in H. 2: { reflexivity. }
    rewrite norm_seq_ens_empty in H.
    assumption.
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
      (ens_ \[exists n1, n = vint n1 /\ n1 <= 0 /\ res = vint 0])
      (fex (fun n1 => ens_ \[n = vint n1 /\ n1 > 0];; fex (fun r1 =>
        (unk "sum" (vint (n1-1)) (vint r1);;
          ens_ \[res = vint (1 + r1)]))))
          (* )) *)
          .

  Definition sum_env := (Fmap.update empty_env "sum" (Some sum)).
  Definition sum_property (n res:val) := ens_ \[res = n].

  (* Close Scope flow_scope. *)

  Lemma ex_sum : forall n1 n res, n1 >= 0 ->
    n = vint n1 ->
    entails_under sum_env (sum n res) (sum_property n res).
  Proof.
    unfold sum_property.
    (* do induction on the numeric value of n *)
    intros n.
    induction_wf IH: (downto 0) n.
    unfold sum, entails_under.
    intros.
    inverts H1 as H1.
    (* base case *)
    { apply ens_void_pure_inv in H1. destr H1. subst. inj H2.
      apply ens_void_pure_intro.
      f_equal. math. }
    (* recursive case *)
    { felim H1. destruct H1 as (n1&H1).
      apply seq_ens_void_pure_inv in H1. destruct H1 as ((?&?)&H1).
      felim H1. destruct H1 as (r1&H1).

      rewrites (>> norm_unk sum_env) in H1.
      { unfold sum_env; resolve_fn_in_env. }

      specialize (IH (n1-1)).
      forward IH. assert (n1 = n). congruence. unfold downto. math.
      specialize (IH (vint (n1-1)) (vint r1)).
      forward IH. math.
      forward IH. reflexivity.
      rewrite IH in H1.
      clear IH.

      rewrite <- norm_ens_ens_void in H1.
      rewrite hstar_hpure_conj in H1.
      apply ens_void_pure_inv in H1. destr H1. subst.
      apply ens_void_pure_intro.
      inj H2. inj H1. f_equal. math. }
  Qed.

  Definition foldr : ufun := fun args rr =>
    match args with
    | vtup (vstr f) (vtup (vint a) (vlist l)) =>
      disj
        (ens_ \[rr = vint a /\ l = nil])
        (fex (fun x => fex (fun r => fex (fun l1 =>
          ens_ \[l = cons x l1];;
          unk "foldr" (vtup (vstr f) (vtup (vint a) (vlist l1))) r;;
          unk f (vtup x r) rr))))
    | _ => empty
    end.

  Definition foldr_env := (Fmap.update empty_env "foldr" (Some foldr)).

End Examples.

(** * Big-step semantics *)
Inductive eresult : Type :=
  | enorm : val -> eresult.

Inductive bigstep : heap -> expr -> heap -> eresult -> Prop :=
  | eval_pval : forall h v,
    bigstep h (pval v) h (enorm v)

  (* there is no var rule *)

  | eval_plet : forall h1 h3 h2 x e1 e2 v r,
    bigstep h1 e1 h3 (enorm v) ->
    bigstep h3 (subst x v e2) h2 r ->
    bigstep h1 (plet x e1 e2) h2 r

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
    bigstep h (pcall v1 v2) h r
    
  | eval_pif_true : forall h1 h2 r e1 e2,
    bigstep h1 e1 h2 r ->
    bigstep h1 (pif (vbool true) e1 e2) h2 r

  | eval_pif_false : forall h1 h2 r e1 e2,
    bigstep h1 e2 h2 r ->
    bigstep h1 (pif (vbool false) e1 e2) h2 r.

  (* | eval_pref : forall x s (h:heap) l,
    h l = None ->
    eval[ s, h, pref x ] => [ s, hupdate l (s x) h, enorm l]
  | eval_deref : forall x s (h:heap) v,
    h (s x) = Some v ->
    eval[ s, h, pderef x ] => [ s, h, enorm v]
  | eval_assign : forall x1 x2 s h,
    eval[ s, h, passign x1 x2 ] => [ s, hupdate (s x1) (s x2) h, enorm 0] *)

(* Definition compatible r1 r2 :=
  match (r1, r2) with
  | (norm r3, enorm r4) => r3 = r4
end. *)

(** * Hoare rules *)
Inductive forward : expr -> flow -> Prop :=
  | fw_val: forall n,
    forward (pval n) (ens (fun res => \[res = n]))

  (* there is no need for fw_var/a store because substitution will take care of it before it is reached *)

  | fw_let: forall x e1 e2 f1 f2 v,
    forward e1 f1 ->
    flow_res f1 v ->
    forward (subst x v e2) f2 ->
    forward (plet x e1 e2) (f1 ;; f2)

  | fw_if: forall b e1 e2 f1 f2,
    forward e1 f1 ->
    forward e2 f2 ->
    forward (pif b e1 e2) (disj f1 f2).

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


(** aka what it means for a triple to be vaild. *)
Definition sem_triple (e: expr) (f: flow) : Prop :=
  forall env h1 h2 v,
    bigstep h1 e h2 (enorm v) -> satisfies env h1 h2 (norm v) f.

Lemma sem_pval : forall n,
  sem_triple (pval n) (ens (fun res => \[res = n])).
Proof.
  unfold sem_triple. intros.
  (* appeal to how e executes to tell us about the heaps *)
  inverts H as H.
  (* justify that the staged formula describes the heap *)
  apply ens_pure_intro_dep.
  reflexivity.
Qed.

Lemma sem_plet : forall x e1 e2 f1 f2 v,
  sem_triple e1 f1 ->
  flow_res f1 v ->
  sem_triple (subst x v e2) f2 ->
  sem_triple (plet x e1 e2) (f1;; f2).
Proof.
  intros.
  unfold sem_triple. intros.

  (* reason about how the let executes *)
  inverts H2 as H2.

  (* use the semantic triple we have about e1 *)
  lets H3: H env0 H2. clear H H2. sort.

  (* we need to know that spec value and program value are the same *)
  specializes H0 H3. subst.

  (* know about f2 *)
  specializes H1 env0 h3 h2 v0 H9. clear H9.

  constructor. exists h3. exists (norm v).
  intuition.
Qed.

Lemma sem_pif : forall b e1 e2 f1 f2,
  sem_triple e1 f1 ->
  sem_triple e2 f2 ->
  sem_triple (pif b e1 e2) (disj f1 f2).
Proof.
  introv Ht Hf.
  unfold sem_triple. intros.
  inverts H as H.
  { (* true *)
    unfold sem_triple in Ht.
    specializes Ht env0 H.
    now apply s_disj_l. }
  { (* false *)
    unfold sem_triple in Hf.
    specializes Hf env0 H.
    now apply s_disj_r. }
Qed.

Module Soundness.

  Local Notation derivable := forward.
  Local Notation valid := sem_triple.

  Theorem soundness : forall e f,
    derivable e f -> valid e f.
  Proof.
    introv H.
    induction H.
    - apply sem_pval.
    - apply sem_plet with (v := v); auto.
    - apply sem_pif; auto.
  Qed.
  (* Admitted. *)

End Soundness.

Module ForwardExamples.

  (* let x = 1 in x *)
  Definition e1_let := (plet "x" (pval (vint 1)) (pvar "x")).
  Definition f1 :=
    ens (fun v => \[v = vint 1]) ;;
    ens (fun r => \[r = vint 1]).

  Example ex1:
    forward e1_let f1.
  Proof.
    eapply fw_let.
    - apply fw_val.
    - unfold flow_res.
      intros.
      apply ens_pure_inv_dep in H.
      destruct H.
      exact H.
    - simpl.
      apply fw_val.
  Qed.

End ForwardExamples.
