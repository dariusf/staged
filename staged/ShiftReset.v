From Coq Require Import Classes.RelationClasses.
From Coq Require Morphisms Program.Basics.

From Staged Require Export HeapF.
From Staged Require Export LibFmap.
From Staged Require Export ExtraTactics.

Local Open Scope string_scope.
(* Local Open Scope nat_scope. *)
Local Open Scope Z_scope.
Local Open Scope list_scope.

Set Implicit Arguments.

(** * Programs *)
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
  | vfptr : var -> val

with expr : Type :=
  | pvar (x: var)
  | pval (v: val)
  | plet (x: var) (e1 e2: expr)
  | pfix (f: var) (x: var) (e: expr)
  | pfun (x: var) (e: expr)
  | padd (x y: expr)
  | pfst (t: expr)
  | psnd (t: expr)
  | pminus (x y: expr)
  | passert (b: val)
  | pref (v: val)
  | pderef (v: val)
  | passign (x: val) (v: val)
  | pif (x: val) (e1: expr) (e2: expr)
  | papp (x: expr) (a: expr)
  | pshift (k: expr) (e: expr)
  | preset (e: expr).

#[global]
Instance Inhab_val : Inhab val.
Proof.
  constructor.
  exists vunit.
  constructor.
Qed.

Fixpoint subst (y:var) (w:val) (e:expr) : expr :=
  let aux t := subst y w t in
  let if_y_eq x t1 t2 := if var_eq x y then t1 else t2 in
  match e with
  | pval v => pval v
  | padd x y => padd x y
  | pminus x y => pminus x y
  | pfst x => pfst x
  | psnd x => psnd x
  | pvar x => if_y_eq x (pval w) e
  | passert b => passert b
  | pderef r => pderef r
  | passign x y => passign x y
  | pref v => pref v
  | pfun x t1 => pfun x (if_y_eq x t1 (aux t1))
  | pfix f x t1 => pfix f x (if_y_eq f t1 (if_y_eq x t1 (aux t1)))
  | papp e v => papp e v
  | plet x t1 t2 => plet x (aux t1) (if_y_eq x t2 (aux t2))
  | pif t0 t1 t2 => pif t0 (aux t1) (aux t2)
  | pshift k e1 => pshift k (aux e1)
  | preset e => preset (aux e)
  end.

Module Val.
  Definition value := val.
End Val.

Module Export Heap := HeapF.HeapSetup Val.

Definition empty_heap : heap := Fmap.empty.

Definition precond := hprop.
Definition postcond := val -> hprop.

(* shft's continuation could have a more general [A -> flow] type, but it can't be used in the semantics as long as it has to pass through ufun *)
Inductive result : Type :=
  | shft : var -> flow -> (val -> flow) -> result
  | norm : val -> result

(** * Staged formulae *)
with flow : Type :=
  | req : precond -> flow -> flow
  | ens : postcond -> flow
  | seq : flow -> flow -> flow
  | fex : forall A, (A -> flow) -> flow
  | fall : forall A, (A -> flow) -> flow
  | unk : var -> val -> val -> flow
  | intersect : flow -> flow -> flow
  | disj : flow -> flow -> flow
  | sh : var -> flow -> val -> flow
  | rs : flow -> val -> flow
  | defun : var -> (val -> val -> flow) -> flow.

Definition ens_ H := ens (fun r => \[r = vunit] \* H).

Definition empty := ens_ \[True].

Notation req_ H := (req H empty).

Definition ufun := val -> val -> flow.
Definition senv := Fmap.fmap var (option ufun).

Definition empty_env : senv := Fmap.empty.

Declare Scope flow_scope.
Open Scope flow_scope.

Infix ";;" := seq (at level 38, right associativity) : flow_scope.

Notation "'∃' x1 .. xn , H" :=
  (fex (fun x1 => .. (fex (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '∃' '/ '  x1  ..  xn , '/ '  H ']'") : flow_scope.

Notation "'∀' x1 .. xn , H" :=
  (fall (fun x1 => .. (fall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '∀' '/ '  x1  ..  xn , '/ '  H ']'") : flow_scope.

Notation "f '$' '(' x ',' r ')'" := (unk f x r)
  (at level 80, format "f '$' '(' x ','  r ')'", only printing) : flow_scope.

(* Notation "'⟨' f '→' r '⟩'" := (rs f r) *)
  (* (at level 40, format "'⟨' f  '→'  r '⟩'", only printing) : flow_scope. *)

(* Check (rs (∃ x, empty) vunit;; empty). *)
(* Check (∃ x, rs empty vunit;; empty). *)

(* Notation "'sh' k '.' b ',' r ⟩" := (rs f r) *)
  (* (at level 80, format "⟨ f ','  r ⟩", only printing) : flow_scope. *)

Notation "'ens' r '.' Q" := (ens (fun r => Q))
  (at level 80, format "'ens'  r '.'  Q" , only printing) : flow_scope.

Fixpoint flow_result (f:flow) (v:val) : Prop :=
  match f with
  | req _ f => flow_result f v
  | ens q => exists h r, q r h /\ v = r
  | seq f1 f2 => flow_result f2 v
  | fex f => exists a, flow_result (f a) v
  | fall f => forall a, flow_result (f a) v
  | unk _ _ r => r = v
  | intersect f1 f2 => flow_result f1 v /\ flow_result f2 v
  | disj f1 f2 => flow_result f1 v \/ flow_result f2 v
  | sh _ _ r => r = v
  | rs _ r => r = v
  | defun _ _ => v = vunit
  end.

Example e1_flow_result : flow_result (ens (fun r => \[r = vint 1])) (vint 1).
Proof.
  simpl.
  intros.
  exists empty_heap.
  eexists.
  split.
  apply hpure_intro. reflexivity.
  reflexivity.
Qed.

(** * Interpretation of a staged formula *)
Inductive satisfies : senv -> senv -> heap -> heap -> result -> flow -> Prop :=

  | s_req (s1 s2:senv) p (h1 h2:heap) r f
    (H: forall (hp hr:heap),
      p hp ->
      h1 = Fmap.union hr hp ->
      Fmap.disjoint hr hp ->
      satisfies s1 s2 hr h2 r f) :
    satisfies s1 s2 h1 h2 r (req p f)

  | s_ens s1 q h1 h2 r
    (H: exists v h3,
      r = norm v /\
      q v h3 /\
      h2 = Fmap.union h1 h3 /\
      Fmap.disjoint h1 h3) :
    satisfies s1 s1 h1 h2 r (ens q)

  | s_seq s1 s2 f1 f2 h1 h2 r
    (H: exists s3 h3 r1,
      satisfies s1 s3 h1 h3 r1 f1 /\
      satisfies s3 s2 h3 h2 r f2) :
    satisfies s1 s2 h1 h2 r (seq f1 f2)

  | s_fex s1 s2 h1 h2 r (A:Type) (f:A->flow)
    (H: exists v,
      satisfies s1 s2 h1 h2 r (f v)) :
    satisfies s1 s2 h1 h2 r (@fex A f)

  | s_fall s1 s2 h1 h2 r (A:Type) (f:A->flow)
    (H: forall v,
      satisfies s1 s2 h1 h2 r (f v)) :
    satisfies s1 s2 h1 h2 r (@fall A f)

  | s_unk s1 s2 h1 h2 r fn f x
    (He: Fmap.read s1 fn = Some f)
    (Hr: satisfies s1 s2 h1 h2 (norm r) (f x r)) :
    satisfies s1 s2 h1 h2 (norm r) (unk fn x r)

  | s_intersect s1 s2 h1 h2 r f1 f2
    (H1: satisfies s1 s2 h1 h2 r f1)
    (H2: satisfies s1 s2 h1 h2 r f2) :
    satisfies s1 s2 h1 h2 r (intersect f1 f2)

  | s_disj_l s1 s2 h1 h2 r f1 f2
    (H: satisfies s1 s2 h1 h2 r f1) :
    satisfies s1 s2 h1 h2 r (disj f1 f2)

  | s_disj_r s1 s2 h1 h2 r f1 f2
    (H: satisfies s1 s2 h1 h2 r f2) :
    satisfies s1 s2 h1 h2 r (disj f1 f2)

    (** The new rules for shift/reset are as follows. *)

  | s_sh s1 h1 x shb (v:val) :
    satisfies s1 s1 h1 h1
      (shft x shb (fun (y:val) => ens (fun r => \[y = v /\ r = v])))
      (sh x shb v)
    (** [v] may be thought of a prophecy variable for the result of a [sh]ift, which may be depended upon by anything sequenced after it (i.e. its continuation). *)
    (** A [sh] on its own reduces to a [shft] outcome an identity continuation, which is in CPS instead of having the prophecy variable. [y] is the eventual result of this [shft] once it encounters a [rs] and will be depended upon by its continuation, which is just [v]. The result [r] at this point is also [v]. *)

  | s_sh_seq s1 s2 f1 (f2k k1:val->flow) h1 h2 shb x (v:val)
      (H: exists k,
          satisfies s1 s2 h1 h2 (shft x shb k) f1 /\
            k1 = (fun x => ∃ r, k r;; f2k x)) :
    satisfies s1 s2 h1 h2 (shft x shb k1) (f1;; f2k v)

    (** This rule extends the continuation in a [shft] on the left side of a [seq]. [v] has to be specified manually, typically by a [change] tactic. *)

  | s_rs_sh s1 s2 f h1 h2 r rf
    (H: exists s3 h3 f1 (fk:val->flow) k v,
      satisfies s1 s3 h1 h3 (shft k f1 fk) f /\
      satisfies (* TODO x is fresh/not already in s3? *)
        (Fmap.update s3 k (Some (fun x r =>
          ens_ \[flow_result (fk x) v /\ v = r];;
          rs (fk x) v))) s2
      h3 h2 rf (rs f1 r)) :
    satisfies s1 s2 h1 h2 rf (rs f r)

    (** This rule applies when the body of a [rs] <i>reduces to</i> a [shft] (not when a [sh] is directly inside a [rs]; that happens in reduction). The continuation is known, so it is bound in (the environment of) the [sh]ift body before that is run. *)

  | s_rs_val s1 s2 h1 h2 v f
    (H: satisfies s1 s2 h1 h2 (norm v) f) :
    satisfies s1 s2 h1 h2 (norm v) (rs f v)

  | s_defun s1 s2 h1 x uf
    (H: s2 = Fmap.update s1 x (Some uf)) :
    satisfies s1 s2 h1 h1 (norm vunit) (defun x uf).

Notation "s1 ',' s2 ','  h1 ','  h2 ','  r  '|=' f" :=
  (satisfies s1 s2 h1 h2 r f) (at level 30, only printing).

(** * Entailment *)
Definition entails_under s1 f1 f2 :=
  forall h1 h2 s2 r,
    satisfies s1 s2 h1 h2 r f1 -> satisfies s1 s2 h1 h2 r f2.

Definition entails (f1 f2:flow) : Prop :=
  forall s1 s2 h1 h2 r, satisfies s1 s2 h1 h2 r f1 -> satisfies s1 s2 h1 h2 r f2.

Definition bientails (f1 f2:flow) : Prop :=
  forall h1 h2 r s1 s2,
    satisfies s1 s2 h1 h2 r f1 <-> satisfies s1 s2 h1 h2 r f2.

Infix "⊑" := entails (at level 90, right associativity) : flow_scope.

Notation "env '⊢' f1 '⊑' f2" :=
  (entails_under env f1 f2) (at level 90, only printing) : flow_scope.

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
  auto.
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

Infix "====>" := Morphisms.respectful (at level 80, right associativity).
Notation Proper := Morphisms.Proper.
Notation respectful := Morphisms.respectful.
Notation impl := Program.Basics.impl.
Notation flip := Basics.flip.

(** Incantations for setoid rewriting *)
Section Proprium.

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
    (eq ====> eq ====> eq ====> eq ====> eq ====> entails ====> impl)
    satisfies.
  Proof.
    unfold entails, Proper, respectful, impl.
    intros. subst.
    auto.
  Qed.

  #[global]
  Instance Proper_satisfies_bi : Proper
    (eq ====> eq ====> eq ====> eq ====> eq ====> bientails ====> impl)
    satisfies.
  Proof.
    unfold bientails, entails, Proper, respectful, impl.
    intros. subst.
    apply H4.
    auto.
  Qed.

  #[global]
  Instance Proper_satisfies_under : forall env, Proper
    (eq ====> eq ====> eq ====> eq ====> entails_under env ====> impl)
    (satisfies env).
  Proof.
    unfold entails_under, Proper, respectful, impl.
    intros. subst.
    auto.
  Qed.

  (* #[global] *)
  (* Instance Proper_seq : Proper (entails ====> entails ====> entails) seq. *)
  (* Proof. *)
  (*   unfold Proper, entails, respectful. *)
  (*   intros. *)
  (*   inverts H1 as H1; destr H1. *)
  (*   { constructor. exists h3. exists r1. *)
  (*   eauto. } *)
  (*   { constructor. exists h3. exists r1. *)
  (*   eauto. } *)
  (* Qed. *)

  (* #[global] *)
  (* Instance Proper_seq_entails_under : forall env, *)
  (*   Proper (entails_under env ====> entails_under env ====> entails_under env) seq. *)
  (* Proof. *)
  (*   unfold Proper, entails_under, respectful. *)
  (*   intros. *)
  (*   inverts H1 as H1; destr H1. *)
  (*   constructor. exists h3. exists r1. *)
  (*   split; auto. *)
  (* Qed. *)

  #[global]
  Instance fex_entails_under_morphism (A : Type) : forall env,
    Proper (Morphisms.pointwise_relation A (entails_under env) ====> entails_under env) (@fex A).
  Proof.
    unfold Proper, respectful, Morphisms.pointwise_relation, entails_under.
    intros.
    inverts H0 as H0. destr H0.
    constructor.
    exists v.
    apply H.
    assumption.
  Qed.

  #[global]
  Instance entails_entails_under : forall env,
    Proper (flip entails ====> entails ====> impl) (entails_under env).
  Proof.
    unfold Proper, respectful, entails_under, entails, flip, impl.
    intros.
    eauto.
  Qed.

  (* For rewriting in the goal. Some of the flipped instances are for this purpose.
     Without them, we can only rewrite in the Coq or the staged context. *)
  #[global]
  Instance entails_entails_under_flip : forall env,
    Proper (entails ====> flip entails ====> flip impl) (entails_under env).
  Proof.
    unfold Proper, respectful, entails_under, entails, flip, impl.
    intros.
    eauto.
  Qed.

  #[global]
  Instance bientails_entails_under : forall env,
    Proper (bientails ====> bientails ====> iff) (entails_under env).
  Proof.
    unfold Proper, respectful, entails_under, bientails, impl.
    intros.
    split; intros.
    apply H0.
    apply H1.
    apply H.
    assumption.
    apply H0.
    apply H1.
    apply H.
    assumption.
  Qed.

  (* #[global] *)
  (* Instance Proper_seq_bi : Proper (bientails ====> bientails ====> bientails) seq. *)
  (* Proof. *)
  (*   unfold Proper, bientails, respectful. *)
  (*   intros. *)
  (*   split; intros. *)
  (*   { inverts H1 as H1; destr H1. *)
  (*     constructor. exists h3. exists r1. *)
  (*     split. *)
  (*     apply H; auto. *)
  (*     apply H0; auto. } *)
  (*   { inverts H1 as H1; destr H1. *)
  (*     constructor. exists h3. exists r1. *)
  (*     split. *)
  (*     apply H; auto. *)
  (*     apply H0; auto. } *)
  (* Qed. *)

  #[global]
  Instance Proper_req_entails : Proper (eq ====> entails ====> entails) req.
  Proof.
    unfold Proper, entails, respectful, flip.
    intros.
    constructor. intros.
    rewrite <- H in H2.
    inverts H1 as H1.
    specializes H1 H3 ___.
  Qed.

  #[global]
  Instance Proper_req_bi : Proper (eq ====> bientails ====> bientails) req.
  Proof.
    unfold Proper, bientails, respectful.
    intros.
    split; intros H1.
    { constructor. intros hp hr H2 H3 H4.
      rewrite <- H in H2.
      inverts H1 as H1.
      specializes H1 H3 ___.
      apply H0. assumption. }
    { constructor. intros hp hr H2 H3 H4.
      rewrite H in H2.
      inverts H1 as H1.
      specializes H1 H3 ___.
      apply H0. assumption. }
  Qed.

End Proprium.

Lemma empty_intro : forall s1 h1,
  satisfies s1 s1 h1 h1 (norm vunit) empty.
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

Lemma ens_void_pure_intro : forall P s h,
  P -> satisfies s s h h (norm vunit) (ens_ \[P]).
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

Lemma ens_pure_intro : forall P s h r,
  P r -> satisfies s s h h (norm r) (ens (fun v => \[P v])).
Proof.
  intros.
  constructor.
  exists r.
  exists empty_heap.
  intuition.
  apply hpure_intro; easy.
  fmap_eq.
Qed.

Module Examples.

  Example e1_undelimited : forall x, exists r,
    satisfies empty_env empty_env empty_heap empty_heap r
      (sh x (ens (fun r => \[r = vint 1])) (vint 1)).
  Proof.
    intros.
    eexists.
    apply s_sh.
  Qed.

  Example e2_reset_value :
    satisfies empty_env empty_env empty_heap empty_heap (norm (vint 1))
      (rs (ens (fun r => \[r = vint 1])) (vint 1)).
  Proof.
    intros.
    apply s_rs_val.
    apply ens_pure_intro.
    reflexivity.
  Qed.

  Example e3_rs_sh_no_k : forall x, exists s,
    (* the ret of the shift can be anything because the cont is never taken *)
    satisfies empty_env s empty_heap empty_heap (norm (vint 1))
      (rs (sh x (ens (fun r => \[r = vint 1])) (vint 2)) (vint 1)).
  Proof.
    intros.
    eexists.
    apply s_rs_sh.
    exists empty_env.
    eexists.
    eexists.
    eexists.
    eexists.
    exists (vint 7).
    (* return value of the reset-wrapped continuation.
      can be anything because it's never used. *)
    split.
    constructor.
    { apply s_rs_val.
      apply ens_pure_intro.
      reflexivity. }
  Qed.

  Definition vplus (a b:val) : val :=
    match a, b with
    | vint a, vint b => vint (a + b)
    | _, _ => vunit
    end.

(** A more abstract version of [reset (1 + shift k (k 2))]. *)
(** Example values:
- f = [fun x => 1 + x]
- i = 2, some arbitrary argument to f
- k = k, some arbitrary name *)
  Example e4_rs_sh_k : forall f i k, exists s,
    satisfies empty_env s empty_heap empty_heap (norm (f i))
      (rs (∃ sr, sh k (unk k i sr) sr;;
        ens (fun r => \[r = f i]))
          (f i)).
  Proof.
    intros.
    eexists. (* this is okay because it's an output *)
    apply s_rs_sh.
    exs.
    split.
    (* put the ens into the cont *)
    {
      (* show that the body produces a shift *)
      apply s_fex. eexists.
      (* eta-expand the right side to make it clear what the continuation is *)

      change (ens (fun r => \[r = f ?sr])) with
        ((fun x => ens (fun r => \[r = f x])) sr).
      apply s_sh_seq.

      eexists.
      split.
      apply s_sh.
      reflexivity. }
    { apply s_rs_val. (* handle reset *)

      eapply s_unk. resolve_fn_in_env. (* reset body *)
      simpl.
      apply s_seq. exs. split.

      { apply ens_void_pure_intro.
        split.
        exists (vint 7). (* can be anything *)
        exists empty_heap.
        exists (f i).
        split. apply hpure_intro. reflexivity.
        reflexivity.
        reflexivity. }
      
      apply s_rs_val. (* deep reset *)
      apply s_fex. eexists. (* TODO what is this? *)

      apply s_seq. exs. split.
      apply ens_pure_intro. intuition reflexivity.
      apply ens_pure_intro. reflexivity. }
  Qed.

(** [(reset (shift k (fun x -> k x))) 4 ==> 4]
- The whole thing returns what the application of f/k returns
- The result of the shift is 4 due to the identity k
- The result of the reset is a function; 4 is the result of an inner reset that appears in the course of reduction *)
  Example e5_shift_k : forall k f, k <> f -> exists s,
    satisfies empty_env s empty_heap empty_heap (norm (vint 4))
      (rs (sh k (defun f (fun x r => unk k x r);;
                  ens (fun r => \[r = vfptr f]))
              (vint 4))
          (vfptr f);;
        unk f (vint 4) (vint 4)).
  Proof.
    intros.
    eexists.
    apply s_seq.
    eexists. eexists. eexists.
    split.
    { (* show that reset produces a function *)
      apply s_rs_sh.
      do 6 eexists.
      split.
      (* handle the shift *)
      apply s_sh.
      (* show how the shift body goes through the reset to produce the function *)
      { apply s_rs_val.
        apply s_seq. do 3 eexists. split.
        apply s_defun. reflexivity.
        apply ens_pure_intro. reflexivity. }
    }
    { (* show that applying the function returns 4 *)
      eapply s_unk. resolve_fn_in_env.
      simpl.
      (* applying the function amounts to applying the continuation *)
      eapply s_unk.
      (* TODO resolve_fn_in_env should solve this *)
      { unfold Fmap.update.
        rewrite Fmap.read_union_r.
        rewrite Fmap.read_union_l.
        apply Fmap.read_single.
        apply Fmap.indom_single.
        apply fmap_not_indom_of_neq.
        easy. }
      simpl.

      apply s_seq. do 3 eexists. split.
      apply ens_void_pure_intro.
      split.
      eexists.
      eexists.
      split.
      apply hpure_intro.
      intuition reflexivity.
      reflexivity.
      reflexivity.
      
      apply s_rs_val.
      apply ens_pure_intro.
      intuition reflexivity.
    }
  Qed.

(** [(reset 1 + (shift k (fun x -> k x))) 4 ==> 5]
- res of shift = arg of k = 4
- res of reset = res of shift body = fptr
- final res is that of the inner reset, which doesn't occur syntacically in the code as it is produced by the "handling" of the shift. *)
  Example e6_shift_k : forall k f, k <> f -> exists s,
    satisfies empty_env s empty_heap empty_heap (norm (vint 5))
      (rs (∃ sr, sh k (defun f (fun x r => unk k x r);;
                 ens (fun r => \[r = vfptr f]))
             sr;; ens (fun r => \[r = vplus (vint 1) sr]))
         (vfptr f);;
       ∃ fr, unk f (vint 4) (vint fr)).
  Proof.
    intros.
    eexists.
    apply s_seq.
    do 3 eexists.
    split.
    { (* reset *)
      (* the shift is still "handled", but produces a lambda without
        applying the continuation *)
      apply s_rs_sh.
      do 6 eexists.
      split.
      {
        apply s_fex. eexists.
        (* eta-expand the right side to make it clear what the continuation is *)
        change (ens (fun r => \[r = vplus (vint 1) ?sr])) with
          ((fun x => ens (fun r => \[r = vplus (vint 1) x])) sr).
        apply s_sh_seq. (* this moves the ens into the continuation *)
        eexists.
        split.
        apply s_sh.
        reflexivity. }
      { apply s_rs_val.
        apply s_seq.
        do 3 eexists.
        split.
        apply s_defun. reflexivity.
        apply ens_pure_intro. reflexivity. }
    }
    { (* app *)
      apply s_fex. eexists.
      eapply s_unk. resolve_fn_in_env.
      simpl.
      eapply s_unk.
      (* TODO resolve should solve this *)
      { unfold Fmap.update.
        rewrite Fmap.read_union_r.
        rewrite Fmap.read_union_l.
        apply Fmap.read_single.
        apply Fmap.indom_single.
        apply fmap_not_indom_of_neq.
        easy. }
      simpl.

      apply s_seq. do 3 eexists. split.
      apply ens_void_pure_intro.
      split.
      exists vunit.
      do 2 eexists.
      split.
      apply hpure_intro. reflexivity.
      reflexivity.
      reflexivity.
      
      apply s_rs_val.
      apply s_fex. exists vunit. (* the result of earlier cont left of seq *)
      apply s_seq. do 3 eexists. split.
      (* TODO ens_pure_info has more info, empty heaps? *)
      apply ens_pure_intro. intuition reflexivity.
      apply ens_pure_intro. reflexivity.
    }
  Qed.

End Examples.

(** * Shift-freedom *)
(** Syntactic definition. This is not strong enough to prove the reduction rules, particularly that executions do not end in a [shft]. A stronger definition likely is [Inductive] and enumerates the cases which return [norm], so we can do induction on it. This should entail the semantic definition. With how we do things, the semantic definition is both sufficient and more convenient, so this is mostly left here for posterity. *)
Fixpoint syn_shift_free (f:flow) : Prop :=
  match f with
  | req _ f => syn_shift_free f
  | ens q => True
  | seq f1 f2 => syn_shift_free f1 /\ syn_shift_free f2
  | fex f => exists a, syn_shift_free (f a)
  | fall f => forall a, syn_shift_free (f a)
  | unk _ _ r => False
  | intersect f1 f2 => syn_shift_free f1 /\ syn_shift_free f2
  | disj f1 f2 => syn_shift_free f1 /\ syn_shift_free f2
  | sh _ _ r => False
  | rs _ r => True
  | defun _ _ => True
  end.

(** Semantic definition of shift-freedom. *)
Definition shift_free (f:flow) : Prop :=
  forall s1 s2 h1 h2 v x k b,
    satisfies s1 s2 h1 h2 (norm v) f /\
      not (satisfies s1 s2 h1 h2 (shft x k b) f).

(** * Reduction rules *)
(** RNormal from the paper *)
Lemma red_normal : forall f r,
  shift_free f ->
  entails (rs f r) f.
Proof.
  introv Hsf.
  unfold entails. intros.
  inverts H as H; destr H.
  { (* this case cannot be as f is shift-free *)
    specializes Hsf s1 s3 ___. destruct Hsf.
    instantiate (TEMP2 := vunit). (* unused but needs to be given *)
    apply H2 in H0.
    false. }
  { assumption. }
Qed.

(** RSkip from the paper *)
Lemma red_skip : forall f1 f2 r,
    shift_free f1 ->
    entails (rs (f1;; f2) r) (f1;; rs f2 r).
Proof.
  introv Hsf.
  unfold entails. intros.
  inverts H as H; destr H.
  { (* if either f1 or f2 produce a shift *)
    inverts H0 as H0. destr H0.
    { (* f2 produces a shift *)
      constructor. exs.
      split.
      exact H0.
      constructor. exs.
      split.
      exact H2.
      exact H1. }
    { (* f1 cannot produce a shift as it is shift-free *)
      destr H0.
      apply Hsf in H0.
      false.
      exact vunit. } }
  { (* if f1 returns *)
    inverts H as H. destr H.
    constructor. exs.
    split.
    exact H.
    apply s_rs_val.
    assumption. }
Qed.

(** * Correspondence with the paper *)
(** ** Differences *)
(** #<!-- this space is needed!!-->#
- Function pointer values [vfptr] enable arbitrary higher-order staged formulae. A [defun] staged formula (conceptually just an [ens] which binds a function value) and an output [senv] added to [satisfies] complete this, allowing shift bodies to return continuations. *)
(** ** Section 4.3. Shift/Reset Reduction *)
(** The reduction rules are proved as lemmas.
- #<a href="&num;red_skip">red_skip</a>#
- #<a href="&num;red_normal">red_normal</a># *)