From Coq Require Import Classes.RelationClasses.
From Coq Require Morphisms Program.Basics.

From Staged Require Export HeapF.
From Staged Require Export LibFmap.
From Staged Require Export ExtraTactics.

Local Open Scope string_scope.
(* Local Open Scope nat_scope. *)
Local Open Scope Z_scope.
Local Open Scope list_scope.

Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.

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
(** A deeply-embedded function pointer, referring to a [ufun] in the environment. *)

with expr : Type :=
  | pvar (x: var)
  | pval (v: val)
  | plet (x: var) (e1 e2: expr)
  | pfix (xf: var) (x: var) (e: expr)
  | pfun (x: var) (e: expr)
  | padd (e1 e2: expr)
  | pfst (e: expr)
  | psnd (e: expr)
  | pminus (e1 e2: expr)
  | passert (v: val)
  | pref (v: val)
  | pderef (v: val)
  | passign (e1: val) (e2: val)
  | pif (v: val) (e1: expr) (e2: expr)
  | papp (e1: expr) (e2: expr)
  | pshift (x: var) (eb: expr) (x1:var) (ek: expr)
  | preset (e: expr).

#[global]
Instance Inhab_val : Inhab val.
Proof.
  constructor.
  exists vunit.
  constructor.
Qed.

Fixpoint subst (y:var) (v:val) (e:expr) : expr :=
  let aux t := subst y v t in
  let if_y_eq x t1 t2 := if var_eq x y then t1 else t2 in
  match e with
  | pval v => pval v
  | padd x z => padd x z
  | pminus x z => pminus x z
  | pfst x => pfst x
  | psnd x => psnd x
  | pvar x => if_y_eq x (pval v) e
  | passert b => passert b
  | pderef r => pderef r
  | passign x z => passign x z
  | pref v => pref v
  | pfun x t1 => pfun x (if_y_eq x t1 (aux t1))
  | pfix f x t1 => pfix f x (if_y_eq f t1 (if_y_eq x t1 (aux t1)))
  | papp e v => papp e v
  | plet x t1 t2 => plet x (aux t1) (if_y_eq x t2 (aux t2))
  | pif t0 t1 t2 => pif t0 (aux t1) (aux t2)
  | pshift x e1 x1 ek => pshift x (aux e1) x1 (aux ek)
  | preset e => preset (aux e)
  end.

Module Val.
  Definition value := val.
End Val.

Module Export Heap := HeapF.HeapSetup Val.

Definition empty_heap : heap := Fmap.empty.

Definition postcond := val -> hprop.

(** * Staged formulae *)
Inductive flow : Type :=
  | fin : flow
  | req : hprop -> flow -> flow
  | ens : postcond -> flow
  | seq : flow -> flow -> flow
  | fex : forall (A:Type), (A -> flow) -> flow
  | fall : forall (A:Type), (A -> flow) -> flow
  | unk : var -> val -> val -> flow
  | intersect : flow -> flow -> flow
  | disj : flow -> flow -> flow
  | sh : var -> flow -> val -> flow -> flow
  .

Definition ens_ H := ens (fun r => \[r = vunit] \* H).

Definition empty := ens_ \[True].

Notation req_ H := (req H empty).

Definition ufun := val -> val -> flow.

#[global]
Instance Inhab_ufun : Inhab ufun.
Proof.
  constructor.
  exists (fun (r v:val) => ens_ \[r = v]).
  constructor.
Qed.

Definition senv := Fmap.fmap var ufun.

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

Notation "'ens' r '.' Q" := (ens (fun r => Q))
  (at level 80, format "'ens'  r '.'  Q" , only printing) : flow_scope.

Implicit Types s : senv.
Implicit Types h : heap.
Implicit Types H : hprop.
Implicit Types Q : postcond.
Implicit Types u : ufun.
Implicit Types f : flow.
Implicit Types x y z k : var.
Implicit Types a v r : val.
Implicit Types e : expr.

Inductive fstep : senv -> senv -> heap -> heap -> val -> flow -> flow -> Prop :=

  | s_req : forall s1 s2 H h1 h2 v f f1,
    (forall (hp hr:heap),
      H hp ->
      h1 = Fmap.union hr hp ->
      Fmap.disjoint hr hp ->
      fstep s1 s2 hr h2 v f f1) ->
    fstep s1 s2 h1 h2 v (req H f) f1

  | s_ens : forall s1 Q h1 h2 v h3,
    Q v h3 ->
    h2 = Fmap.union h1 h3 ->
    Fmap.disjoint h1 h3 ->
    fstep s1 s1 h1 h2 v (ens Q) fin

  | s_seq_empty : forall v s1 h1 f2,
    fstep s1 s1 h1 h1 v (seq fin f2) f2

  | s_seq_step : forall v s1 s2 h1 h2 f1 f2 f3,
    fstep s1 s2 h1 h2 v f1 f3 ->
    fstep s1 s2 h1 h2 v (seq f1 f2) (seq f3 f2)

  (* | s_fex : forall s1 s2 h1 h2 v (A:Type) (c:A->flow) b,
    fstep s1 s2 h1 h2 v (@fex A c) (c b)

  | s_fall : forall s1 s2 h1 h2 v (A:Type) (c:A->flow) f1,
    (forall b, fstep s1 s2 h1 h2 v (c b) f1) ->
    fstep s1 s2 h1 h2 v (@fall A c) f1 *)

  (* | s_intersect_step_l : forall s1 s2 h1 h2 v f1 f2 f3,
    fstep s1 s2 h1 h2 v f1 f3 ->
    fstep s1 s2 h1 h2 v (intersect f1 f2) (intersect f3 f2)

  | s_intersect_step_r : forall s1 s2 h1 h2 v f1 f2 f3,
    fstep s1 s2 h1 h2 v f1 f3 ->
    fstep s1 s2 h1 h2 v (intersect f1 f2) (intersect f1 f3)

  | s_intersect_elim_l : forall s1 h1 v f2,
    fstep s1 s1 h1 h1 v (intersect fin f2) f2

  | s_intersect_elim_r : forall s1 h1 v f1,
    fstep s1 s1 h1 h1 v (intersect f1 fin) f1 *)

  (* | s_disj_l : forall s1 h1 v f1 f2,
    fstep s1 s1 h1 h1 v (disj f1 f2) f1

  | s_disj_r : forall s1 h1 v f1 f2,
    fstep s1 s1 h1 h1 v (disj f1 f2) f2 *)

  | s_unk : forall s1 h1 h1 r xf uf a,
    Fmap.read s1 xf = uf ->
    fstep s1 s1 h1 h1 r (unk xf a r) (uf a r)
  .

(* Notation "s1 ',' s2 ','  h1 ','  h2 ','  r  '|=' f1 '~>' f2" :=
  (fstep s1 s2 h1 h2 r f1 f2) (at level 30, only printing). *)


Inductive fsteps :
  senv -> senv -> heap -> heap -> val -> flow -> flow -> Prop :=

  | fsteps_refl : forall s1 h1 v f,
    fsteps s1 s1 h1 h1 v f f

  | fsteps_step : forall s1 s2 s3 h1 h2 h3 v f1 f2 f3,
    fstep s1 s2 h1 h2 v f1 f2 ->
    fsteps s2 s3 h2 h3 v f2 f3 ->
    fsteps s1 s3 h1 h3 v f1 f3.

(* Notation "s1 ',' s2 ','  h1 ','  h2 ','  r  '|=' f1 '~>*' f2" :=
  (fsteps s1 s2 h1 h2 r f1 f2) (at level 30, only printing). *)

Lemma fsteps_of_fstep_ : forall s1 s2 h1 h2 v f1 f2,
  fstep s1 s2 h1 h2 v f1 f2 ->
  fsteps s1 s2 h1 h2 v f1 f2.
Proof using.
  introv M. applys fsteps_step M. applys fsteps_refl.
Qed.

Lemma fsteps_trans : forall s1 s2 s3 h1 h2 h3 v f1 f2 f3,
  fsteps s1 s2 h1 h2 v f1 f2 ->
  fsteps s2 s3 h2 h3 v f2 f3 ->
  fsteps s1 s3 h1 h3 v f1 f3.
Proof using.
  introv M1. induction M1; introv M2. { auto. } { constructors*. }
Qed.

Definition fterminal f : Prop :=
  f = fin.

Definition freducible s1 h1 f1 : Prop :=
  exists s2 h2 v f2, fstep s1 s2 h1 h2 v f1 f2.

Lemma freducible_inv : forall s h v,
  ~ freducible s h fin.
Proof using.
  intros. intros M. inverts M. destr H. inverts H0 as H0.
Qed.

Definition fnotstuck s h f : Prop :=
  fterminal f \/ freducible s h f.

(* Inductive terminates : heap->trm->Prop :=
  | terminates_step : forall s t,
      (forall s' t', step s t s' t' -> terminates s' t') ->
      terminates s t.

Definition safe (s:heap) (t:trm) : Prop :=
  forall s' t', fsteps s t s' t' -> notstuck s' t'.

Definition correct (s:heap) (t:trm) (Q:val->hprop) : Prop :=
  forall s' v, fsteps s t s' v -> Q v s'. *)

Example step_e1: forall (x y:loc) s1, exists s2 h2 v,
  x <> y ->
  fsteps s1 s2 empty_heap h2 v (ens_ (x~~>vint 1);; ens_ (y~~>vint 2)) fin.
Proof.
  intros. exs. intros.

  applys fsteps_step.
  { applys s_seq_step.
    applys s_ens.
    - hintro. split. reflexivity. apply hsingle_intro.
    - fmap_eq. reflexivity.
    - fmap_disjoint. }

  applys fsteps_step.
  { applys s_seq_empty. }

  applys fsteps_step.
  { applys s_ens.
    - hintro. split. reflexivity. apply hsingle_intro.
    - reflexivity.
    - apply* Fmap.disjoint_single_single. }

  applys fsteps_refl.
Qed.


(* Definition pufun := val -> val -> expr. *)
Definition penv := Fmap.fmap var val.
(* pufun. *)
Implicit Types p : penv.

Definition empty_penv : penv := Fmap.empty.

Inductive step : penv -> heap -> expr -> heap -> expr -> Prop :=

(* Context rules *)
(* | step_seq_ctx : forall s1 s2 t1 t1' t2,
    step s1 t1 s2 t1' ->
    step s1 (trm_seq t1 t2) s2 (trm_seq t1' t2) *)
| step_let_ctx : forall p h1 h2 x t1 t1' t2,
    step p h1 t1 h2 t1' ->
    step p h1 (plet x t1 t2) h2 (plet x t1' t2)

| step_let_sh : forall p h x x1 x2 e2 ek eb,
    step p h (plet x (pshift x1 eb x2 ek) e2)
      h (pshift x1 eb x2 (plet x eb e2))

| step_reset_val : forall p h v,
    step p h (preset (pval v)) h (pval v)

| step_reset_ctx : forall p h1 h2 e1 e2,
    step p h1 e1 h2 e2 ->
    step p h1 (preset e1) h2 (preset e2)

| step_reset_sh : forall p h x x1 eb ek,
    step p h (preset (pshift x eb x1 ek)) h (subst x (vfun x1 ek) eb)

(* Reductions *)
| step_fun : forall p h x t1,
    step p h (pfun x t1) h (pval (vfun x t1))
(* | step_fix : forall h f x t1,
    step h (pfix f x t1) h (vfix f x t1) *)
| step_app_fun : forall p h v1 v2 x t1,
    v1 = vfun x t1 ->
    step p h (papp (pval v1) (pval v2)) h (subst x v2 t1)

| step_app_unk : forall p h va xf x e1,
    Fmap.read p xf = vfun x e1 ->
    step p h (papp (pvar xf) (pval va)) h (subst x va e1)

(* | step_app_fix : forall h v1 v2 f x t1,
    v1 = vfix f x t1 ->
    step h (papp v1 v2) h (subst x v2 (subst f v1 t1)) *)
| step_if : forall p h b t1 t2,
    step p h (pif (vbool b) t1 t2) h (if b then t1 else t2)
(* | step_seq : forall s t2 v1,
    step s (trm_seq v1 t2) s t2 *)
| step_let : forall p h x t2 v1,
    step p h (plet x (pval v1) t2) h (subst x v1 t2)

(* Primitive operations *)
(* | step_add : forall s n1 n2,
    step s (val_add (val_int n1) (val_int n2)) s (val_int (n1 + n2))
| step_div : forall s n1 n2,
    n2 <> 0 ->
    step s (val_div (val_int n1) (val_int n2)) s (Z.quot n1 n2)
| step_rand : forall s n n1,
    0 <= n1 < n ->
    step s (val_rand (val_int n)) s (val_int n1)
| step_ref : forall s v p,
    ~ Fmap.indom s p ->
    step s (val_ref v) (Fmap.update s p v) (val_loc p)
| step_get : forall s p,
    Fmap.indom s p ->
    step s (val_get (val_loc p)) s (Fmap.read s p)
| step_set : forall s p v,
    Fmap.indom s p ->
    step s (val_set (val_loc p) v) (Fmap.update s p v) val_unit
| step_free : forall s p,
    Fmap.indom s p ->
    step s (val_free (val_loc p)) (Fmap.remove s p) val_unit *)
.

(** The judgment [steps s t s' t'] corresponds to the reflexive and transitive
    closure of [step]. Concretely, it asserts that the configuration [(s,t)] can
    reduce in zero, one, or several steps to [(s',t')]. *)

Inductive steps : penv -> heap -> expr -> heap -> expr -> Prop :=
  | steps_refl : forall p h t,
      steps p h t h t
  | steps_step : forall p h1 h2 h3 t1 t2 t3,
      step p h1 t1 h2 t2 ->
      steps p h2 t2 h3 t3 ->
      steps p h1 t1 h3 t3.

Lemma steps_of_step : forall p h1 h2 t1 t2,
  step p h1 t1 h2 t2 ->
  steps p h1 t1 h2 t2.
Proof using. introv M. applys steps_step M. applys steps_refl. Qed.

Lemma steps_trans : forall p h1 h2 h3 t1 t2 t3,
  steps p h1 t1 h2 t2 ->
  steps p h2 t2 h3 t3 ->
  steps p h1 t1 h3 t3.
Proof using.
  introv M1. induction M1; introv M2. { auto. } { constructors*. }
Qed.

Definition terminal e : Prop :=
  match e with
  | pval _ => True
  | pshift _ _ _ _ => True
  | _ => False
  end.

Definition reducible p h e : Prop :=
  exists h' e', step p h e h' e'.

Lemma reducible_val_inv : forall p h v,
  ~ reducible p h (pval v).
Proof using. introv (s'&e'&M). inverts M. Qed.

Lemma reducible_val_shift : forall p h v x1 eb x2 ek,
  ~ reducible p h (pshift x1 eb x2 ek).
Proof using. introv (s'&e'&M). inverts M. Qed.

Definition notstuck p h e : Prop :=
  terminal e \/ reducible p h e.



Example e1_step: exists er,
  steps empty_penv empty_heap (pshift "k" (papp (pvar "k") (pval (vint 1))) "r" (pvar "r"))
    empty_heap er.
Proof.
(* a shift on its own is terminal already *)
Abort.

Example e1_step: exists er,
  steps (Fmap.single "k" (vfun "x" (pvar "x"))) empty_heap
    (preset (plet "x"
      (pshift "k" (papp (pvar "k") (pval (vint 1))) "r" (pvar "r"))
      (padd (pvar "x") (pval (vint 1)))))
    empty_heap er.
Proof.
  intros. exs. intros.

  applys steps_step.
  { applys step_reset_ctx.
    applys step_let_sh. }

  applys steps_step.
  { applys step_reset_sh. }

  simpl.

  applys steps_step.
  { applys step_app_unk.
    resolve_fn_in_env. }

  simpl.

  applys steps_refl.
Qed.
(* Print e1_step. *)


Inductive terminates : heap->expr->Prop :=
  | terminates_step : forall p h e,
      (forall h' e', step p h e h' e' -> terminates h' e') ->
      terminates h e.

Definition safe p h e : Prop :=
  forall h' e', steps p h e h' e' -> notstuck p h' e'.

(* TODO relation between contents of s and p. needed? expressed outside? *)
(* TODO relation between shift bodies. step index? *)
Fixpoint correct n s p h e f : Prop :=
  (* forall h' v, steps p h e h' (pval v) -> Q v h'. *)
  forall h1 er,
    terminal er ->
    steps p h e h1 er ->
  match n, er with
  | O, pval v => fsteps s s h h1 v f fin
  | S n1, pshift x1 eb x2 ek =>
    (* exists v f1 f2 v1, *)
    forall v f1 f2 v1,
    correct n1 s p h1 eb f1 ->
    correct n1 s p h1 ek f2 ->
    fsteps s s h h1 v f (sh x1 f1 v1 f2)
  | _, _ => False
  end.

(* TODO this could be inductive maybe, then no need for the index *)



  (* -> Q v h1. *)

(* Lemma seval_sound : forall h e Q,
  seval h e Q ->
  terminates h e /\ safe h e /\ correct h e Q.
Proof using.
  introv M. splits.
  { applys* seval_terminates. }
  { applys* seval_safe. }
  { applys* seval_correct. }
Qed. *)

(* need an equiv of seval to define triple,
  and which implies these soundness properties.
  try to prove the soundness properties directly first. *)

Example e2: correct O empty_env empty_penv empty_heap
  (pval (vint 1)) (ens (fun r => \[r = vint 1])).
Proof.
  simpl. intros.
  unfold terminal in H. destruct er; tryfalse. clear H.
  {
    inverts H0 as H.
    { (* refl *)
      eapply fsteps_step.
      { applys s_ens.
        hintro. reflexivity. fmap_eq. reflexivity. fmap_disjoint. }
      eapply fsteps_refl. }
    { (* values don't step *)
      false_invert H. }
  }
  { inverts H0 as H0. false_invert H0. }
Qed.

Example e3: correct (S O) empty_env empty_penv empty_heap
  (pshift "x1" (pval (vint 1)) "x2" (pvar "x2"))
  (sh "x" (ens (fun r => \[True])) (vint 1) (ens (fun r => \[True]))).
Proof.
  unfold correct. intros.
  unfold terminal in H. destruct er; tryfalse. clear H.
  { inverts H0 as H0. false_invert H0. }
  {
    intros.
    inverts H0 as H0.
    { (* refl *)
      eapply fsteps_step.
      { applys s_sh.
        hintro. reflexivity. fmap_eq. reflexivity. fmap_disjoint. }
      eapply fsteps_refl. }
    }
    { (* values don't step *)
      false_invert H0. }
  }
Qed.



(* both are programs. so deeply embed staged as well.
  and this is a compilation problem *)
(* cps denotation? *)















(** * Entailment *)
(* Definition entails (f1 f2:flow) : Prop :=
  forall s1 s2 h1 h2 v,
    fsteps s1 s2 h1 h2 v f1 fin ->
    fsteps s1 s2 h1 h2 v f2 fin.

Infix "⊑" := entails (at level 90, right associativity) : flow_scope.

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

Infix "====>" := Morphisms.respectful (at level 80, right associativity).
Notation Proper := Morphisms.Proper.
Notation respectful := Morphisms.respectful.
Notation impl := Program.Basics.impl.
Notation flip := Basics.flip.

(** Incantations for setoid rewriting *)
Section Propriety.

  #[global]
  Instance Proper_entails : Proper
    (flip entails ====> entails ====> impl)
    entails.
  Proof.
    unfold entails, Proper, respectful, impl.
    intros.
    auto.
  Qed.

  (* Lemma steps_seq_inv: forall s1 s2 s3 h1 h2 h3 v f1 f2,
    fsteps s1 s2 h1 h2 v (f1;; f2) fin ->
    fsteps s1 s3 h1 h3 v f1 fin /\ fsteps s3 s2 h3 h2 v f2 fin. *)
  Lemma steps_seq_inv: forall s1 s2 h1 h2 v f1 f2,
    fsteps s1 s2 h1 h2 v (f1;; f2) fin ->
    exists s3 h3, fsteps s1 s3 h1 h3 v f1 fin /\ fsteps s3 s2 h3 h2 v f2 fin.
  Proof.
    (* intros s1 s2 h1 h2 v f1. *)
    (* dependent induction f1; intros. *)

    intros.

    inverts H as H.
    (* inverts H as H. *)
    dependent induction H.
    (* induction H. *)
    {
    exists s1 h1.
    (* exists s2 h2. *)
    split.
    apply steps_refl.
    assumption.
    }
    {
      applys IHsatisfies.

      (* inverts H as H. *)

      (* specializes IHsatisfies f3 f2. *)

    }




(*
    (* remember (f1;; f2) as f3.
    remember fin as f4.
    induction H.
    false.
    subst. *)
    dependent induction H.
    (* steps_refl case eliminated *)
    pose proof H.
    inverts H as H.
    (* f1 is fin *)
    clear IHsteps.
    (* specializes IHsteps fin f4. *)
    admit.
    (* f1; f2 takes a step *)
      specializes IHsteps f5 f2. do 2 forward IHsteps by reflexivity.
      destr IHsteps.
      exists s0 h0.
      split. 2: { assumption. }
      applys steps_step H H2.
      (* applys s_seq_step. *)
 *)

Admitted.

    (* exs.
    split.
    {
      inverts H as H.
      
      admit.
    }
    { admit. }


    (* split; dependent induction H.
    {
      (* f1 *)
      (* the seq has to take a step, to f4 *)
      (* pose proof H. *)
      (* there are two cases. either f1 is fin or we take a step *)
      inverts H as H.
      { (* f1 is fin and f2 = f4 *)
        clear IHsteps.
        (* applys IHsteps. 2: { reflexivity. } *)
        applys_eq steps_refl.
        admit.
        admit.
      }
      { (* f1 takes a step *)
        specializes IHsteps f5 f2. do 2 forward IHsteps by reflexivity.
        applys steps_step H IHsteps. }
    }
    { admit. } *)
  Admitted. *)

  Lemma steps_seq_intro: forall s1 s2 s3 h1 h2 h3 v f1 f2,
    fsteps s1 s3 h1 h3 v f1 fin ->
    fsteps s3 s2 h3 h2 v f2 fin ->
    fsteps s1 s2 h1 h2 v (f1;; f2) fin.
  Proof.
    intros.
    dependent induction H.
    { (* f1 is fin, so doesn't step *)
      applys steps_step.
      eapply s_seq_empty.
      assumption. }
    { (* f1 fsteps to f3, which goes to fin *)
      applys steps_step.
      { applys s_seq_step. eassumption. }
        applys IHsteps H1.
        reflexivity. }
  Qed.

  #[global]
  Instance Proper_seq : Proper (entails ====> entails ====> entails) seq.
  Proof.
    unfold Proper, entails, respectful.
    intros.
    eapply steps_seq_inv in H1. destr H1.
    specializes H H2. clear H2.
    specializes H0 H3. clear H3.
    applys steps_seq_intro H H0.
  Qed.

End Propriety. *)
