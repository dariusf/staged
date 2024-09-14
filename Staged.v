
(* From Coq Require Import ZArith Lia Bool List String Program.Equality Classes.RelationClasses. *)
From Coq Require Import Classes.RelationClasses.

Set Implicit Arguments.
From SLF Require Export LibString LibCore.
From SLF Require Export LibSepTLCbuffer LibSepFmap.
Module Fmap := LibSepFmap.
From SLF Require LibSepSimpl.

From SLF Require Import Tactics.

(* From CDF Require Import Common Sequences Separation Tactics HeapTactics. *)

Local Open Scope string_scope.
(* Local Open Scope nat_scope. *)
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition ident : Type := string.
Definition ident_eq := String.string_dec.

Inductive val :=
  | vint : Z -> val
  | vfun : ident -> expr -> val
  | vfix : ident -> ident -> expr -> val

with expr : Type :=
  | pvar (x: ident)
  | pval (v: val)
  | plet (x: ident) (e1: expr) (e2: expr)
  | pfix (f: ident) (x: ident) (e: expr)
  | pfun (x: ident) (e: expr)
  (* | pref (x: ident) *)
  (* | pderef (x: ident) *)
  (* | passign (x1: ident) (x2: ident) *)
  | pif (x: val) (e1: expr) (e2: expr)
  | pcall (x: val) (a: val).

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
  | enorm : val -> eresult.

Definition loc : Type := nat.
Definition heap : Type := fmap loc val.

Definition empty_heap : heap := Fmap.empty.

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

(* copied from LibSepReference *)

(* this notation is missing for some reason *)
Notation "h1 \u h2" := (Fmap.union h1 h2)
  (at level 37, right associativity).

(* ################################################################# *)
(** * Heap Predicates *)

(** We next define heap predicates and establish their properties. All this
    material is wrapped in a module, allowing us to instantiate the functor from
    chapter [LibSepSimpl] that defines the tactic [xsimpl]. *)
Module SepSimplArgs.

(* ================================================================= *)
(** ** Hprop and Entailment *)

Declare Scope hprop_scope.
Open Scope hprop_scope.

(** The type of heap predicates is named [hprop]. *)

Definition hprop := heap -> Prop.

(** Implicit types for meta-variables. *)

Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.

(** Entailment for heap predicates, written [H1 ==> H2]. This entailment
    is linear. *)

Definition himpl (H1 H2:hprop) : Prop :=
  forall h, H1 h -> H2 h.

Notation "H1 ==> H2" := (himpl H1 H2) (at level 55) : hprop_scope.

(** Entailment between postconditions, written [Q1 ===> Q2]. *)

Definition qimpl A (Q1 Q2:A->hprop) : Prop :=
  forall (v:A), Q1 v ==> Q2 v.

Notation "Q1 ===> Q2" := (qimpl Q1 Q2) (at level 55) : hprop_scope.

(* ================================================================= *)
(** ** Definition of Heap Predicates *)

(** The core heap predicates are defined next, together with the
    associated notation:

    - [\[]] denotes the empty heap predicate
    - [\[P]] denotes a pure fact
    - [\Top] denotes the true heap predicate (affine)
    - [p ~~> v] denotes a singleton heap
    - [H1 \* H2] denotes the separating conjunction
    - [Q1 \*+ H2] denotes the separating conjunction extending a postcondition
    - [\exists x, H] denotes an existential quantifier
    - [\forall x, H] denotes a universal quantifier
    - [H1 \-* H2] denotes a magic wand between heap predicates
    - [Q1 \--* Q2] denotes a magic wand between postconditions. *)

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

Notation "\[]" := (hempty)
  (at level 0) : hprop_scope.

Notation "p '~~>' v" := (hsingle p v) (at level 32) : hprop_scope.

Notation "H1 '\*' H2" := (hstar H1 H2)
  (at level 41, right associativity) : hprop_scope.

Notation "'\exists' x1 .. xn , H" :=
  (hexists (fun x1 => .. (hexists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\exists' '/ '  x1  ..  xn , '/ '  H ']'") : hprop_scope.

Notation "'\forall' x1 .. xn , H" :=
  (hforall (fun x1 => .. (hforall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\forall' '/ '  x1  ..  xn , '/ '  H ']'") : hprop_scope.

(** The remaining operators are defined in terms of the preivous above,
    rather than directly as functions over heaps. Doing so reduces the
    amount of proofs, by allowing to better leverage the tactic [xsimpl]. *)

Definition hpure (P:Prop) : hprop :=
  \exists (p:P), \[].

Definition htop : hprop :=
  \exists (H:hprop), H.

Definition hwand (H1 H2 : hprop) : hprop :=
  \exists H0, H0 \* hpure ((H1 \* H0) ==> H2).

Definition qwand A (Q1 Q2:A->hprop) : hprop :=
  \forall x, hwand (Q1 x) (Q2 x).

Notation "\[ P ]" := (hpure P)
  (at level 0, format "\[ P ]") : hprop_scope.

Notation "\Top" := (htop) : hprop_scope.

Notation "Q \*+ H" := (fun x => hstar (Q x) H)
  (at level 40) : hprop_scope.

Notation "H1 \-* H2" := (hwand H1 H2)
  (at level 43, right associativity) : hprop_scope.

Notation "Q1 \--* Q2" := (qwand Q1 Q2)
  (at level 43) : hprop_scope.

(* ================================================================= *)
(** ** Basic Properties of Separation Logic Operators *)

(* ----------------------------------------------------------------- *)
(** *** Tactic for Automation *)

(** We set up [auto] to process goals of the form [h1 = h2] by calling
    [fmap_eq], which proves equality modulo associativity and commutativity. *)

#[global] Hint Extern 1 (_ = _ :> heap) => fmap_eq.

(** We also set up [auto] to process goals of the form [Fmap.disjoint h1 h2]
    by calling the tactic [fmap_disjoint], which essentially normalizes all
    disjointness goals and hypotheses, split all conjunctions, and invokes
    proof search with a base of hints specified in [LibSepFmap.v]. *)

Import Fmap.DisjointHints.

Tactic Notation "fmap_disjoint_pre" :=
  subst; rew_disjoint; jauto_set.

#[global] Hint Extern 1 (Fmap.disjoint _ _) => fmap_disjoint_pre.

(* ----------------------------------------------------------------- *)
(** *** Properties of [himpl] and [qimpl] *)

Lemma himpl_refl : forall H,
  H ==> H.
Proof using. introv M. auto. Qed.

#[global] Hint Resolve himpl_refl.

Lemma himpl_trans : forall H2 H1 H3,
  (H1 ==> H2) ->
  (H2 ==> H3) ->
  (H1 ==> H3).
Proof using. introv M1 M2. unfolds* himpl. Qed.

Lemma himpl_trans_r : forall H2 H1 H3,
   H2 ==> H3 ->
   H1 ==> H2 ->
   H1 ==> H3.
Proof using. introv M1 M2. applys* himpl_trans M2 M1. Qed.

Lemma himpl_antisym : forall H1 H2,
  (H1 ==> H2) ->
  (H2 ==> H1) ->
  (H1 = H2).
Proof using. introv M1 M2. applys pred_ext_1. intros h. iff*. Qed.

Lemma hprop_op_comm : forall (op:hprop->hprop->hprop),
  (forall H1 H2, op H1 H2 ==> op H2 H1) ->
  (forall H1 H2, op H1 H2 = op H2 H1).
Proof using. introv M. intros. applys himpl_antisym; applys M. Qed.

Lemma qimpl_refl : forall A (Q:A->hprop),
  Q ===> Q.
Proof using. intros. unfolds*. Qed.

#[global] Hint Resolve qimpl_refl.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hempty] *)

Lemma hempty_intro :
  \[] Fmap.empty.
Proof using. unfolds*. Qed.

Lemma hempty_inv : forall h,
  \[] h ->
  h = Fmap.empty.
Proof using. auto. Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hstar] *)

Lemma hstar_intro : forall H1 H2 h1 h2,
  H1 h1 ->
  H2 h2 ->
  Fmap.disjoint h1 h2 ->
  (H1 \* H2) (Fmap.union h1 h2).
Proof using. intros. exists~ h1 h2. Qed.

Lemma hstar_inv : forall H1 H2 h,
  (H1 \* H2) h ->
  exists h1 h2, H1 h1 /\ H2 h2 /\ Fmap.disjoint h1 h2 /\ h = Fmap.union h1 h2.
Proof using. introv M. applys M. Qed.

Lemma hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.
Proof using.
  applys hprop_op_comm. unfold hprop, hstar. intros H1 H2.
  intros h (h1&h2&M1&M2&D&U). rewrite~ Fmap.union_comm_of_disjoint in U.
  exists* h2 h1.
Qed.

Lemma hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).
Proof using.
  intros H1 H2 H3. applys himpl_antisym; intros h.
  { intros (h'&h3&(h1&h2&M3&M4&D'&U')&M2&D&U). subst h'.
    exists h1 (h2 \+ h3). splits~. { applys* hstar_intro. } }
  { intros (h1&h'&M1&(h2&h3&M3&M4&D'&U')&D&U). subst h'.
    exists (h1 \+ h2) h3. splits~. { applys* hstar_intro. } }
Qed.

Lemma hstar_hempty_l : forall H,
  \[] \* H = H.
Proof using.
  intros. applys himpl_antisym; intros h.
  { intros (h1&h2&M1&M2&D&U). forwards E: hempty_inv M1. subst.
    rewrite~ Fmap.union_empty_l. }
  { intros M. exists (Fmap.empty:heap) h. splits~. { applys hempty_intro. } }
Qed.

Lemma hstar_hempty_r : forall H,
  H \* \[] = H.
Proof using.
  applys neutral_r_of_comm_neutral_l. applys~ hstar_comm. applys~ hstar_hempty_l.
Qed.

Lemma hstar_hexists : forall A (J:A->hprop) H,
  (hexists J) \* H = hexists (fun x => (J x) \* H).
Proof using.
  intros. applys himpl_antisym; intros h.
  { intros (h1&h2&(x&M1)&M2&D&U). exists~ x h1 h2. }
  { intros (x&(h1&h2&M1&M2&D&U)). exists h1 h2. splits~. { exists~ x. } }
Qed.

Lemma hstar_hforall : forall H A (J:A->hprop),
  (hforall J) \* H ==> hforall (J \*+ H).
Proof using.
  intros. intros h M. destruct M as (h1&h2&M1&M2&D&U). intros x. exists~ h1 h2.
Qed.

Lemma himpl_frame_l : forall H2 H1 H1',
  H1 ==> H1' ->
  (H1 \* H2) ==> (H1' \* H2).
Proof using. introv W (h1&h2&?). exists* h1 h2. Qed.

Lemma himpl_frame_r : forall H1 H2 H2',
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1 \* H2').
Proof using.
  introv M. do 2 rewrite (@hstar_comm H1). applys~ himpl_frame_l.
Qed.

Lemma himpl_frame_lr : forall H1 H1' H2 H2',
  H1 ==> H1' ->
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1' \* H2').
Proof using.
  introv M1 M2. applys himpl_trans. applys~ himpl_frame_l M1. applys~ himpl_frame_r.
Qed.

Lemma himpl_hstar_trans_l : forall H1 H2 H3 H4,
  H1 ==> H2 ->
  H2 \* H3 ==> H4 ->
  H1 \* H3 ==> H4.
Proof using.
  introv M1 M2. applys himpl_trans M2. applys himpl_frame_l M1.
Qed.

Lemma himpl_hstar_trans_r : forall H1 H2 H3 H4,
  H1 ==> H2 ->
  H3 \* H2 ==> H4 ->
  H3 \* H1 ==> H4.
Proof using.
  introv M1 M2. applys himpl_trans M2. applys himpl_frame_r M1.
Qed.

(* ----------------------------------------------------------------- *)
(** ***  Properties of [hpure] *)

Lemma hpure_intro : forall P,
  P ->
  \[P] Fmap.empty.
Proof using. introv M. exists M. unfolds*. Qed.

Lemma hpure_inv : forall P h,
  \[P] h ->
  P /\ h = Fmap.empty.
Proof using. introv (p&M). split~. Qed.

Lemma hstar_hpure_l : forall P H h,
  (\[P] \* H) h = (P /\ H h).
Proof using.
  intros. apply prop_ext. unfold hpure.
  rewrite hstar_hexists. rewrite* hstar_hempty_l.
  iff (p&M) (p&M). { split~. } { exists~ p. }
Qed.

Lemma hstar_hpure_r : forall P H h,
  (H \* \[P]) h = (H h /\ P).
Proof using.
  intros. rewrite hstar_comm. rewrite hstar_hpure_l. apply* prop_ext.
Qed.

Lemma himpl_hstar_hpure_r : forall P H H',
  P ->
  (H ==> H') ->
  H ==> (\[P] \* H').
Proof using. introv HP W. intros h K. rewrite* hstar_hpure_l. Qed.

Lemma hpure_inv_hempty : forall P h,
  \[P] h ->
  P /\ \[] h.
Proof using.
  introv M. rewrite <- hstar_hpure_l. rewrite~ hstar_hempty_r.
Qed.

Lemma hpure_intro_hempty : forall P h,
  \[] h ->
  P ->
  \[P] h.
Proof using.
  introv M N. rewrite <- (hstar_hempty_l \[P]). rewrite~ hstar_hpure_r.
Qed.

Lemma himpl_hempty_hpure : forall P,
  P ->
  \[] ==> \[P].
Proof using. introv HP. intros h Hh. applys* hpure_intro_hempty. Qed.

Lemma himpl_hstar_hpure_l : forall P H H',
  (P -> H ==> H') ->
  (\[P] \* H) ==> H'.
Proof using.
  introv W Hh. rewrite hstar_hpure_l in Hh. applys* W.
Qed.

Lemma hempty_eq_hpure_true :
  \[] = \[True].
Proof using.
  applys himpl_antisym; intros h M.
  { applys* hpure_intro_hempty. }
  { forwards*: hpure_inv_hempty M. }
Qed.

Lemma hfalse_hstar_any : forall H,
  \[False] \* H = \[False].
Proof using.
  intros. applys himpl_antisym; intros h; rewrite hstar_hpure_l; intros M.
  { false*. } { lets: hpure_inv_hempty M. false*. }
Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hexists] *)

Lemma hexists_intro : forall A (x:A) (J:A->hprop) h,
  J x h ->
  (hexists J) h.
Proof using. intros. exists~ x. Qed.

Lemma hexists_inv : forall A (J:A->hprop) h,
  (hexists J) h ->
  exists x, J x h.
Proof using. intros. destruct H as [x H]. exists~ x. Qed.

Lemma himpl_hexists_l : forall A H (J:A->hprop),
  (forall x, J x ==> H) ->
  (hexists J) ==> H.
Proof using. introv W. intros h (x&Hh). applys* W. Qed.

Lemma himpl_hexists_r : forall A (x:A) H J,
  (H ==> J x) ->
  H ==> (hexists J).
Proof using. introv W. intros h. exists x. apply~ W. Qed.

Lemma himpl_hexists : forall A (J1 J2:A->hprop),
  J1 ===> J2 ->
  hexists J1 ==> hexists J2.
Proof using.
  introv W. applys himpl_hexists_l. intros x. applys himpl_hexists_r W.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hforall] *)

Lemma hforall_intro : forall A (J:A->hprop) h,
  (forall x, J x h) ->
  (hforall J) h.
Proof using. introv M. applys* M. Qed.

Lemma hforall_inv : forall A (J:A->hprop) h,
  (hforall J) h ->
  forall x, J x h.
Proof using. introv M. applys* M. Qed.

Lemma himpl_hforall_r : forall A (J:A->hprop) H,
  (forall x, H ==> J x) ->
  H ==> (hforall J).
Proof using. introv M. intros h Hh x. apply~ M. Qed.

Lemma himpl_hforall_l : forall A x (J:A->hprop) H,
  (J x ==> H) ->
  (hforall J) ==> H.
Proof using. introv M. intros h Hh. apply~ M. Qed.

Lemma hforall_specialize : forall A (x:A) (J:A->hprop),
  (hforall J) ==> (J x).
Proof using. intros. applys* himpl_hforall_l x. Qed.

Lemma himpl_hforall : forall A (J1 J2:A->hprop),
  J1 ===> J2 ->
  hforall J1 ==> hforall J2.
Proof using.
  introv W. applys himpl_hforall_r. intros x. applys himpl_hforall_l W.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hwand] *)

Lemma hwand_equiv : forall H0 H1 H2,
  (H0 ==> H1 \-* H2) <-> (H1 \* H0 ==> H2).
Proof using.
  unfold hwand. iff M.
  { rewrite hstar_comm. applys himpl_hstar_trans_l (rm M).
    rewrite hstar_hexists. applys himpl_hexists_l. intros H.
    rewrite (hstar_comm H). rewrite hstar_assoc.
    rewrite (hstar_comm H H1). applys~ himpl_hstar_hpure_l. }
  { applys himpl_hexists_r H0.
    rewrite <- (hstar_hempty_r H0) at 1.
    applys himpl_frame_r. applys himpl_hempty_hpure M. }
Qed.

Lemma himpl_hwand_r : forall H1 H2 H3,
  H2 \* H1 ==> H3 ->
  H1 ==> (H2 \-* H3).
Proof using. introv M. rewrite~ hwand_equiv. Qed.

Lemma himpl_hwand_r_inv : forall H1 H2 H3,
  H1 ==> (H2 \-* H3) ->
  H2 \* H1 ==> H3.
Proof using. introv M. rewrite~ <- hwand_equiv. Qed.

Lemma hwand_cancel : forall H1 H2,
  H1 \* (H1 \-* H2) ==> H2.
Proof using. intros. applys himpl_hwand_r_inv. applys himpl_refl. Qed.

Arguments hwand_cancel : clear implicits.

Lemma himpl_hempty_hwand_same : forall H,
  \[] ==> (H \-* H).
Proof using. intros. apply himpl_hwand_r. rewrite~ hstar_hempty_r. Qed.

Lemma hwand_hempty_l : forall H,
  (\[] \-* H) = H.
Proof using.
  intros. applys himpl_antisym.
  { rewrite <- hstar_hempty_l at 1. applys hwand_cancel. }
  { rewrite hwand_equiv. rewrite~ hstar_hempty_l. }
Qed.

Lemma hwand_hpure_l : forall P H,
  P ->
  (\[P] \-* H) = H.
Proof using.
  introv HP. applys himpl_antisym.
  { lets K: hwand_cancel \[P] H. applys himpl_trans K.
    applys* himpl_hstar_hpure_r. }
  { rewrite hwand_equiv. applys* himpl_hstar_hpure_l. }
Qed.

Lemma hwand_curry : forall H1 H2 H3,
  (H1 \* H2) \-* H3 ==> H1 \-* (H2 \-* H3).
Proof using.
  intros. apply himpl_hwand_r. apply himpl_hwand_r.
  rewrite <- hstar_assoc. rewrite (hstar_comm H1 H2).
  applys hwand_cancel.
Qed.

Lemma hwand_uncurry : forall H1 H2 H3,
  H1 \-* (H2 \-* H3) ==> (H1 \* H2) \-* H3.
Proof using.
  intros. rewrite hwand_equiv. rewrite (hstar_comm H1 H2).
  rewrite hstar_assoc. applys himpl_hstar_trans_r.
  { applys hwand_cancel. } { applys hwand_cancel. }
Qed.

Lemma hwand_curry_eq : forall H1 H2 H3,
  (H1 \* H2) \-* H3 = H1 \-* (H2 \-* H3).
Proof using.
  intros. applys himpl_antisym.
  { applys hwand_curry. }
  { applys hwand_uncurry. }
Qed.

Lemma hwand_inv : forall h1 h2 H1 H2,
  (H1 \-* H2) h2 ->
  H1 h1 ->
  Fmap.disjoint h1 h2 ->
  H2 (h1 \u h2).
Proof using.
  introv M2 M1 D. unfolds hwand. lets (H0&M3): hexists_inv M2.
  lets (h0&h3&P1&P3&D'&U): hstar_inv M3. lets (P4&E3): hpure_inv P3.
  subst h2 h3. rewrite union_empty_r in *. applys P4. applys* hstar_intro.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of qwand *)

Lemma qwand_equiv : forall H A (Q1 Q2:A->hprop),
  H ==> (Q1 \--* Q2) <-> (Q1 \*+ H) ===> Q2.
Proof using.
  unfold qwand. iff M.
  { intros x. rewrite hstar_comm. applys himpl_hstar_trans_l (rm M).
    applys himpl_trans. applys hstar_hforall. simpl.
    applys himpl_hforall_l x. rewrite hstar_comm. applys hwand_cancel. }
  { applys himpl_hforall_r. intros x. rewrite* hwand_equiv. }
Qed.

Lemma qwand_cancel : forall A (Q1 Q2:A->hprop),
  Q1 \*+ (Q1 \--* Q2) ===> Q2.
Proof using. intros. rewrite <- qwand_equiv. applys qimpl_refl. Qed.

Lemma himpl_qwand_r : forall A (Q1 Q2:A->hprop) H,
  Q1 \*+ H ===> Q2 ->
  H ==> (Q1 \--* Q2).
Proof using. introv M. rewrite~ qwand_equiv. Qed.

Arguments himpl_qwand_r [A].

Lemma qwand_specialize : forall A (x:A) (Q1 Q2:A->hprop),
  (Q1 \--* Q2) ==> (Q1 x \-* Q2 x).
Proof using. intros. applys* himpl_hforall_l x. Qed.

Arguments qwand_specialize [ A ].

(* ----------------------------------------------------------------- *)
(** *** Properties of [htop] *)

Lemma htop_intro : forall h,
  \Top h.
Proof using. intros. exists~ (=h). Qed.

Lemma himpl_htop_r : forall H,
  H ==> \Top.
Proof using. intros. intros h Hh. applys* htop_intro. Qed.

Lemma htop_eq :
  \Top = (\exists H, H).
Proof using. auto. Qed.

Lemma hstar_htop_htop :
  \Top \* \Top = \Top.
Proof using.
  applys himpl_antisym.
  { applys himpl_htop_r. }
  { rewrite <- hstar_hempty_r at 1. applys himpl_frame_r. applys himpl_htop_r. }
Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hsingle] *)

Lemma hsingle_intro : forall p v,
  (p ~~> v) (Fmap.single p v).
Proof using. intros. hnfs*. Qed.

Lemma hsingle_inv: forall p v h,
  (p ~~> v) h ->
  h = Fmap.single p v.
Proof using. auto. Qed.

Lemma hstar_hsingle_same_loc : forall p w1 w2,
  (p ~~> w1) \* (p ~~> w2) ==> \[False].
Proof using.
  intros. unfold hsingle. intros h (h1&h2&E1&E2&D&E). false.
  subst. applys* Fmap.disjoint_single_single_same_inv.
Qed.

Arguments hstar_hsingle_same_loc : clear implicits.

(* ----------------------------------------------------------------- *)
(** *** Definition and Properties of [haffine] and [hgc] *)

Definition haffine (H:hprop) :=
  True.

Lemma haffine_hany : forall (H:hprop),
  haffine H.
Proof using. unfold haffine. auto. Qed.

Lemma haffine_hempty :
  haffine \[].
Proof using. applys haffine_hany. Qed.

Definition hgc := (* equivalent to [\exists H, \[haffine H] \* H] *)
  htop.

Notation "\GC" := (hgc) : hprop_scope.

Lemma haffine_hgc :
  haffine \GC.
Proof using. applys haffine_hany. Qed.

Lemma himpl_hgc_r : forall H,
  haffine H ->
  H ==> \GC.
Proof using. introv M. applys himpl_htop_r. Qed.

Lemma hstar_hgc_hgc :
  \GC \* \GC = \GC.
Proof using. applys hstar_htop_htop. Qed.

(* ----------------------------------------------------------------- *)
(** *** Functor Instantiation to Obtain [xsimpl] *)

End SepSimplArgs.

(** We are now ready to instantiate the functor that defines [xsimpl].
    Demos of [xsimpl] are presented in chapter [Himpl.v]. *)

Module Export HS := LibSepSimpl.XsimplSetup(SepSimplArgs).

Export SepSimplArgs.

(** From now on, all operators have opaque definitions. *)

Global Opaque hempty hpure hstar hsingle hexists hforall
              hwand qwand htop hgc haffine.

(** At this point, the tactic [xsimpl] is defined. There remains to customize
    the tactic so that it recognizes the predicate [p ~~> v] in a special way
    when performing simplifications. *)

(** The tactic [xsimpl_hook_hsingle p v] operates as part of [xsimpl].
    The specification that follows makes sense only in the context of the
    presentation of the invariants of [xsimpl] described in [LibSepSimpl.v].
    This tactic is invoked on goals of the form [Xsimpl (Hla, Hlw, Hlt) HR],
    where [Hla] is of the form [H1 \* .. \* Hn \* \[]]. The tactic
    [xsimpl_hook_hsingle p v] searches among the [Hi] for a heap predicate
    of the form [p ~~> v']. If it finds one, it moves this [Hi] to the front,
    just before [H1]. Then, it cancels it out with the [p ~~> v] that occurs
    in [HR]. Otherwise, the tactic fails. *)

Ltac xsimpl_hook_hsingle p :=
  xsimpl_pick_st ltac:(fun H' =>
    match H' with (hsingle p ?v') =>
      constr:(true) end);
  apply xsimpl_lr_cancel_eq;
  [ xsimpl_lr_cancel_eq_repr_post tt | ].

(** The tactic [xsimpl_hook] handles cancellation of heap predicates of the
    form [p ~~> v]. It forces their cancellation against heap predicates of
    the form [p ~~> w], by asserting the equality [v = w]. Note: this tactic
    is later refined to also handle records. *)

Ltac xsimpl_hook H ::=
  match H with
  | hsingle ?p ?v => xsimpl_hook_hsingle p
  end.

(** One last hack is to improve the [math] tactic so that it is able
    to handle the [val_int] coercion in goals and hypotheses of the
    form [val_int ?n = val_int ?m], and so that it is able to process
    the well-founded relations [dowto] and [upto] for induction on
    integers. *)

(* Ltac math_0 ::=
  unfolds downto, upto;
  repeat match goal with
  | |- val_int _ = val_int _ => fequal
  | H: val_int _ = val_int _ |- _ => inverts H
  end. *)

(* end LibSepReference *)

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

  | s_req env p h1 h2 r
    (H: exists h3, h1 = Fmap.union h2 h3 /\ Fmap.disjoint h2 h3 /\ p h3) :
    satisfies env (req p) h1 h2 r

  | s_ens env q h1 h2 r
    (H: exists v h3, r = norm v /\ q v h3 /\ h2 = Fmap.union h1 h3 /\ Fmap.disjoint h1 h3) :
    satisfies env (ens q) h1 h2 r

  | s_seq env f1 f2 h1 h2 r
    (H: exists h3 r1, satisfies env f1 h1 h3 r1 /\ satisfies env f2 h3 h2 r) : satisfies env (seq f1 f2) h1 h2 r

  (* | s_ffex (a:Type) (f:a->flow) : forall env h1 h2 r x, *)
  | s_ffex env f h1 h2 r
    (H: exists v, satisfies env (f v) h1 h2 r) :
    satisfies env (ffex f) h1 h2 r

  | s_unk env fn h1 h2 r f x
    (He: env fn = Some f)
    (Hr: satisfies env (f x r) h1 h2 (norm r)) :
    satisfies env (unk fn x r) h1 h2 (norm r)

  | s_disj_l env h1 h2 r f1 f2
    (H: satisfies env f1 h1 h2 r) :
    satisfies env (disj f1 f2) h1 h2 r

  | s_disj_r env h1 h2 r f1 f2
    (H: satisfies env f2 h1 h2 r) :
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

Definition empty := ens (fun r => \[True]).

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
(* Ltac hstep :=
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
  end. *)


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

  Example ex3_req_ret: flow_res f2 (vint 2).
  Proof.
    unfold flow_res.
    exists empty_heap.
    exists empty_heap.
    exists empty_env.
    unfold f2.
    apply (s_ffex).
    eexists.
    constructor.
    eexists.
    intuition.
    fmap_eq.
  Qed.

  Definition f4 : flow := empty ;; fex (fun r => unk "f" (vint 1) r).
  Definition f4_env : env := eupdate "f" (fun _ r => ens (fun r1 => \[r = vint 2])) empty_env.

  (* has to be 2 *)
  Example ex5_f_ret: flow_res f4 (vint 2).
  Proof.
    unfold flow_res.
    exists empty_heap. exists empty_heap. exists f4_env.
    unfold f4.
    (* fintro. *)
    constructor. exists empty_heap. exists (norm (vint 7)). intuition.
    (* fintro. *)
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
    apply eupdate_same.
    constructor.
    exists (vint 2).
    exists empty_heap.
    intuition.

    apply hpure_intro_hempty.
    apply hempty_intro.
    reflexivity.
    fmap_eq.
  Qed.

  Example ex4: forall h, satisfies (eupdate "f" (fun x r1 => ens (fun r => \[r1 = r /\ r = x])) empty_env) f4 h h (norm (vint 1)).
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

  Definition foldr :=
  ens (fun _ => \[True]) ;;
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
    forward (pval n) (ens (fun res => \[res = n]))

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