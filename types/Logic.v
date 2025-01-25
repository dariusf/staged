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

(** * Programs *)
Definition var : Type := string.
Definition var_eq := String.string_dec.

Definition loc := nat.

Inductive tag :=
  | tag_int
  | tag_bool
  | tag_str
  | tag_list
  | tag_nil
  | tag_cons.

Inductive val :=
  | vunit : val
  | vint : Z -> val
  | vfun : var -> expr -> val
  | vfix : var -> var -> expr -> val
  | vloc : loc -> val
  | vstr : string -> val
  | vbool : bool -> val
  | vconstr0 : string -> val
  | vconstr1 : string -> val -> val
  | vconstr2 : string -> val -> val -> val
  | verr : val
  | vabort : val

with expr : Type :=
  | pvar (x: var)
  | pval (v: val)
  | plet (x: var) (e1 e2: expr)
  | pif (b: expr) (e1: expr) (e2: expr)
  | papp (x: expr) (a: expr)
  | pfun (x: var) (e: expr)
  | pfix (f: var) (x: var) (e: expr)
  | pfst (t: expr)
  | psnd (t: expr)
  | pminus (x y: expr)
  | padd (x y: expr)
  | ptypetest (tag:tag) (e: expr)
  | passert (b: expr)
  | pref (v: expr)
  | pderef (v: expr)
  | passign (x: expr) (v: expr)
  .

Implicit Types e: expr.
Implicit Types r v: val.

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
  | ptypetest tag e => ptypetest tag e
  | plet x t1 t2 => plet x (aux t1) (if_y_eq x t2 (aux t2))
  | pif t0 t1 t2 => pif t0 (aux t1) (aux t2)
  end.

Definition vcons a b : val := vconstr2 "cons" a b.
Definition vnil : val := vconstr0 "nil".

Definition interpret_tag tag v : bool :=
  match tag, v with
  | tag_int, vint _ => true
  | tag_bool, vbool _ => true
  | tag_str, vstr _ => true
  | tag_nil, vconstr0 "nil" => true
  | tag_cons, vconstr2 "cons" _ _ => true
  | tag_list, vconstr0 "nil" => true
  | tag_list, vconstr2 "cons" _ _ => true
  | _, _ => false
  end.

(* [(Integer) i] *)
Definition ptypecast tag (v:val) :=
  plet "x" (ptypetest tag (pval v))
    (pif (pvar "x") (pval v) (pval vabort)).

Fixpoint pmatch v (cases: list (tag * expr)) : expr :=
  match cases with
  | nil => pval vabort
  | (tag, e) :: cs =>
    plet "x" (ptypetest tag (pval v))
      (pif (pvar "x") e (pmatch v cs))
  end.

Definition pletcast x tag e1 e2 : expr :=
  (plet x e1
    (plet "xb" (ptypetest tag (pvar x))
      (pif (pvar "xb") e2 (pval vabort)))).

Module Val.
  Definition value := val.
End Val.

Module Export Heap := HeapF.HeapSetup Val.

Implicit Types h: heap.

Inductive bigstep : heap -> expr -> heap -> val -> Prop :=
  | eval_pval : forall h v,
    bigstep h (pval v) h v

  (* there is no var rule *)

  | eval_plet : forall h1 h3 h2 x e1 e2 v Re,
    bigstep h1 e1 h3 v ->
    bigstep h3 (subst x v e2) h2 Re ->
    bigstep h1 (plet x e1 e2) h2 Re

  | eval_padd : forall h x y,
    bigstep h (padd (pval (vint x)) (pval (vint y))) h (vint (x + y))

  | eval_pminus : forall h x y,
    bigstep h (pminus (pval (vint x)) (pval (vint y))) h (vint (x - y))

  | eval_pfst1 : forall x h v,
    bigstep h (pfst (pval (vconstr1 x v))) h v

  | eval_pfst2 : forall x h v1 v2,
    bigstep h (pfst (pval (vconstr2 x v1 v2))) h v1

  | eval_psnd2 : forall x h v1 v2,
    bigstep h (psnd (pval (vconstr2 x v1 v2))) h v2

  | eval_pfun : forall h x e,
    bigstep h (pfun x e) h (vfun x e)

  | eval_pfix : forall h x e xf,
    bigstep h (pfix xf x e) h (vfix xf x e)

  | eval_app_fun : forall v1 v2 h x e Re,
    v1 = vfun x e ->
    bigstep h (subst x v2 e) h Re ->
    bigstep h (papp (pval v1) (pval v2)) h Re

  | eval_app_fix : forall v1 v2 h x e Re xf,
    v1 = vfix xf x e ->
    bigstep h (subst x v2 (subst xf v1 e)) h Re ->
    bigstep h (papp (pval v1) (pval v2)) h Re

  | eval_pif_true : forall h1 h2 Re e1 e2,
    bigstep h1 e1 h2 Re ->
    bigstep h1 (pif (pval (vbool true)) e1 e2) h2 Re

  | eval_pif_false : forall h1 h2 Re e1 e2,
    bigstep h1 e2 h2 Re ->
    bigstep h1 (pif (pval (vbool false)) e1 e2) h2 Re

  | eval_pref : forall h v p,
    ~ Fmap.indom h p ->
    bigstep h (pref (pval v)) (Fmap.update h p v) (vloc p)

  | eval_pderef : forall h p,
    Fmap.indom h p ->
    bigstep h (pderef (pval (vloc p))) h (Fmap.read h p)

  | eval_passign : forall h p v,
    Fmap.indom h p ->
    bigstep h (passign (pval (vloc p)) (pval v)) (Fmap.update h p v) vunit

  | eval_passert : forall h,
    bigstep h (passert (pval (vbool true))) h vunit

  | eval_ptypetest : forall h tag v,
    bigstep h (ptypetest tag (pval v)) h (vbool (interpret_tag tag v))

  .

(** * Types *)
Definition type := val -> Prop.
Implicit Types t: type.

(* bot <: err <: t <: ok <: any <: top *)
(* abort <: top *)

Definition tsingle v1 : type := fun v => v = v1.
Definition terr : type := tsingle verr.
Definition tabort : type := tsingle vabort.

Definition ttop : type := fun _ => True.
Definition tbot : type := fun _ => False.
Definition tintersect t1 t2 : type := fun v => t1 v /\ t2 v.
Definition tunion t1 t2 : type := fun v => t1 v \/ t2 v.
Definition tnot t : type := fun v => not (t v).

Definition tint : type := tunion terr (fun v => exists i, v = vint i).
Definition tbool : type := tunion terr (fun v => exists b, v = vbool b).

Definition tforall A (f:A -> type) : type := fun v =>
  forall x:A, (f x) v.
Definition texists A (f:A -> type) : type := fun v =>
  exists x:A, (f x) v.

Declare Scope typ_scope.
Open Scope typ_scope.
Bind Scope typ_scope with type.

Notation "'∃' x1 .. xn , H" :=
  (texists (fun x1 => .. (texists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '∃' '/ '  x1  ..  xn , '/ '  H ']'") : typ_scope.

Notation "'∀' x1 .. xn , H" :=
  (tforall (fun x1 => .. (tforall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '∀' '/ '  x1  ..  xn , '/ '  H ']'") : typ_scope.

Definition tany : type := tnot tabort.

(** The type of finite lists. can be coinductive to be infinite.
  non-inductive recursive types are ignored for now. *)
Inductive tlist : type -> val -> Prop :=
  | tlist_err : forall t,
    tlist t verr
  | tlist_nil : forall t,
    tlist t vnil
  | tlist_cons : forall vh vt t,
    t vh ->
    tlist t vt ->
    tlist t (vcons vh vt).

Definition tnil : type := tunion terr (fun v => v = vnil).
Definition tcons : type :=
  tunion terr (fun v => forall v1 v2, v = vcons v1 v2).

(** Unary logical relation on expressions *)
Definition E t := fun e =>
  forall h1 h2 r, bigstep h1 e h2 r -> t r.

Definition tarrow t1 t2 : type := fun vf =>
  forall x e, vf = vfun x e ->
  forall v, t1 v ->
  E t2 (papp (pval (vfun x e)) (pval v)).

(** Dependent arrow *)
Definition tdarrow v t1 t2 : type := fun vf =>
  forall x e, vf = vfun x e ->
  t1 v ->
  E t2 (papp (pval (vfun x e)) (pval v)).

(** All values are of type top *)
Lemma top_intro: forall v,
  ttop v.
Proof.
  unfold ttop. jauto.
Qed.

Lemma bot_inv: forall v,
  not (tbot v).
Proof.
  jauto.
Qed.

(** * Subtyping *)
Definition subtype t1 t2 := forall v, t1 v -> t2 v.
Notation "t1 '<:' t2" := (subtype t1 t2) (at level 40).

Instance subtype_refl : Reflexive subtype.
Proof. unfold Reflexive, subtype. intros. auto. Qed.

Instance subtype_trans : Transitive subtype.
Proof. unfold Transitive, subtype. intros. auto. Qed.

Instance subtype_preorder : PreOrder subtype.
Proof. constructor. apply subtype_refl. apply subtype_trans. Qed.

Definition equiv t1 t2 := forall v, t1 v <-> t2 v.

Instance equiv_refl : Reflexive equiv.
Proof. unfold Reflexive, equiv. jauto. Qed.

Instance equiv_trans : Transitive equiv.
Proof. unfold Transitive, equiv. intros. split; rewrite H, H0; jauto. Qed.

Instance equiv_sym : Symmetric equiv.
Proof. unfold Symmetric, equiv. intros. split; rewrite H; jauto. Qed.

Instance equiv_equiv : Equivalence equiv.
Proof. constructor. apply equiv_refl. apply equiv_sym. apply equiv_trans. Qed.

Lemma function_variance: forall t1 t2 t3 t4,
  t3 <: t1 ->
  t2 <: t4 ->
  tarrow t1 t2 <: tarrow t3 t4.
Proof.
  unfold subtype, tarrow, E. intros.
  specializes H1 H2. clear H2.
  apply H0. clear H0.
  specializes H H3.
  specializes H1 H H4.
Qed.

(** The standard subsumption rule is a consequence of the semantic definition. *)
Lemma subsumption: forall t1 t2 v,
  t1 v -> t1 <: t2 -> t2 v.
Proof.
  unfold subtype. intros.
  eauto.
Qed.

Lemma subtype_bot: forall t,
  tbot <: t.
Proof.
  unfold tbot, subtype. intros. false.
Qed.

Lemma subtype_top: forall t,
  t <: ttop.
Proof.
  unfold ttop, subtype. constructor.
Qed.

(** top is the annihilator of union *)
Lemma tunion_ttop: forall t,
  equiv (tunion ttop t) ttop.
Proof.
  intros. iff H.
  { unfold ttop. eauto. }
  { unfold tunion, ttop. eauto. }
Qed.

Lemma tintersect_tbot: forall t,
  equiv (tintersect tbot t) tbot.
Proof.
  unfold tbot, tintersect. intros. iff H.
  { destr H. false. }
  { false. }
Qed.

Module Examples.

Definition id := vfun "x" (pvar "x").
Definition id_type1 : type := ∀ t, tarrow t t.
Definition id_type2 : type := ∀ v, tdarrow v ttop (tsingle v).

Lemma id_has_type1 : id_type1 id.
Proof.
  unfold id, id_type1.
  unfold tforall. intros.
  unfold tarrow. intros.
  unfold E. intros.
  injects H.
  inverts H1 as H1.
  { injects H1.
    inverts H6 as H6.
    assumption. (* this is the key step *) }
  { inverts H1 as H1. }
Qed.

Lemma id_has_type2 : id_type2 id.
Proof.
  unfold id, id_type2.
  unfold tforall. intros.
  unfold tdarrow. intros.
  unfold tsingle, E. intros.
  injects H.
  inverts H1 as H1.
  { injects H1.
    inverts H6 as H6.
    reflexivity. (* note the difference! *) }
  { inverts H1 as H1. }
Qed.

End Examples.

(** * Variance and mutability *)

(** These two disjuncts are included in the infinite set of disjuncts of the supertypes of t1 *)
Lemma contra_disjuncts: forall t1 v,
  (tunion ttop t1) v -> (exists t2, t1 <: t2 /\ t2 v).
Proof.
  unfold tunion, ttop, subtype.
  intros.
  destruct H.
  - exists ttop. jauto.
  - exists t1. jauto.
Qed.

Lemma contra_is_top: forall t1 v,
  ttop v <-> (exists t2, t1 <: t2 /\ t2 v).
Proof.
  iff H.
  { exists ttop. hint subtype_top. jauto. }
  { destr H. apply top_intro. }
Qed.

Definition tcov : type -> type := fun t1 v =>
  exists t2, t2 <: t1 -> t2 v.
Definition tcontra : type -> type := fun t1 v =>
  forall t2, t1 <: t2 -> t2 v.
Definition tinv : type -> type := fun t1 v => t1 v.
Definition twild : type := ttop.

Example ex_list: (tlist tint) (vcons (vint 1) (vcons (vint 2) vnil)).
Proof.
  apply tlist_cons.
  unfold tint.
  unfold tunion. right.
  eexists. reflexivity.
  apply tlist_cons.
  unfold tint.
  unfold tunion. right.
  eexists. reflexivity.
  apply tlist_nil.
Qed.

Lemma subtype_cov: forall t,
  t <: tcov t.
Proof.
  unfold subtype, tcov. intros.
  eauto.
Qed.

(* Lemma list_covariant: forall t,
  tlist t <: tlist (tcov t).
Proof.
  unfold subtype. intros.
  induction H.
  - apply tlist_nil.
  - apply tlist_cons.
    { unfold tcov. intros. exists t. auto. }
    { assumption. }
Qed. *)

(* Lemma list_contravariant: forall t,
  tlist (tcontra t) <: tlist t.
Proof.
  unfold subtype. intros.
  remember (tcontra t) as t1 eqn:H1.
  induction H.
  - apply tlist_nil.
  - apply tlist_cons.
    { subst. unfold tcontra in H.
      specializes* IHtlist.
      apply H.
      unfold subtype.
      auto. }
    { subst.
      specializes* IHtlist. }
Qed. *)

(** * Program specifications *)

(* Even though we use hprop, for pure logic we can just wrap everything in \[P] *)
Definition postcond := val -> hprop.

Implicit Types H: hprop.
Implicit Types Q: postcond.

Inductive spec :=
  | req : hprop -> spec -> spec
  | ens : postcond -> spec
  | sexists : forall A, (A -> spec) -> spec
  | sforall : forall A, (A -> spec) -> spec
  | sintersect : spec -> spec -> spec.

Implicit Types s: spec.

Declare Scope spec_scope.
Open Scope spec_scope.
Bind Scope spec_scope with spec.

Notation "'∃' x1 .. xn , H" :=
  (texists (fun x1 => .. (texists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '∃' '/ '  x1  ..  xn , '/ '  H ']'") : spec_scope.

Notation "'∀' x1 .. xn , H" :=
  (tforall (fun x1 => .. (tforall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '∀' '/ '  x1  ..  xn , '/ '  H ']'") : spec_scope.

Inductive spec_satisfies : heap -> heap -> val -> spec -> Prop :=

  | s_req : forall h1 h2 r s H,
    (forall hp hr,
      H hp ->
      h1 = Fmap.union hr hp ->
      Fmap.disjoint hr hp ->
      spec_satisfies hr h2 r s) ->
    spec_satisfies h1 h2 r (req H s)

  | s_ens : forall Q h1 h2 h3 r,
    Q r h3 ->
    h2 = Fmap.union h1 h3 ->
    Fmap.disjoint h1 h3 ->
    spec_satisfies h1 h2 r (ens Q)

  | s_ex : forall h1 h2 r (A:Type) (f:A->spec),
    (exists (b:A), spec_satisfies h1 h2 r (f b)) ->
    spec_satisfies h1 h2 r (@sexists A f)

  | s_all : forall h1 h2 r (A:Type) (f:A->spec),
    (forall (b:A), spec_satisfies h1 h2 r (f b)) ->
    spec_satisfies h1 h2 r (@sforall A f)

  | s_intersect : forall h1 h2 r s1 s2,
    spec_satisfies h1 h2 r s1 ->
    spec_satisfies h1 h2 r s2 ->
    spec_satisfies h1 h2 r (sintersect s1 s2)
  .

Definition subsumes s1 s2 := forall h1 h2 r,
  spec_satisfies h1 h2 r s1 ->
  spec_satisfies h1 h2 r s2.

Definition ens_ H := ens (fun r => \[r = vunit] \* H).
Definition empty := ens_ \[True].
Notation req_ H := (req H empty).

(*
  case v of
  | p1 => s1
  | p2 => s2
    
  is written as

  intersect
    (req (p1 v) (ens s1))
    (req (p2 v /\ not (p1 v)) (ens s2))
*)

Fixpoint scase_ P v (cases:list ((val -> Prop) * spec)) : spec :=
  match cases with
  | nil => empty
  | (p, s) :: cs =>
    sintersect (req \[p v /\ not P] s) (scase_ (p v /\ P) v cs)
  end.

Definition scase v (cases:list ((val -> Prop) * spec)) : spec :=
  scase_ True v cases.

(** * Introduction/inversion lemmas, and other properties of specs *)
Lemma req_pure_intro : forall h1 h2 r P s,
  (P -> spec_satisfies h1 h2 r s) ->
  spec_satisfies h1 h2 r (req \[P] s).
Proof.
  intros.
  apply s_req. intros.
  hinv H0. subst. rew_fmap.
  apply* H.
Qed.

Lemma empty_intro: forall h,
  spec_satisfies h h vunit empty.
Proof.
  unfold empty. intros. eapply s_ens.
  hintro. splits*. hintro. all: auto.
Qed.

(** * Semantics of program specs/triples *)
Definition program_has_spec (s:spec) (e:expr) :=
  forall h1 h2 r,
    bigstep h1 e h2 r ->
    spec_satisfies h1 h2 r s.

Definition triple H Q e :=
  forall h1 h2 r,
    H h1 -> bigstep h1 e h2 r -> Q r h2.

Lemma triple_subsumption: forall H1 H2 Q1 Q2 e,
  triple H2 Q2 e ->
  H1 ==> H2 ->
  Q2 ===> Q1 ->
  triple H1 Q1 e.
Proof.
  unfold triple. intros.
  apply H3.
  eauto.
Qed.

(* Is this rule still true in separation logic? *)
Lemma stronger_triple_subsumption: forall H1 H2 Q1 Q2 e,
  triple H2 Q2 e ->
  H1 ==> H2 ->
  Q2 \*+ H1 ===> Q1 ->
  triple H1 Q1 e.
Proof.
  unfold triple. intros.
  apply H3.
  specializes H H5.
  eauto.
Abort.

(** * Specs for program constructs *)
Lemma program_has_spec_assert: forall b,
  program_has_spec (req_ \[b = true])
   (passert (pval (vbool b))).
Proof.
  intros.
  unfold program_has_spec. introv Hb.
  inverts Hb as Hb.
  apply req_pure_intro. intros.
  apply empty_intro.
Qed.

(*

TODO

- variance: are the definitions of covariance and contravariance reasonable?
- interesting examples

*)