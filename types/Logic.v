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

(* Fixpoint val_dec (x y : val) : { x = y } + { x <> y }
with expr_dec (x y : expr) : { x = y } + { x <> y }.
Proof.
  hint Z.eq_dec, var_eq, Nat.eq_dec, Bool.bool_dec.
  hint string_dec.
  intros. decide equality; jauto. apply expr_dec.
Qed.
Defined. *)

Fixpoint subst (y:var) (w:val) (e:expr) : expr :=
  let aux t := subst y w t in
  let if_y_eq x t1 t2 := if var_eq x y then t1 else t2 in
  match e with
  | pval v => pval v
  | padd e1 e2 => padd (aux e1) (aux e2)
  | pminus e1 e2 => pminus (aux e1) (aux e2)
  | pfst e => pfst (aux e)
  | psnd e => psnd (aux e)
  | pvar x => if_y_eq x (pval w) e
  | passert e => passert (aux e)
  | pderef e => pderef (aux e)
  | passign e1 e2 => passign (aux e1) (aux e2)
  | pref e => pref (aux e)
  | pfun x t1 => pfun x (if_y_eq x t1 (aux t1))
  | pfix f x t1 => pfix f x (if_y_eq f t1 (if_y_eq x t1 (aux t1)))
  | papp e1 e2 => papp (aux e1) (aux e2)
  | ptypetest tag e => ptypetest tag (aux e)
  | plet x t1 t2 => plet x (aux t1) (if_y_eq x t2 (aux t2))
  | pif t0 t1 t2 => pif (aux t0) (aux t1) (aux t2)
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
  plet "_ok" (ptypetest tag (pval v))
    (pif (pvar "_ok") (pval v) (pval vabort)).

Fixpoint pmatch_ x (cases: list (tag * expr)) : expr :=
  match cases with
  | nil => pval vabort
  | (tag, eb) :: cs =>
    plet "_b" (ptypetest tag x)
      (pif (pvar "_b") eb (pmatch_ x cs))
  end.

Definition pmatch e (cases: list (tag * expr)) : expr :=
  (plet "_scr" e (pmatch_ (pvar "_scr") cases)).

Definition pletcast x tag e1 e2 : expr :=
  (plet x e1
    (plet "_xb" (ptypetest tag (pvar x))
      (pif (pvar "_xb") e2 (pval vabort)))).

Module Val.
  Definition value := val.
End Val.

Module Export Heap := HeapF.HeapSetup Val.

Definition empty_heap : heap := Fmap.empty.

Implicit Types h: heap.

Inductive bigstep : heap -> expr -> heap -> val -> Prop :=
  | eval_pval : forall h v,
    bigstep h (pval v) h v

  (* there is no var rule *)

  | eval_plet : forall h1 h3 h2 x e1 e2 v Re,
    bigstep h1 e1 h3 v -> v <> vabort ->
    bigstep h3 (subst x v e2) h2 Re ->
    bigstep h1 (plet x e1 e2) h2 Re

  | eval_plet_abort : forall h1 h2 x e1 e2 v,
    bigstep h1 e1 h2 v -> v = vabort ->
    (* bigstep h2 (pval v) h2 v -> *)
    bigstep h1 (plet x e1 e2) h2 v

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
Definition tcons t1 t2 : type :=
  tunion terr (fun v => forall v1 v2, v = vcons v1 v2 /\ t1 v /\ t2 v2).


(* This nonconstructive definition is not useful *)
Definition tany_nonconstructive : type := tnot tabort.
Definition tany : type :=
  ∀ t t1 t2,
    tunion tint (tunion tbool (tunion (tlist t) (tunion (tcons t1 t2) tnil))).

(** Unary logical relation on expressions *)
Notation E t := (fun e =>
  forall h1 h2 r, bigstep h1 e h2 r -> t r).

Notation is_fn vf :=
  (exists xf x e, vf = vfun x e \/ vf = vfix xf x e).

Definition tarrow t1 t2 : type := fun vf =>
  is_fn vf ->
  forall v, t1 v ->
  E t2 (papp (pval vf) (pval v)).

(** Dependent arrow *)
Definition tdarrow v t1 t2 : type := fun vf =>
  is_fn vf ->
  t1 v ->
  E t2 (papp (pval vf) (pval v)).

(** All values are of type top *)
Lemma ttop_intro: forall v,
  ttop v.
Proof.
  unfold ttop. jauto.
Qed.

Lemma tbot_inv: forall v,
  not (tbot v).
Proof.
  jauto.
Qed.

Lemma terr_intro:
  terr verr.
Proof.
  unfold terr, tsingle.
  reflexivity.
Qed.

Lemma tsingle_inv: forall v1 v2,
  tsingle v1 v2 -> v1 = v2.
Proof.
  unfold tsingle. intros.
  congruence.
Qed.

Lemma tsingle_intro: forall v,
  tsingle v v.
Proof.
  unfold tsingle.
  congruence.
Qed.

Lemma tabort_intro:
  tabort vabort.
Proof.
  unfold tabort.
  apply tsingle_intro.
Qed.

Lemma tint_intro: forall n,
  tint (vint n).
Proof.
  unfold tint.
  right.
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

(** * Properties of subtyping *)
Lemma function_variance: forall t1 t2 t3 t4,
  t3 <: t1 ->
  t2 <: t4 ->
  tarrow t1 t2 <: tarrow t3 t4.
Proof.
  unfold subtype, tarrow. intros.
  specializes H H3.
  specializes H1 H2 H h1.
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

Lemma subtype_terr_tany:
  terr <: tany.
Proof.
  unfold terr, tany, subtype. intros.
  unfold tforall. intros.
  unfold tunion. left.
  unfold tint. left.
  assumption.
Qed.

Lemma subtype_terr_tlist: forall t,
  terr <: tlist t.
Proof.
  unfold terr, subtype. intros.
  apply tsingle_inv in H. subst v.
  apply tlist_err.
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
  inverts H1 as H1.
  { injects H1.
    inverts H7 as H7.
    assumption. (* this is the key step *) }
  { inverts H1 as H1. }
Qed.

Lemma id_has_type2 : id_type2 id.
Proof.
  unfold id, id_type2.
  unfold tforall. intros.
  unfold tdarrow. intros.
  unfold tsingle. intros.
  (* injects H. *)
  inverts H1 as H1.
  - injects H1.
    inverts H7 as H7.
    reflexivity. (* note the difference! *)
  - inverts H1 as H1.
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
  { destr H. apply ttop_intro. }
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

Implicit Types P: Prop.
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

(** * Semantics of program specs *)
Definition program_has_spec (s:spec) (e:expr) :=
  forall h1 h2 r,
    bigstep h1 e h2 r ->
    spec_satisfies h1 h2 r s.

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

(** * Semantics of triples *)
Definition triple H Q e :=
  forall h1, H h1 ->
  forall h2 r, bigstep h1 e h2 r -> Q r h2.

Definition pure_triple P (Q:val->Prop) e :=
  P -> forall r, bigstep empty_heap e empty_heap r -> Q r.

(** * Relation to pure triples *)
Definition triple_to_pure_triple : forall P (Q:val->Prop) e,
  triple \[P] (fun r => \[Q r]) e ->
  pure_triple P Q e.
Proof.
  unfold pure_triple, triple. intros.
  specializes H empty_heap.
  forward H. hintro. assumption.
  specializes H H1.
  hinv H.
  assumption.
Qed.

Definition pure_triple_to_triple : forall P (Q:val->Prop) e,
  pure_triple P Q e ->
  triple \[P] (fun r => \[Q r]) e.
Proof.
  unfold pure_triple, triple. intros.
  hinv H0. subst h1.
  specializes H H0 r.
  (* for arbitrary e, we cannot ensure that the heap after execution is empty. pure triples only describe programs which don't use heap operations. *)
Abort.

(** * Structural rules *)
(** Triple subsumption, or the rule of consequence *)
Lemma triple_conseq: forall H1 H2 Q1 Q2 e,
  triple H1 Q1 e ->
  H2 ==> H1 ->
  Q1 ===> Q2 ->
  triple H2 Q2 e.
Proof.
  unfold triple. intros.
  specializes H0 H4.
  specializes H H0 H5.
  specializes~ H3 H.
Qed.

(** This rule is only true in Hoare logic. In separation logic it requires frame inference, which the semantic [==>] does not do. *)
Lemma stronger_triple_subsumption: forall P1 P2 (Q1 Q2:val->Prop) e,
  pure_triple P2 Q2 e ->
  (P1 -> P2) ->
  (forall r, Q2 r /\ P1 -> Q1 r) ->
  pure_triple P1 Q1 e.
Proof.
  unfold pure_triple. intros.
  specializes H0 H2.
  specializes H H0 H3.
Qed.

Lemma triple_extract_pure_r: forall H P Q e,
  (P -> triple H Q e) ->
  triple (H \* \[P]) Q e.
Proof.
  unfold triple. intros.
  hinv H1. hinv H3. subst. rew_fmap *.
Qed.

(** * Triples for program constructs *)
Lemma triple_val: forall H v,
  triple H (fun r => H \* \[r = v])
   (pval v).
Proof.
  unfold triple. intros.
  hintro.
  inverts H1 as H1.
  splits*.
Qed.

Lemma triple_err: forall H v,
  triple H (fun r => H \* \[r = verr])
   (pval verr).
Proof.
  intros. applys triple_val verr.
Qed.

Lemma triple_abort: forall H v,
  triple H (fun r => H \* \[r = vabort])
   (pval vabort).
Proof.
  intros. applys triple_val vabort.
Qed.

(** Why is the statement of this rule this way?

  In the value case, the use of Q1 in the precondition allows us to know what value e1 returns.

  In the abort case, we don't have a triple, but still need a way to assume what e1 returns - hence the use of an entailment, to put the assumption back in positive position.

  Suppose we used an equality with Q2. As the equality is in negative position, we would then have to prove the equality, without knowledge of what e1 returns. *)
Lemma triple_plet: forall H Q1 Q2 x e1 e2,
  triple H Q1 e1 ->
  (forall v,
    v <> vabort ->
    triple (Q1 v) Q2 (subst x v e2)) ->
  (forall v,
    v = vabort ->
    (fun r => Q1 v \* \[r = vabort]) ===> Q2) ->
  triple H Q2 (plet x e1 e2).
Proof.
  unfold triple. intros.
  inverts H4 as H4.
  { specializes H0 H3 H4. }
  { clear H1.
    specializes H0 H3 H4.
    specializes H2 vabort.
    forward H2 by reflexivity.
    apply H2.
    hintro.
    splits*. }
Qed.

Lemma triple_pif_true: forall H Q e1 e2,
  triple H Q e1 ->
  triple H Q (pif (pval (vbool true)) e1 e2).
Proof.
  unfold triple. intros.
  inverts H2 as H2.
  eauto.
Qed.

Lemma triple_pif_false: forall H Q e1 e2,
  triple H Q e2 ->
  triple H Q (pif (pval (vbool false)) e1 e2).
Proof.
  unfold triple. intros.
  inverts H2 as H2.
  eauto.
Qed.

(** This combined rule also works *)
Lemma triple_pif: forall H Q e1 e2 (b:bool),
  (b = true -> triple H Q e1) ->
  (b = false -> triple H Q e2) ->
  triple H Q (pif (pval (vbool b)) e1 e2).
Proof.
  unfold triple. intros.
  destruct b; intros.
  - inverts H3 as H3.
    specializes H0 H2 H3.
  - inverts H3 as H3.
    specializes H1 H2 H3.
Qed.

Lemma triple_ptypetest: forall H tag v,
  triple H (fun r => H \* \[r = vbool (interpret_tag tag v)])
    (ptypetest tag (pval v)).
Proof.
  unfold triple. intros.
  hintro.
  inverts H1 as H1.
  jauto.
Qed.

(** Use triples in the proof instead of unfolding everything *)
Lemma triple_ptypecast_success: forall H tag v,
  interpret_tag tag v = true ->
  triple H (fun r => H \* \[r = v])
    (ptypecast tag v).
Proof.
  unfold ptypecast. intros.
  eapply triple_plet.
  { apply triple_ptypetest. }
  { intros.
    simpl.
    apply triple_extract_pure_r. intros. subst. rewrite H0.
    apply triple_pif_true.
    apply triple_val. }
  { intros. xsimpl. } (* vacuous; abort cannot happen as result is bool *)
Qed.

Lemma triple_ptypecast_failure: forall H tag v,
  interpret_tag tag v = false ->
  triple H (fun r => H \* \[r = vabort])
    (ptypecast tag v).
Proof.
  unfold ptypecast. intros.
  eapply triple_plet.
  { apply triple_ptypetest. }
  { intros. simpl.
    apply triple_extract_pure_r. intros. subst. rewrite H0.
    apply triple_pif_false.
    apply triple_val. }
  { intros. xsimpl. }
Qed.

(* semantic reasoning also works *)
Lemma triple_ptypecast_failure1: forall H tag v,
  interpret_tag tag v = false ->
  triple H (fun r => H \* \[r = vabort])
    (ptypecast tag v).
Proof.
  unfold triple. intros.
  hintro.
  inverts H2 as H2.
  simpl in H10.
  inverts H10 as H10.
  { inverts H2 as H2.
    false. }
  { inverts H2 as H2.
    inverts H10 as H10.
    splits*. }
  { inverts H2 as H2. }
Qed.

(** Arrow type in terms of triples *)
Definition tarrow_ t1 t2 : type := fun vf =>
  is_fn vf ->
  forall v,
    pure_triple (t1 v) (fun r => t2 r) (papp (pval vf) (pval v)).

(** Type assertions talk about strictly fewer executions. *)
Lemma tarrow_triple: forall t1 t2,
  tarrow t1 t2 <: tarrow_ t1 t2.
Proof.
  unfold tarrow, tarrow_. unfold subtype, pure_triple.
  intros.
  specializes H H0 H1.
Qed.

(** This is not true for the same reason [pure_triple_to_triple] isn't true. *)
Lemma tarrow_triple_conv: forall t1 t2,
  tarrow_ t1 t2 <: tarrow t1 t2.
Proof.
  unfold tarrow, tarrow_. unfold subtype, pure_triple.
  intros.
  specializes H H0 H1 r.
  apply H.
Abort.

Definition tail := vfun "x"
  (pmatch (pvar "x") (
    (tag_nil, pval verr) ::
    (tag_cons, (plet "y" (psnd (pvar "x")) (pvar "y"))) ::
    nil)).

(* sanity check for big-step semantics, pmatch, ANF *)
Example ex_tail: exists r,
  bigstep empty_heap (papp (pval tail) (pval (vcons (vint 1) vnil))) empty_heap r /\ r = vnil.
Proof.
  unfold tail. simpl. eexists.
  split.
  { eapply eval_app_fun. reflexivity.
    simpl.
    eapply eval_plet.
    apply eval_pval.
    unfold vcons, not. intros. inverts H as H.
    simpl.
    eapply eval_plet.
    apply eval_ptypetest.
    simpl.
    unfold not. intros. inverts H as H.
    apply eval_pif_false.
    eapply eval_plet.
    apply eval_ptypetest.
    simpl.
    unfold not. intros. inverts H as H.
    apply eval_pif_true.
    eapply eval_plet.
    apply eval_psnd2.
    simpl.
    unfold vnil, not. intros. inverts H as H.
    apply eval_pval. }
  { reflexivity. }
Qed.

Definition tail_sp1 := ∀ t, tarrow (tlist t) (tlist t).
Definition tail_sp2 := ∀ t, tarrow (tlist t) (tunion (tlist t) tabort).
Definition tail_sp3 := ∀ t, tarrow (tcons t (tlist t)) (tlist t).
Definition tail_sp4 := ∀ t,
  tintersect
    (tarrow (tnot (tcons t (tlist t))) tabort)
    (tarrow (tcons t (tlist t)) (tlist t)).

(* case is encoded manually. too much of a pain to do it with dependent arrows *)
Definition tail_sp5 := ∀ t,
  tintersect
    (tarrow (tcons t (tlist t)) (tlist t))
    (tarrow tnil terr).

Definition tail_sp6 := ∀ t (ys:type),
  tintersect
    (tarrow (tcons t ys) ys)
    (tarrow (tnot (tcons t ys)) terr).

Definition tail_sp7 := tarrow tany tany.

Lemma tail_sp1_sp7:
  tail_sp1 <: tail_sp7.
Proof.
  unfold subtype, tail_sp1, tail_sp7.
  intros.
  specializes H tany.
  unfold tarrow. intros. subst.
  unfold tarrow in H.
  specializes H H0.
  (* we now have to prove that given v0:Any, v0:List Any *)
Abort.

Lemma tail_sp6_sp7:
  tail_sp6 <: tail_sp7.
Proof.
  unfold subtype, tail_sp6, tail_sp7. intros.
  specializes H tany tany. destruct H.
  unfold tarrow. intros.
  destruct (classic (tcons tany tany v0)).
  - specializes H H1 H4.
  - specializes H0 H1 H3.
    applys~ subtype_terr_tany.
Qed.
(* Print Assumptions tail_sp6_sp7. *)

Lemma tail_sp6_sp1:
  tail_sp6 <: tail_sp1.
Proof.
  unfold subtype, tail_sp6, tail_sp1. intros.
  unfold tforall. intros t1.
  specializes H t1 (tlist t1). destruct H.
  unfold tarrow. intros.
  destruct (classic (tcons t1 (tlist t1) v0)).
  - specializes H H1 H4 H3.
  - specializes H0 H1 H4 H3.
    apply~ subtype_terr_tlist.
Qed.

Lemma tail_sp4_sp2:
  tail_sp4 <: tail_sp2.
Proof.
  unfold subtype, tail_sp4, tail_sp2. intros.
  unfold tforall. intros t1.
  specializes H t1. destruct H.
  unfold tarrow. intros.
  destruct (classic (tcons t1 (tlist t1) v0)).
  - specializes H0 H1 H4 H3.
    left.
    assumption.
  - specializes H H1 H4 H3.
    right.
    assumption.
Qed.

Lemma tail_sp4_sp3:
  tail_sp4 <: tail_sp3.
Proof.
  unfold subtype, tail_sp4, tail_sp3. intros.
  unfold tforall. intros t1.
  specializes H t1. destruct H.
  unfold tarrow. intros.
  destruct (classic (tcons t1 (tlist t1) v0)).
  - specializes H0 H1 H4 H3.
  - specializes H H1 H4 H3.
Abort.

Definition apply := vfun "f" (pfun "x" (papp (pvar "f") (pvar "x"))).
Definition apply_type1 := ∀ a b, tarrow (tarrow a b) (tarrow a b).
Definition apply_type2 := ∀ b x, tarrow (tarrow (tsingle x) b) (tdarrow x ttop b).
Definition apply_spec := forall (f x:val) (b:type),
  triple \[is_fn f /\ (tarrow (tsingle x) b) f]
    (fun r => \[b r])
      (plet "applyf" (papp (pval apply) (pval f))
       (papp (pvar "applyf") (pval x))).

Lemma apply_has_type1:
  apply_type1 apply.
Proof.
  unfold apply_type1, apply.
  unfold tforall. intros a b.

  (* assume v, the value eventually bound to f, has function type.
    then confirm using the big-step semantics. *)
  unfold tarrow at 1. intros.
  inverts H1 as H1. 2: { invert H1. } injects H1.
  inverts H7 as H7.
  clear H H7.

  (* do the same for v0/x *)
  unfold tarrow. intros.
  inverts H2 as H2. 2: { invert H2. } injects H2.
  clear H. simpl in H8.

  (* we know v is of function type, so we have to handle
    both cases when using the big-step semantics *)
  inverts H8 as H8.

  { unfold tarrow in H0.
    forward H0. exists "_". exs. left. reflexivity.
    specializes H0 H1.
    eapply H0.
    eapply eval_app_fun. reflexivity.
    eassumption. }

  { unfold tarrow in H0.
    forward H0. exs. right. reflexivity.
    specializes H0 H1.
    eapply H0.
    eapply eval_app_fix. reflexivity.
    eassumption. }
Qed.

Lemma apply_has_type2:
  apply_type2 apply.
Proof.
  unfold apply_type2, apply.
  unfold tforall. intros b x.

  (* assume v, the value eventually bound to f, has function type.
    then confirm using the big-step semantics. *)
  unfold tarrow at 1. intros.
  inverts H1 as H1. 2: { invert H1. } injects H1.
  inverts H7 as H7.
  clear H H7.

  (* do the same for v0/x *)
  unfold tdarrow. intros.
  inverts H2 as H2. 2: { invert H2. } injects H2.
  simpl in H8. clear H.

  (* we know v is of function type, so we have to handle
    both cases when using the big-step semantics *)
  inverts H8 as H8.

  { unfold tarrow, tsingle in H0.
    forward H0. exists "_". exs. left. reflexivity.
    specializes H0 x.
    forward H0 by reflexivity.
    specializes H0 h0 h0 r.
    apply H0.
    eapply eval_app_fun. reflexivity.
    eassumption. }

  { unfold tarrow, tsingle in H0.
    forward H0. exs. right. reflexivity.
    specializes H0 x.
    forward H0 by reflexivity.
    specializes H0 h0 h0 r.
    apply H0.
    eapply eval_app_fix. reflexivity.
    eassumption. }
Qed.

Lemma apply_has_spec:
  apply_spec.
Proof.
  unfold apply_spec, apply. unfold triple. intros.
  hinv H. subst h1. destruct H.

  (* use the arrow type. given f is a function, and we supply the singleton, we know the result is of b *)
  unfold tarrow, tsingle in H1.
  specializes H1 H x. forward H1 by reflexivity.

  inverts H0 as H0.
  2: { (* the case where the let produces an abort *)
    inverts H0 as H0.
    { injects H0. simpl in H7. inverts H7 as H7. }
    { inverts H0 as H0. }
  }
  clear H8.
  simpl in H9.
  (* H0 is the execution of e1, which applies apply to f.
    H9 is e2, which applies the result to x. *)

  inverts H0 as H0. 2: { inverts H0 as H0. } injects H0.
  simpl in H7.
  inverts H7 as H7.

  (* now we know that e1 returned a function.
    continue symbolically executing e2. *)
  inverts H9 as H9. 2: { invert H9. } injects H9.
  simpl in H7.
  hintro.
  eauto.
Qed.

Definition length_list := vfix "length" "xs"
  (pmatch (pvar "xs")
    ((tag_nil, pval (vint 0)) ::
    (tag_cons,
      plet "tail" (psnd (pvar "xs"))
      (plet "r1" (papp (pvar "length") (pvar "tail"))
        (padd (pval (vint 1)) (pvar "r1")))) ::
    nil)).

Definition length_list_type := ∀ t, tarrow (tlist t) (tunion tint tabort).

Lemma length_list_has_type:
  length_list_type length_list.
Proof.
  unfold length_list_type, length_list.
  unfold tforall. intros t.
  unfold tarrow. intros _ v Ht.
  (* induction on the structure of the type of the input list *)
  induction Ht; intros * Hb.
  {
    (* err base case *)
    inverts Hb as Hb. { inverts Hb as Hb. } injects Hb.
    simpl in H5.
    inverts H5 as H5. 2: { inverts H5 as H5. } simpl in H7.
    clear H6.
    inverts H5 as H5.
    inverts H7 as H7. clear H6. 2: { inverts H7 as H7. }
    inverts H7 as H7. simpl in H0.
    inverts H0 as H0.
    inverts H0 as H0. 2: { inverts H0 as H0. } clear H6.
    inverts H0 as H0. simpl in H7.
    inverts H7 as H7.
    inverts H7 as H7.
    right. apply tabort_intro.
  }
  {
    (* empty list base case *)
    inverts Hb as Hb. { inverts Hb as Hb. } injects Hb.
    simpl in H5.
    inverts H5 as H5. 2: { inverts H5 as H5. } simpl in H7.
    clear H6.
    inverts H5 as H5.
    inverts H7 as H7. clear H6. 2: { inverts H7 as H7. }
    inverts H7 as H7. simpl in H0.
    inverts H0 as H0.
    inverts H0 as H0. left. apply tint_intro.
  }
  {
    (* inductive case *)
    inverts Hb as Hb. { inverts Hb as Hb. } injects Hb.
    simpl in H6.
    inverts H6 as H6. 2: { inverts H6 as H6. } simpl in H7.
    clear H7.
    inverts H6 as H6.
    inverts H8 as H8. clear H7. 2: { inverts H8 as H8. }
    inverts H8 as H8. simpl in H0.
    inverts H0 as H0.
    inverts H0 as H0. clear H7. 2: { inverts H0 as H0. }
    inverts H0 as H0. simpl in H8.
    inverts H8 as H8.
    inverts H8 as H8. clear H7.
    2: { inverts H8 as H8. inverts Ht as Ht. }
    inverts H8 as H8. simpl in H0.
    (* recursive call *)
    inverts H0 as H0.
    {
      (* if it doesn't abort *)
      specializes IHHt H0.
      clear H0.
      destruct IHHt. 2: { false. }
      inverts H8 as H8.
      left. apply tint_intro.
    }
    {
      (* if it aborts *)
      specializes IHHt H0.
      assumption.
    }
  }
Qed.
