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
(* Definition var : Type := string. *)
Notation var := string.
Implicit Types x k : var.

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
  | passert (v: expr)
  | pref (v: expr)
  | pderef (v: expr)
  | passign (e1: expr) (e2: expr)
  | pif (v: expr) (e1: expr) (e2: expr)
  | papp (e1: expr) (e2: expr)
  | pshift (eb: var -> expr)
  | preset (e: expr).

Implicit Types e : expr.

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
  | padd e1 e2 => padd (aux e1) (aux e2)
  | pminus x z => pminus x z
  | pfst x => pfst x
  | psnd x => psnd x
  | pvar x => if_y_eq x (pval v) e
  | passert b => passert (aux b)
  | pderef r => pderef (aux r)
  | passign x z => passign (aux x) (aux z)
  | pref v => pref (aux v)
  | pfun x t1 => pfun x (if_y_eq x t1 (aux t1))
  | pfix f x t1 => pfix f x (if_y_eq f t1 (if_y_eq x t1 (aux t1)))
  | papp e1 e2 => papp (aux e1) (aux e2)
  | plet x t1 t2 => plet x (aux t1) (if_y_eq x t2 (aux t2))
  | pif t0 t1 t2 => pif (aux t0) (aux t1) (aux t2)
  | pshift e => pshift (fun k => aux (e k))
  | preset e => preset (aux e)
  end.


Module Val.
  Definition value := val.
End Val.

Module Export Heap := HeapF.HeapSetup Val.

Definition empty_heap : heap := Fmap.empty.

Definition postcond := val -> hprop.


Inductive eresult : Type :=
  | enorm : val -> eresult
  | eshft : (var -> expr) -> (val -> expr) -> eresult.

Notation "'eshft(' k ',' eb ',' x ',' ek ')'" :=
  (eshft k eb x ek) (at level 30, only printing,
  format "'eshft(' k ','  eb ','  x ','  ek ')'" ).

Definition penv := Fmap.fmap var (val -> expr).
Implicit Types p penv : penv.

#[global]
Instance Inhab_pfun : Inhab (val -> expr).
Proof.
  constructor.
  exists (fun a:val => pval vunit).
  constructor.
Qed.

Definition empty_penv : penv := Fmap.empty.

Coercion pval : val >-> expr.
Coercion pvar : var >-> expr.
Coercion vint : Z >-> val.

Inductive bigstep : penv -> heap -> expr -> heap -> eresult -> Prop :=

  | eval_pval : forall p1 h v,
    bigstep p1 h (pval v) h (enorm v)

  | eval_pfun : forall p h x e,
    bigstep p h (pfun x e) h (enorm (vfun x e))

  | eval_padd : forall p1 h v1 v2 i1 i2,
    vint i1 = v1 ->
    vint i2 = v2 ->
    bigstep p1 h (padd (pval v1) (pval v2)) h (enorm (vint (i1 + i2)))

  | eval_pshift : forall h p (eb:var->expr),
    bigstep p h (pshift eb) h (eshft eb (fun v => pval v))

  | eval_plet : forall p1 h1 h3 h2 x e1 e2 v Re,
    bigstep p1 h1 e1 h3 (enorm v) ->
    bigstep p1 h3 (subst x v e2) h2 Re ->
    bigstep p1 h1 (plet x e1 e2) h2 Re

  | eval_plet_sh : forall x e1 e2 h1 h2 p1 (eb:var->expr) (ek:val->expr),
    bigstep p1 h1 e1 h2 (eshft eb ek) ->
    bigstep p1 h1 (plet x e1 e2) h2 (eshft eb (fun y => plet x (ek y) e2))

  | eval_papp_fun : forall v1 v2 h x e Re p1,
    v1 = vfun x e ->
    bigstep p1 h (subst x v2 e) h Re ->
    bigstep p1 h (papp (pval v1) (pval v2)) h Re

  (* | eval_app_fix : forall v1 v2 h x e Re xf p,
    v1 = vfix xf x e ->
    bigstep p h (subst x v2 (subst xf v1 e)) h Re ->
    bigstep p h (papp (pval v1) (pval v2)) h Re *)

  | eval_papp_unk : forall v h1 h2 Re (ef:val->expr) (f:var) p1,
    Fmap.read p1 f = ef ->
    bigstep p1 h1 (ef v) h2 Re ->
    bigstep p1 h1 (papp (pvar f) (pval v)) h2 Re

  | eval_preset_val : forall p1 h1 h2 p e v,
    bigstep p1 h1 e h2 (enorm v) ->
    bigstep p1 h1 (preset e) h2 (enorm v)

  | eval_preset_sh : forall k p1 h1 h2 h3 e (eb:var->expr) (ek:val->expr) Re,
    bigstep p1 h1 e h3 (eshft eb ek) ->
    bigstep (Fmap.update p1 k ek) h3 (eb k) h2 Re ->
    bigstep p1 h1 (preset e) h2 Re

  .

Notation " '[' p1 ','  h1  '|'  e ']'  '~~>'  '[' p2 ','  h2  '|'  Re ']'" :=
  (bigstep p1 h1 e p2 h2 Re) (at level 30, only printing).

Notation "'pshift' k '.' e" :=
  (pshift k e) (at level 30, only printing,
  format "'pshift'  k '.'  e" ).


(** * Staged formulae *)
Inductive flow : Type :=
  | req : hprop -> flow -> flow
  | ens : postcond -> flow
  | bind : flow -> (val -> flow) -> flow
  | fex : forall (A:Type), (A -> flow) -> flow
  | fall : forall (A:Type), (A -> flow) -> flow
  | unk : var -> val -> flow
  | intersect : flow -> flow -> flow
  | disj : flow -> flow -> flow
  | sh : (var -> flow) -> flow
  | rs : flow -> flow
  | defun : var -> (val -> flow) -> flow
  .


(* Notation "'ens[' r ']' H" :=
  (ens r H) (at level 30, only printing
  (* , *)
  (* format "ens[ r ] H" *)
  ). *)

(* Implicit Types f : flow.
Implicit Types F : var -> flow.
Implicit Types φ : var -> var -> flow. *)

(* Definition ens_ H := ens (fun r s => \[r = vunit] \* H s). *)

(* Definition ufun := val -> val -> flow. *)
(* Definition ufun : Type := var * var * flow. *)
(* Definition ufun : Type := var -> var -> flow. *)
Definition ufun := val -> flow.
(* Definition senv := Fmap.fmap var ufun. *)
Definition senv := Fmap.fmap var ufun.
Implicit Types u : ufun.
Implicit Types env : senv.
Definition empty_env : senv := Fmap.empty.

Definition ens_ H := ens (fun r => \[r = vunit] \* H).

#[global]
Instance Inhab_ufun : Inhab ufun.
Proof.
  constructor.
  exists (fun (v:val) => ens_ \[]).
  constructor.
Qed.

Declare Scope flow_scope.
Open Scope flow_scope.

Definition seq (f1 f2:flow) := bind f1 (fun _ => f2).

Infix ";;" := seq (at level 38, right associativity) : flow_scope.

Inductive result : Type :=
  | norm : val -> result
  | shft : (var -> flow) -> (val -> flow) -> result.

(* Notation "'shft(λ' k  r '.'  fb ',' 'λ' x  r1 '.'  fk ')'" :=
(* Notation "'shft(λ' k r '.' fb ',' 'λ' x r1 '.' fk ')'" := *)
  (shft k r fb x r1 fk) (at level 30, only printing
  (* , *)
  (* format "'shft(λ' k  r '.'  fb ','  'λ' x  r1 '.'  fk ')'"  *)
  ). *)

Notation "'∃' a1 .. an , H" :=
  (fex (fun a1 => .. (fex (fun an => H)) ..))
  (at level 39, a1 binder, H at level 50, right associativity,
   format "'[' '∃' '/ '  a1  ..  an , '/ '  H ']'") : flow_scope.

(* Fixpoint flow_res f : option var :=
  match f with
  | ens r _ => Some r
  | ens_ _ => None
  | upd _ _ => None
  | req _ f => flow_res f
  | seq _ f => flow_res f
  | sh _ r => Some r
  | fexs _ f => flow_res f
  (* | fex_fresh _ f => flow_res f *)
  | unk _ _ r => Some r
  (* | fex f => None *)
  (* TODO remove *)
  | rs _ r => None (* TODO remove *)
  end. *)

Inductive satisfies : senv -> senv -> heap -> heap -> result -> flow -> Prop :=

  | s_req : forall (s1 s2:senv) H (h1 h2:heap) R f,
    (forall (hp hr:heap),
      H hp ->
      h1 = Fmap.union hr hp ->
      Fmap.disjoint hr hp ->
      satisfies s1 s2 hr h2 R f) ->
    satisfies s1 s2 h1 h2 R (req H f)

  | s_ens : forall s1 Q h1 h2 R,
    (exists v h3,
      R = norm v /\
      Q v h3 /\
      h2 = Fmap.union h1 h3 /\
      Fmap.disjoint h1 h3) ->
    satisfies s1 s1 h1 h2 R (ens Q)

  | s_bind : forall s3 h3 v s1 s2 f1 (f2:val->flow) h1 h2 R,
    satisfies s1 s3 h1 h3 (norm v) f1 ->
    satisfies s3 s2 h3 h2 R (f2 v) ->
    satisfies s1 s2 h1 h2 R (bind f1 f2)

  | s_fex s1 s2 h1 h2 R (A:Type) (f:A->flow)
    (H: exists b,
      satisfies s1 s2 h1 h2 R (f b)) :
    satisfies s1 s2 h1 h2 R (@fex A f)

  | s_fall s1 s2 h1 h2 R (A:Type) (f:A->flow)
    (H: forall b,
      satisfies s1 s2 h1 h2 R (f b)) :
    satisfies s1 s2 h1 h2 R (@fall A f)

  | s_unk : forall s1 s2 h1 h2 R xf uf a,
    Fmap.read s1 xf = uf ->
    satisfies s1 s2 h1 h2 R (uf a) ->
    satisfies s1 s2 h1 h2 R (unk xf a)

  | s_intersect s1 s2 h1 h2 R f1 f2
    (H1: satisfies s1 s2 h1 h2 R f1)
    (H2: satisfies s1 s2 h1 h2 R f2) :
    satisfies s1 s2 h1 h2 R (intersect f1 f2)

  | s_disj_l s1 s2 h1 h2 R f1 f2
    (H: satisfies s1 s2 h1 h2 R f1) :
    satisfies s1 s2 h1 h2 R (disj f1 f2)

  | s_disj_r s1 s2 h1 h2 R f1 f2
    (H: satisfies s1 s2 h1 h2 R f2) :
    satisfies s1 s2 h1 h2 R (disj f1 f2)

    (** The new rules for shift/reset are as follows. *)

  | s_sh : forall s1 h1 (fb:var->flow),
    satisfies s1 s1 h1 h1
      (* (shft x shb v (fun r1 => rs (ens (fun r => \[r = v])) r1)) *)
      (shft fb (fun r1 => ens (fun r => \[r = r1])))
      (sh fb)
    (** A [sh] on its own reduces to a [shft] containing an identity continuation. *)

  (* | s_shc s1 h1 x shb fk v :
    satisfies s1 s1 h1 h1
      (shft x shb v (fun r2 => rs fk r2))
      (shc x shb v (fun r2 => rs fk r2)) *)
    (** [shc] corresponds directly to [shft]. *)

  (* | s_seq_sh s1 s2 f1 f2 fk h1 h2 shb k (v:val) :
    satisfies s1 s2 h1 h2 (shft k shb v (fun r1 => rs fk r1)) f1 ->
    satisfies s1 s2 h1 h2 (shft k shb v (fun r1 => rs (fk;; f2) r1)) (f1;; f2) *)

  | s_bind_sh : forall s1 s2 f1 (f2:val->flow) fk h1 h2 (fb:var->flow),
    satisfies s1 s2 h1 h2 (shft fb fk) f1 ->
    satisfies s1 s2 h1 h2 (shft fb (fun r1 => bind (fk r1) f2))
      (bind f1 f2)

    (** This rule extends the continuation in a [shft] on the left side of a [seq]. Notably, it moves whatever comes next #<i>under the reset</i>#, preserving shift-freedom by constructon. *)

  | s_rs_sh : forall k s1 s2 fr h1 h2 rf s3 h3 (fb:var->flow) fk,
    satisfies s1 s3 h1 h3 (shft fb fk) fr ->
    satisfies (Fmap.update s3 k (fun a => rs (fk a))) s2
      h3 h2 rf (rs (fb k)) ->
    satisfies s1 s2 h1 h2 rf (rs fr)

    (** This rule applies when the body of a [rs] #<i>evaluates to</i># a [shft] (not when a [sh] is directly inside a [rs]; that happens in reduction). The continuation carried by the [shft] is known, so it is bound in (the environment of) the [sh]ift body before that is run. *)
    (** The two resets in the semantics are accounted for: one is around the shift body, and one is already the topmost form in the continuation. *)
    (** Note: because staged formulae are turned into values (via [shft] and being added to the [senv]), rewriting can no longer be done to weaken them. Environment entailment was an attempt at solving this problem; the Proper instances might have to be tweaked to allow rewriting too. Another possible solution is a syntactic entailment relation in the relevant rules to allow weakening. *)

  | s_rs_val : forall s1 s2 h1 h2 v f,
    satisfies s1 s2 h1 h2 (norm v) f ->
    satisfies s1 s2 h1 h2 (norm v) (rs f)

  | s_defun s1 s2 h1 x uf :
    (* ~ Fmap.indom s1 x -> *)
    s2 = Fmap.update s1 x uf ->
    satisfies s1 s2 h1 h1 (norm vunit) (defun x uf)

  (* | s_discard s1 s2 h x R f :
    satisfies s1 s2 h h R f ->
    s2 = Fmap.remove s1 x ->
    satisfies s1 s2 h h R (discard f x) *)

  .

(* Notation "'∀' a1 .. an , H" :=
  (fall (fun a1 => .. (fall (fun an => H)) ..))
  (at level 39, a1 binder, H at level 50, right associativity,
   format "'[' '∀' '/ '  a1  ..  an , '/ '  H ']'") : flow_scope. *)


Notation "s1 ',' s2 ','  h1 ','  h2 ','  r  '|=' f" :=
  (satisfies s1 s2 h1 h2 r f) (at level 30, only printing).

Lemma s_seq : forall s3 h3 r1 s1 s2 f1 f2 h1 h2 R,
  satisfies s1 s3 h1 h3 (norm r1) f1 ->
  satisfies s3 s2 h3 h2 R f2 ->
  satisfies s1 s2 h1 h2 R (seq f1 f2).
Proof.
  unfold seq. intros.
  applys* s_bind.
Qed.

Lemma s_ens_ : forall H h1 h2 s1,
  (exists h3,
    H h3 /\
    h2 = Fmap.union h1 h3 /\
    Fmap.disjoint h1 h3) ->
  satisfies s1 s1 h1 h2 (norm vunit) (ens_ H).
Proof.
  unfold ens_. intros.
  applys* s_ens.
  destr H0. exists vunit h3. intuition. hintro. jauto.
Qed.


(* Notation "'ens' H" :=
  (ens_ H) (at level 30, only printing,
  format "'ens' H"). *)




Inductive spec_assert_valid_under penv (env:senv) : expr -> flow -> Prop :=
  | sav_base: forall e f,
    (forall h1 h2 (eb:var->expr) (ek:val->expr),
        not (bigstep penv h1 e h2 (eshft eb ek))) ->
    (forall h1 h2 v,
        bigstep penv h1 e h2 (enorm v) ->
        satisfies env env h1 h2 (norm v) f) ->
    spec_assert_valid_under penv env e f

| sav_shift: forall e f,
    (forall h1 h2 v, not (bigstep penv h1 e h2 (enorm v))) ->
    (forall h1 h2 (eb:var->expr) (ek:val->expr),
        bigstep penv h1 e h2 (eshft eb ek) ->
        exists (fb:var->flow) (fk:val->flow),
          satisfies env env h1 h2 (shft fb fk) f /\
            (forall x, spec_assert_valid_under penv env (eb x) (fb x)) /\
            (forall v, spec_assert_valid_under penv env (ek v) (fk v))) ->
    spec_assert_valid_under penv env e f.


Definition spec_assert_valid e f : Prop :=
  forall penv env,
    spec_assert_valid_under penv env e f.
