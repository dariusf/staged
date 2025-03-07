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
  (* | vfix : var -> var -> expr -> val
  | vloc : loc -> val
  | vtup : val -> val -> val
  | vstr : string -> val
  | vbool : bool -> val
  | vlist : list val -> val
  | vfptr : var -> val *)

with expr : Type :=
  | pvar (x: var)
  | pval (v: val)
  | plet (x: var) (e1 e2: expr)
  (* | pfix (xf: var) (x: var) (e: expr)
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
 *)
  | papp (e1: expr) (e2: expr)
  | pshift (k: var) (e: expr)
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
  (* | padd x z => padd x z
  | pminus x z => pminus x z
  | pfst x => pfst x
  | psnd x => psnd x *)
  | pvar x => if_y_eq x (pval v) e
  (* | passert b => passert (aux b)
  | pderef r => pderef (aux r)
  | passign x z => passign (aux x) (aux z)
  | pref v => pref (aux v)
  | pfun x t1 => pfun x (if_y_eq x t1 (aux t1))
  | pfix f x t1 => pfix f x (if_y_eq f t1 (if_y_eq x t1 (aux t1)))
  *)
  | papp e v => papp e v
  | plet x t1 t2 => plet x (aux t1) (if_y_eq x t2 (aux t2))
  (* | pif t0 t1 t2 => pif (aux t0) (aux t1) (aux t2) *)
  | pshift k e1 => pshift k (aux e1)
  | preset e => preset (aux e)
  end.

Module Val.
  Definition value := val.
End Val.

Module Export Heap := HeapF.HeapSetup Val.

Definition empty_heap : heap := Fmap.empty.




Inductive eresult : Type :=
  | enorm : val -> eresult
  | eshft : val -> var -> expr -> eresult.

Definition penv := Fmap.fmap var val.
Implicit Types p : penv.

Definition empty_penv : penv := Fmap.empty.

Definition store : Type := Fmap.fmap var val.
Definition empty_store : store := Fmap.empty.
Implicit Types s : store.

Inductive bigstep : penv -> store -> heap -> expr -> store -> heap -> var -> eresult -> Prop :=
  | eval_pval : forall s1 s2 h v p r,
    s2 = Fmap.update s1 r v ->
    bigstep p s1 h (pval v) s2 h r (enorm v)

  | eval_pshift : forall s1 s2 h p k eb r v,
    s2 = Fmap.update s1 r v ->
    bigstep p s1 h (pshift k eb) s2 h r
      (eshft (vfun k eb) r (pvar r))

      (* (eshft (vfun k eb) (vfun "x" (preset (pvar "x")))) *)

  (* there is no var rule *)

  | eval_plet : forall s1 s2 s3 h1 h3 h2 x e1 e2 v Re p1 r r1,
    bigstep p1 s1 h1 e1 s3 h3 r (enorm v) ->
    bigstep p1 s3 h3 (subst x v e2) s2 h2 r1 Re ->
    bigstep p1 s1 h1 (plet x e1 e2) s2 h2 r1 Re

  | eval_plet_sh : forall x e1 e2 h1 h2 p1 x1 x2 xy xtmp eb ek r r1 s1 s2,
    bigstep p1 s1 h1 e1 s2 h2 r (eshft (vfun x1 eb) x2 ek) ->
    bigstep p1 s1 h1 (plet x e1 e2) s2 h2 r1
      (eshft (vfun x1 eb)
        xy (plet xtmp (papp (pval (vfun x2 ek)) (pvar xy))
          (plet x (pvar xtmp) e2)))

  (*

  | eval_preset_val : forall s1 s2 h1 h2 p e v,
    bigstep p s1 h1 e s2 h2 (enorm v) ->
    bigstep p s1 h1 (preset e) s2 h2 (enorm v)

  | eval_preset_sh : forall s1 s2 s3 h1 h2 h3 R p e x1 x2 eb ek,
    bigstep p s1 h1 e s3 h3 (eshft (vfun x1 eb) (vfun x2 ek)) ->
    bigstep p s3 h3 ((* non-0 *) (subst x1 (vfun x2 ek) eb)) s2 h2 R ->
    bigstep p s1 h1 (preset e) s2 h2 R *)

  .






Definition asn := store -> heap -> Prop.
Implicit Types H : asn.
Implicit Types r : var.
(* Implicit Types Q : val -> asn. *)

(** * Staged formulae *)
Inductive flow : Type :=
  | req : asn -> flow -> flow
  (* | ens : (val -> asn) -> flow *)
  | ens : var -> asn -> flow
  | ens_ : asn -> flow
  | seq : flow -> flow -> flow
  | fexs : var -> flow -> flow (* exists in store *)
  | fex : forall (A:Type), (A -> flow) -> flow

  | sh : var -> flow -> var -> flow
  | rs : flow -> val -> flow

  (* 
  | fall : forall (A:Type), (A -> flow) -> flow
  | unk : var -> val -> val -> flow
  | intersect : flow -> flow -> flow
  | disj : flow -> flow -> flow
  | shc : var -> flow -> val -> (val -> flow) -> flow
  *)
  .

(* Definition ens_ H := ens (fun r s => \[r = vunit] \* H s). *)

Definition ufun := val -> val -> flow.
Definition senv := Fmap.fmap var ufun.
Implicit Types u : ufun.
Implicit Types S : senv.
Definition empty_env : senv := Fmap.empty.

Declare Scope flow_scope.
Open Scope flow_scope.

Infix ";;" := seq (at level 38, right associativity) : flow_scope.

Inductive result : Type :=
  | norm : val -> result
  | shft : var -> flow -> var -> flow -> result.

Inductive satisfies : store -> store -> heap -> heap -> result -> flow -> Prop :=

  | s_req : forall s1 s2 H (h1 h2:heap) R f,
    (forall (hp hr:heap),
      H s1 hp ->
      h1 = Fmap.union hr hp ->
      Fmap.disjoint hr hp ->
      satisfies s1 s1 hr h2 R f) ->
    satisfies s1 s1 h1 h2 R (req H f)

  | s_ens : forall s1 H h1 h2 R v h3 r,
      R = norm v ->
      Fmap.read s1 r = v ->
      H s1 h3 ->
      h2 = Fmap.union h1 h3 ->
      Fmap.disjoint h1 h3 ->
    satisfies s1 s1 h1 h2 R (ens r H)

  | s_ens_ : forall s1 H h1 h2 h3 r,
      H s1 h3 ->
      h2 = Fmap.union h1 h3 ->
      Fmap.disjoint h1 h3 ->
    satisfies s1 s1 h1 h2 (norm vunit) (ens_ H)

  | s_seq s3 h3 v s1 s2 f1 f2 h1 h2 R :
    satisfies s1 s3 h1 h3 (norm v) f1 ->
    satisfies s3 s2 h3 h2 R f2 ->
    satisfies s1 s2 h1 h2 R (seq f1 f2)
  (** seq is changed to require a value from the first flow *)

  (* | s_fex s1 s2 h1 h2 R (A:Type) (f:A->flow)
    (H: exists b,
      satisfies s1 s2 h1 h2 R (f b)) :
    satisfies s1 s2 h1 h2 R (@fex A f) *)

  | s_fex s1 s2 h1 h2 R (A:Type) (f:A->flow)
    (H: exists b,
      satisfies s1 s2 h1 h2 R (f b)) :
    satisfies s1 s2 h1 h2 R (@fex A f)

  | s_fexs : forall s1 s2 h1 h2 R f x,
    (exists v,
      satisfies (Fmap.update s1 x v) s2 h1 h2 R (f)) ->
    satisfies s1 s2 h1 h2 R (fexs x f)


  (* | s_fall s1 s2 h1 h2 R (A:Type) (f:A->flow)
    (H: forall b,
      satisfies s1 s2 h1 h2 R (f b)) :
    satisfies s1 s2 h1 h2 R (@fall A f)

  | s_unk s1 s2 h1 h2 r xf uf a
    (He: Fmap.read s1 xf = uf)
    (Hr: satisfies s1 s2 h1 h2 (norm r) (uf a r)) :
    satisfies s1 s2 h1 h2 (norm r) (unk xf a r)

  | s_intersect s1 s2 h1 h2 R f1 f2
    (H1: satisfies s1 s2 h1 h2 R f1)
    (H2: satisfies s1 s2 h1 h2 R f2) :
    satisfies s1 s2 h1 h2 R (intersect f1 f2)

  | s_disj_l s1 s2 h1 h2 R f1 f2
    (H: satisfies s1 s2 h1 h2 R f1) :
    satisfies s1 s2 h1 h2 R (disj f1 f2)

  | s_disj_r s1 s2 h1 h2 R f1 f2
    (H: satisfies s1 s2 h1 h2 R f2) :
    satisfies s1 s2 h1 h2 R (disj f1 f2) *)

  | s_sh s1 h1 x shb r :
    satisfies s1 s1 h1 h1
      (shft x shb r (ens r (fun _ => \[True])))
(* (fun r1 => rs (ens r (fun s => \[r = v])) r1) *)
      (sh x shb r)

  (*
    (** A [sh] on its own reduces to a [shft] containing an identity continuation. *)

  | s_seq_sh s1 s2 f1 f2 fk h1 h2 shb k (v:val) :
    satisfies s1 s2 h1 h2 (shft k shb v (fun r1 => rs fk r1)) f1 ->
    satisfies s1 s2 h1 h2 (shft k shb v (fun r1 => rs (fk;; f2) r1)) (f1;; f2)
    (** This rule extends the continuation in a [shft] on the left side of a [seq]. Notably, it moves whatever comes next #<i>under the reset</i>#, preserving shift-freedom by constructon. *)

  | s_rs_sh s1 s2 f h1 h2 r rf s3 h3 fb fk k v1 :
    satisfies s1 s3 h1 h3 (shft k fb v1 (fun r2 => rs fk r2)) f ->
    (* ~ Fmap.indom s3 k -> *)
    satisfies
        (Fmap.update s3 k (fun a r =>
          rs (ens_ \[v1 = a];; fk) r)) s2
      h3 h2 rf (rs fb r) ->
    satisfies s1 s2 h1 h2 rf (rs f r)

  | s_rs_val s1 s2 h1 h2 v f
    (H: satisfies s1 s2 h1 h2 (norm v) f) :
    satisfies s1 s2 h1 h2 (norm v) (rs f v) *)

  .

Notation "'∃' x1 .. xn , H" :=
  (fex (fun x1 => .. (fex (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '∃' '/ '  x1  ..  xn , '/ '  H ']'") : flow_scope.

(* Notation "'∀' x1 .. xn , H" :=
  (fall (fun x1 => .. (fall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '∀' '/ '  x1  ..  xn , '/ '  H ']'") : flow_scope. *)


Notation "s1 ',' s2 ','  h1 ','  h2 ','  r  '|=' f" :=
  (satisfies s1 s2 h1 h2 r f) (at level 30, only printing).

Inductive spec_assert : expr -> var -> flow -> Prop :=

  | sa_pval: forall r v,
    spec_assert (pval v) r (fexs r (ens r (fun s => \[Fmap.read s r = v])))

  | sa_pshift: forall r1 r k e fe,
    spec_assert e r1 fe ->
    spec_assert (pshift k e) r (fexs r (sh k fe r))

  .


Inductive spec_assert_valid : expr -> var -> flow -> Prop :=
  (* | sav_base: forall r s1 s2 f e h1 h2 v, *)
  | sav_base: forall e r f,
    (forall s1 s2 h1 h2 v,
      bigstep empty_penv s1 h1 e s2 h2 r (enorm v) ->
      satisfies s1 s2 h1 h2 (norm v) f) ->
    spec_assert_valid e r f

  | sav_shift: forall e r f,
    (* spec_assert_valid ek r fk -> *)
    (* spec_assert_valid eb r fb -> *)
    (forall s1 s2 h1 h2, forall x1 eb x2 ek,
    (* fb fk, *)
      bigstep empty_penv s1 h1 e s2 h2 r (eshft (vfun x1 eb) x2 ek) ->
      exists fb fk,
      satisfies s1 s2 h1 h2 (shft x1 fb x2 fk) f) ->
    spec_assert_valid e r f.
    (* TODO missing relation between fk and ek *)

Lemma pval_sound: forall v r,
  (* spec_assert (pval v) r (fexs r (ens r (fun s => \[Fmap.read s r = v]))) -> *)
  spec_assert_valid (pval v) r (fexs r (ens r (fun s => \[Fmap.read s r = v]))).
Proof.
  intros.
  (* TODO remove these after confirming that they are useless *)
  (* useless, value case must be proved entirely using semantics *)
  (* inverts H. *)
  (* clear H. *)
  applys sav_base.
  intros.
  inverts H as H. (* eval_pval *)
  apply s_fexs. exists v0.
  applys* s_ens.
  resolve_fn_in_env.
  hintro. resolve_fn_in_env.
  fmap_eq.
Qed.


Lemma pshift_sound: forall k e r fe,
  (* spec_assert (pshift k e) r (fexs r (sh k fe r)) -> *)
  spec_assert_valid (pshift k e) r (fexs r (sh k fe r)).
Proof.
  intros.
  (* also useless? *)
  (* inverts H as H. *)
  (* clear H. *)
  applys sav_shift.

  intros.
  inverts H as H.
  (* eval_pshift *)
  exists fe.
  exs.
  apply s_fexs. exists v.
  eapply s_sh.
Qed.


Lemma plet_sound: forall x e1 e2 r r1 f1 f2,
  spec_assert_valid e1 r1 f1 ->
  spec_assert_valid e2 r f2 ->
  spec_assert_valid (plet x e1 e2) r
    (f1;; ens_ (fun s => \[Fmap.read s r = Fmap.read s x]);; f2).
Proof.
  intros.
  inverts H as H.
  {
    (* norm *)
    apply sav_base.
    intros.
    inverts H1 as H1.

    (* specializes H H1. *)
    admit.
  }
  {
    (* shift *)
    admit.
  }
Abort.