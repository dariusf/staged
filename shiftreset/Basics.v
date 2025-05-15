
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
(* Ltac auto_star ::= try solve [ auto | fmap_eq | eauto | intuition eauto ]. *)

(** * Programs *)
Definition var : Type := string.
Notation var_eq := String.string_dec.

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

Definition vadd (v1 v2 : val) : val :=
  match v1, v2 with
  | vint i1, vint i2 => vint (i1 + i2)
  | _, _ => vunit
  end.

Definition vand (v1 v2 : val) : val :=
  match v1, v2 with
  | vbool b1, vbool b2 => vbool (andb b1 b2)
  | _, _ => vunit
  end.

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

(** * Staged formulae *)
Inductive flow : Type :=
  | req : hprop -> flow -> flow
  | ens : postcond -> flow
  (* | seq : flow -> flow -> flow *)
  | bind : flow -> (val -> flow) -> flow
  | fex : forall (A:Type), (A -> flow) -> flow
  | fall : forall (A:Type), (A -> flow) -> flow
  | unk : var -> val -> flow
  | intersect : flow -> flow -> flow
  | disj : flow -> flow -> flow
(** The following are new: *)
  (* | sh : (var -> flow) -> flow *)
  | shc : var -> flow -> (val -> flow) -> flow
(** [sh k fb vr] is a shift with body [fb] and #<i>result</i># [vr]. *)
(** [k] names the continuation delimited by an enclosing [rs], and may occur in [fb] as an [unk] or [vfptr]. *)
(** [vr] is the #<i>result</i># of the shift, which is the value a shift appears to evaluate to when a continuation is taken. [vr] will be equal to the value that the continuation will be resumed with, and can be depended on in anything sequenced after a [sh]. *)
  (* | shc : var -> flow -> val -> (val -> flow) -> flow *)
(** [shc k fb vr fc] is a [sh] in CPS form, or the syntactic counterpart of [shft]. It carries a continuation whose argument is the equivalent of [sh]'s [r]. This continuation has a mixed first-/higher-order representation and has a [rs] as its topmost form. *)
(** Examples:
- the formula [Sh#(k. fb, vr, Rs(fc, r))] is represented as
  [shc "k" fb vr (fun r => rs fc r)]
- the continuation [(λ vr. < fc >)] is represented as
  a tuple [(vr, fun r => rs fc r)]. *)
  | rs : flow -> flow
(** [rs f vr] is a reset with body [f] and return value [vr]. *)
  | defun : var -> (val -> flow) -> flow
  | discard : var -> flow
(** [defun x uf] is equivalent to [ens_ (x=(λ x r. uf x r))], where [x] can reside in the environment (which regular [ens_] cannot access).
  Should defun be scoped? We don't think so, because the resulting continuation is first-class and does not have a well-defined lifetime. *)
  (* | discard : flow -> var -> flow *)
  .

Definition seq (f1 f2:flow) := bind f1 (fun _ => f2).

Definition ident v := ens (fun r => \[r = v]).

Definition sh k fb := shc k fb ident.

Definition ens_ H := ens (fun r => \[r = vunit] \* H).

Definition empty := ens_ \[True].

Notation req_ H := (req H empty).

Definition ufun := val -> flow.

#[global]
Instance Inhab_ufun : Inhab ufun.
Proof.
  constructor.
  exists (fun (v:val) => ens_ \[]).
  constructor.
Qed.

Definition senv := Fmap.fmap var ufun.

Definition empty_env : senv := Fmap.empty.

(* shft's continuation could have a more general [A -> flow] type, but it can't be used in the semantics as long as it has to pass through ufun *)
Inductive result : Type :=
  | norm : val -> result
  (* | shft : var -> flow -> (val -> flow) -> result *)
  .
  (** See [shc] for what the arguments mean. *)

Declare Scope flow_scope.
Open Scope flow_scope.

Infix ";;" := seq (at level 38, right associativity) : flow_scope.

(* Notation "'let' x '=' f1 'in' f2" :=
  (bind f1 (fun x => f2))
  (at level 38, x binder, right associativity, only printing) : flow_scope. *)

    (* format "'[' 'let'  x  '='  f1  'in' ']' '/' '[' f2 ']'") : flow_scope. *)
    (* format "'[v' '[' 'let'  x  '='  f1  'in' ']' '/' '[' f2 ']' ']'") : flow_scope. *)

(* Definition ex_bind :=
  bind (ens (fun r => \[r = vint 1])) (fun x => ens (fun r => \[r = x])).
Definition ex_bind1 :=
  bind (ex_bind) (fun x => ens (fun r => \[r = x])).

Example e : True.
Proof.
  pose ex_bind1.
  unfold ex_bind1 in f.
  unfold ex_bind in f. *)

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

(* Notation "'sh' '(' k '.' fb '),' vr" := (sh k fb vr)
  (at level 80, format "'sh'  '(' k '.'  fb '),'  vr", only printing) : flow_scope. *)

(* Notation "'shc' '(' k '.' fb ')' '(' vr '.' '⟨' fk '⟩' ')'" := (shc k fb vr (fun r => rs fk r))
  (at level 80, format "'shc'  '(' k '.'  fb ')'  '(' vr '.'  '⟨' fk '⟩' ')'", only printing) : flow_scope. *)

Notation "'ens' r '.' Q" := (ens (fun r => Q))
  (at level 80, format "'ens'  r '.'  Q" , only printing) : flow_scope.

Implicit Types s : senv.
Implicit Types h : heap.
Implicit Types H : hprop.
Implicit Types Q : postcond.
Implicit Types u : ufun.
(* Implicit Types c : val -> flow. *)
Implicit Types f : flow.
(* Implicit Types fb : var -> flow. *)
Implicit Types fk : val -> flow.
Implicit Types x y z k : var.
Implicit Types a v r : val.
Implicit Types R : result.
Implicit Types e : expr.


(* For when the goal can be dispatched by brute force.
  jauto handles these but will not leave unsolved goals. *)
Ltac zap :=
  lazymatch goal with
  | H: exists _, _ |- _ => destr H; zap
  | H: _ /\ _ |- _ => destr H; zap
  | |- _ /\ _ => splits; zap
  | |- exists _, _ => eexists; zap
  | _ => jauto
  end.

(* Dispatch goals involving the heaps that come out of ens once
  we have to reason about semantics *)
Ltac heaps :=
  lazymatch goal with
  | H: exists _, _ |- _ => destr H; heaps
  | H: _ /\ _ |- _ => destr H; heaps
  | H: norm _ = norm _ |- _ => injects H; heaps
  | H: (_ ~~> _) _ |- _ => hinv H; heaps
  | H: \[_] _ |- _ => hinv H; heaps
  | H: (_ \* _) _ |- _ => hinv H; heaps
  | |- (_ ~~> _) _ => hintro; heaps
  | |- (_ \* _) _ => hintro; heaps
  | |- \[_] _ => hintro; heaps
  (* as late as we can *)
  | |- _ /\ _ => splits; heaps
  | |- exists _, _ => eexists; heaps
  | _ => subst; rew_fmap *
  end.

(*
Inductive satisfies : senv -> senv -> heap -> heap -> val ->
  flow -> Prop :=

  | s_req : forall (s1 s2:senv) H (h1 h2:heap) v f,
    (forall (hp hr:heap),
      H hp ->
      h1 = Fmap.union hr hp ->
      Fmap.disjoint hr hp ->
      satisfies s1 s2 hr h2 v f) ->
    satisfies s1 s2 h1 h2 v (req H f)

  | s_ens : forall s1 Q h1 h2 v,
    (exists h3,
      Q v h3 /\
      h2 = Fmap.union h1 h3 /\
      Fmap.disjoint h1 h3) ->
    satisfies s1 s1 h1 h2 v (ens Q)

  | s_bind : forall s1 s2 s3 h1 h2 h3 v v1 f fk,
    satisfies s1 s3 h1 h3 v f ->
    satisfies s3 s2 h3 h2 v1 (fk v) ->
    satisfies s1 s2 h1 h2 v1 (bind f fk)

  | s_rs : forall s1 s2 fr h1 h2 v,
    satisfies_k s1 s2 h1 h2 v fr ident ->
    satisfies s1 s2 h1 h2 v (rs fr)

  | s_unk : forall s1 s2 h1 h2 v xf uf a,
    Fmap.read s1 xf = uf ->
    satisfies s1 s2 h1 h2 v (uf a) ->
    satisfies s1 s2 h1 h2 v (unk xf a)
*)

Inductive cont :=
| cont_id : cont
| cont_flow : (val -> flow) -> cont.

Inductive satisfies_k : senv -> senv -> heap -> heap -> val ->
  flow -> cont -> Prop :=
(*
  | sk_req : forall (s1 s2:senv) H (h1 h2:heap) v f fk,
    (forall (hp hr:heap),
      H hp ->
      h1 = Fmap.union hr hp ->
      Fmap.disjoint hr hp ->
      satisfies_k s1 s2 hr h2 v f fk) ->
    satisfies_k s1 s2 h1 h2 v (req H f) fk
*)
  | sk_ens_id : forall s1 Q h1 h2 v,
    (exists h3,
      Q v h3 /\
      h2 = Fmap.union h1 h3 /\
      Fmap.disjoint h1 h3) ->
    satisfies_k s1 s1 h1 h2 v (ens Q) cont_id
  | sk_ens : forall s1 s2 Q h1 h2 v v1 fk,
    (exists h3,
      Q v h3 /\
      h2 = Fmap.union h1 h3 /\
      Fmap.disjoint h1 h3) ->
    satisfies_k s1 s2 h1 h2 v1 (fk v) cont_id ->
    satisfies_k s1 s2 h1 h2 v1 (ens Q) (cont_flow fk)

  | sk_bind_id : forall s1 s2 h1 h2 v f fk1,
    satisfies_k s1 s2 h1 h2 v f (cont_flow fk1) ->
    satisfies_k s1 s2 h1 h2 v (bind f fk1) cont_id

  | sk_bind : forall s1 s2 h1 h2 v f fk1 fk,
    satisfies_k s1 s2 h1 h2 v f (cont_flow (fun v1 => bind (fk1 v1) fk)) ->
    satisfies_k s1 s2 h1 h2 v (bind f fk1) (cont_flow fk)

  | sk_sh_id : forall s1 s2 h1 h2 v k fb,
    satisfies_k (Fmap.update s1 k ident) s2 h1 h2 v fb cont_id ->
    satisfies_k s1 s2 h1 h2 v (sh k fb) cont_id

  | sk_sh : forall s1 s2 h1 h2 v k fb fk,
    satisfies_k (Fmap.update s1 k fk) s2 h1 h2 v fb cont_id  ->
    satisfies_k s1 s2 h1 h2 v (sh k fb) (cont_flow fk)
(*
  | sk_shc : forall s1 s2 h1 v k fb fk fk1,
    satisfies_k
      (Fmap.update s1 k (fun r => bind (fk r) fk1))
      s2 h1 h1 v fb ident ->
    satisfies_k s1 s2 h1 h1 v (shc k fb fk) fk1
*)

  | sk_rs_id : forall s1 s2 fr h1 h2 v,
    satisfies_k s1 s2 h1 h2 v fr cont_id ->
    satisfies_k s1 s2 h1 h2 v (rs fr) cont_id

  | sk_rs : forall s1 s2 s3 fr h1 h2 h3 v v1 fk,
    satisfies_k s1 s2 h1 h2 v fr cont_id ->
    satisfies_k s2 s3 h2 h3 v1 (fk v) cont_id ->
    satisfies_k s1 s3 h1 h3 v1 (rs fr) (cont_flow fk)

  | sk_unk : forall s1 s2 h1 h2 v xf uf a c,
    Fmap.read s1 xf = uf ->
    satisfies_k s1 s2 h1 h2 v (uf a) c ->
    satisfies_k s1 s2 h1 h2 v (unk xf a) c.
(*
  (* this rule is not syntax-directed, but seems essential *)
  (* TODO is this admissible? *)
  | sk_k_as_bind : forall s1 s2 h1 h2 v f fk,
    satisfies s1 s2 h1 h2 v (bind f fk) ->
    satisfies_k s1 s2 h1 h2 v f fk.
*)
Definition problematic_sk_bind :=
  rs (bind
        (ens (fun r => \[r = vint 1]))
        (fun v => sh "k" (ens (fun r => \[r = vint 2])))).

Example sk_bind_is_the_problem :
  exists s2 v,
    satisfies_k Fmap.empty s2 empty_heap empty_heap v problematic_sk_bind cont_id.
Proof.
  eexists.
  eexists.
  unfold problematic_sk_bind.
  apply sk_rs_id.
  apply sk_bind_id.
  (*
  apply sk_k_as_bind.
  eapply s_bind.
  eapply s_ens.
  admit. (* provable *)
  eapply s_bind.
  (* dead *) *)
  eapply sk_ens.
  { heaps. }
  apply sk_sh_id.
  eapply sk_ens_id.
  { heaps. }
Qed.

(* Conclusion, we need something that can carry the continuation around *)

(* Some derived rules *)
(*
Lemma sk_ident : forall s1 s2 h1 h2 v f,
  satisfies s1 s2 h1 h2 v f ->
  satisfies_k s1 s2 h1 h2 v f ident.
Proof.
  intros.
  applys sk_k_as_bind.
  applys* s_bind.
  applys s_ens. heaps.
Qed.

Lemma sk_empty : forall s1 s2 h1 h2 v fk,
  satisfies s1 s2 h1 h2 v (fk vunit) ->
  satisfies_k s1 s2 h1 h2 v empty fk.
Proof.
  intros.
  applys sk_k_as_bind.
  applys* s_bind.
  applys s_ens. heaps.
Qed.

(* this rule unfortunately cannot be proved by induction? *)
Lemma continuation_conv : forall s1 s2 h1 h2 v f fk,
  satisfies_k s1 s2 h1 h2 v f fk ->
  satisfies s1 s2 h1 h2 v (bind f fk).
Proof.
  introv H. induction H.
  {
    applys s_bind.
    applys s_req. intros.
    specializes H1 H2 H3 H4.
    (* cycle *)
    inverts H1.
    Fail exact H12.
    (* applys* H0. *)
    (* specializes H1 H H2 H3. *)
    admit.
    admit.
  }
Abort.
*)

Example e1: exists s1,
  satisfies_k empty_env s1 empty_heap empty_heap (vint 3)
  (rs (bind (sh "k" (unk "k" (vint 2))) (fun v => ens (fun r => \[r = vadd v (vint 1)])))) cont_id.
Proof.
  exs.
  applys sk_rs_id.
  applys sk_bind_id.
  applys sk_sh.
  applys sk_unk. reflexivity.
  rewrite fmap_read_update.
  applys sk_ens_id.
  { heaps. }
Qed.

(*
Example e2: exists v1 s1,
  satisfies empty_env s1 empty_heap empty_heap v1
  (bind (ens (fun r => \[r = vint 1]))
    (fun v => ens (fun r => \[r = vadd v (vint 2)])))
  /\ v1 = vint 3.
Proof.
  exs.
  split.
  - applys s_bind.
    applys s_ens. heaps.
    simpl.
    applys s_ens. heaps.
  - f_equal.
Qed.
*)


(* Example e1: exists s1,
  satisfies_k empty_env s1 empty_heap empty_heap (vint 3)
    (rs (bind
         (sh "k" (ens (fun r => \[r = vfptr "k"])))
         (fun v => ens (fun r => \[r = vadd v (vint 1)]))))
  cont_id.
Proof.
  exs.
  applys sk_rs_id.
  applys sk_bind_id.
  applys sk_sh.
  applys sk_unk. reflexivity.
  rewrite fmap_read_update.
  applys sk_ens_id.
  { heaps. }
Qed. *)

(* Definition entails f1 f2 :=
  forall s1 s2 h1 h2 v,
    satisfies s1 s2 h1 h2 v f1 ->
    satisfies s1 s2 h1 h2 v f2. *)

(* Lemma norm_bind_assoc: forall f fk fk1,
  entails (bind (bind f fk) fk1)
    (bind f (fun r => bind (fk r) fk1)).
Proof.
  unfold entails. intros.
  inverts H.
  inverts H7.
  applys* s_bind.
  applys* s_bind.
Qed. *)

(* Lemma no_standalone_shift: forall k fb,
  entails (sh k fb) (ens_ \[False]).
Proof.
  unfold entails. intros.
  inverts H.
Qed. *)

(* Lemma no_standalone_shift1: forall k fb,
  entails (sh k fb) (ens_ \[False]).
Proof.
  unfold entails. intros.
  (* note that we don't have to invert if
    we treat the continuation as identity... *)
  lets: sk_ident H. clear H.
  inverts H0.
  admit.
  admit.
  admit.
Abort. *)

Definition entails_k f1 c1 f2 c2 :=
  forall s1 s2 h1 h2 v,
    satisfies_k s1 s2 h1 h2 v f1 c1 ->
    satisfies_k s1 s2 h1 h2 v f2 c2.

Lemma red_init: forall k fb c,
  entails_k (sh k fb) c (sh k fb) c.
Proof.
  unfold entails_k, sh. intros.
  inverts H.
  applys* sk_sh_id.
  applys* sk_sh.
Qed.

Example e3:
  entails_k empty (cont_flow (fun v => ens_ \[v = vunit]))
    empty (cont_flow (fun v => ens_ \[v = vunit \/ v = vint 1])).
Proof.
  unfold entails_k. intros.
  inverts H.
  inverts H8.
  heaps.
  applys sk_ens. heaps.
  applys sk_ens_id. heaps.
Qed.

(* Lemma lem: forall s1 s2 h1 h2 v f fk,
  satisfies_k s1 s2 h1 h2 v f fk ->
  exists s3 h3 v1,
  satisfies s1 s3 h1 h3 v1 f /\
  satisfies s3 s2 h3 h2 v (fk v1).
Proof. *)

(* Lemma lem: forall s1 s2 h1 h2 v f fk, *)
  (* satisfies_k s1 s2 h1 h2 v f fk ->
  satisfies s1 s2 h1 h2 v (bind f fk). *)
(* Proof.
  intros.
  inverts H.
  applys s_bind.
  applys s_req.
  intros.
  specializes H1 H H2 H3.

  assumption.
  inverts H.

  applys . *)

Lemma norm_bind_assoc_k: forall f fk fk1 c,
  entails_k (bind (bind f fk) fk1) c
    (bind f (fun r => bind (fk r) fk1)) c.
Proof.
  unfold entails_k. intros.
  inverts H.
  {
    inverts H8.
    applys* sk_bind_id.
  }
  {
    inverts H8.
    applys* sk_bind.
    admit.
  }
Abort.



(** * Interpretation of a staged formula *)
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

  | s_shc : forall s1 h1 fb fk k,
    satisfies s1 s1 h1 h1
      (* (shft x shb v (fun r1 => rs (ens (fun r => \[r = v])) r1)) *)
      (shft k fb fk)
      (shc k fb fk)

    (** A [sh] on its own reduces to a [shft] containing an identity continuation. *)

  (* | s_shc s1 h1 x shb fk v :
    satisfies s1 s1 h1 h1
      (shft x shb v (fun r2 => rs fk r2))
      (shc x shb v (fun r2 => rs fk r2)) *)
    (** [shc] corresponds directly to [shft]. *)

  (* | s_seq_sh s1 s2 f1 f2 fk h1 h2 shb k (v:val) :
    satisfies s1 s2 h1 h2 (shft k shb v (fun r1 => rs fk r1)) f1 ->
    satisfies s1 s2 h1 h2 (shft k shb v (fun r1 => rs (fk;; f2) r1)) (f1;; f2) *)

  | s_bind_sh : forall s1 s2 f1 (f2:val->flow) fk h1 h2 fb k,
    satisfies s1 s2 h1 h2 (shft k fb fk) f1 ->
    satisfies s1 s2 h1 h2 (shft k fb (fun r1 => bind (fk r1) f2))
      (bind f1 f2)

    (** This rule extends the continuation in a [shft] on the left side of a [seq]. Notably, it moves whatever comes next #<i>under the reset</i>#, preserving shift-freedom by constructon. *)

  | s_rs_sh : forall k s1 s2 fr h1 h2 rf s3 h3 fb fk,
    satisfies s1 s3 h1 h3 (shft k fb fk) fr ->
    satisfies (Fmap.update s3 k (fun a => rs (fk a))) s2
      h3 h2 rf (rs fb) ->
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

  | s_discard s1 s2 h (f:var) :
    s2 = Fmap.remove s1 f ->
    satisfies s1 s2 h h (norm vunit) (discard f)

  .

Notation "s1 ',' s2 ','  h1 ','  h2 ','  r  '|=' f" :=
  (satisfies s1 s2 h1 h2 r f) (at level 30, only printing).

Lemma s_sh : forall s1 h1 fb k,
  satisfies s1 s1 h1 h1
    (shft k fb (fun r1 => ens (fun r => \[r = r1])))
    (sh k fb).
Proof.
  unfold sh. intros.
  applys* s_shc.
Qed.

Lemma s_seq : forall s3 h3 r1 s1 s2 f1 f2 h1 h2 R,
  satisfies s1 s3 h1 h3 (norm r1) f1 ->
  satisfies s3 s2 h3 h2 R f2 ->
  satisfies s1 s2 h1 h2 R (seq f1 f2).
Proof.
  unfold seq. intros.
  applys* s_bind.
Qed.

Notation s_seq_sh := s_bind_sh.

Lemma s_ens_ : forall H h1 h2 s1,
  (exists h3,
    H h3 /\
    h2 = Fmap.union h1 h3 /\
    Fmap.disjoint h1 h3) ->
  satisfies s1 s1 h1 h2 (norm vunit) (ens_ H).
Proof.
  unfold ens_. intros.
  applys* s_ens.
  heaps.
Qed.

(** A specialization of [equal_f] for exposing the equalities in continuations after inversion. *)
(* Lemma cont_inj : forall fk1 fk2,
  (fun r1 => rs fk1 r1) = (fun r2 => rs fk2 r2) ->
  fk1 = fk2.
Proof.
  intros.
  apply equal_f with (x := arbitrary) in H.
  injects H.
  reflexivity.
Qed. *)

(* Ltac cont_eq :=
  lazymatch goal with
  | H: (fun _ => rs _ _) = (fun _ => rs _ _) |- _ =>
    lets ?: cont_inj H; subst; clear H; cont_eq
  | _ => idtac
  end. *)

(* Lemma cont_inj1 : forall fk1 fk2,
  (fun r1 => fk1) = (fun r2 => fk2) ->
  fk1 = fk2.
Proof.
  intros.
  apply equal_f with (x := arbitrary) in H.
  injects H.
  reflexivity.
Qed.

Ltac cont_eq1 :=
  lazymatch goal with
  | H: (fun _ => rs _ _) = (fun _ => rs _ _) |- _ =>
    lets ?: cont_inj1 H; subst; clear H; cont_eq
  | _ => idtac
  end. *)

(** * Entailment *)
Definition entails (f1 f2:flow) : Prop :=
  forall s1 s2 h1 h2 R,
    satisfies s1 s2 h1 h2 R f1 -> satisfies s1 s2 h1 h2 R f2.

Infix "⊑" := entails (at level 90, right associativity) : flow_scope.

Inductive gentails_under : senv -> nat -> flow -> flow -> Prop :=

  | geu_base : forall s1 f1 f2,
    (forall s2 h1 h2 v,
      satisfies s1 s2 h1 h2 (norm v) f1 ->
      satisfies s1 s2 h1 h2 (norm v) f2) ->
    gentails_under s1 O f1 f2

  | geu_shift : forall s1 n f1 f2,
    (forall s2 h1 h2 k fb fk,
      satisfies s1 s2 h1 h2 (shft k fb fk) f1 ->
      exists fb1 fk1,
        satisfies s1 s2 h1 h2 (shft k fb1 fk1) f2 /\
        gentails_under s1 n fb fb1 /\
        forall v, gentails_under s1 n (fk v) (fk1 v)) ->

    gentails_under s1 (S n) f1 f2.

(* hide the index *)
Notation "env '⊢' f1 '⊆' f2" :=
  (gentails_under env _ f1 f2) (at level 90, only printing) : flow_scope.

(* Definition gentails n f1 f2 :=
  forall s1, gentails_under s1 n f1 f2. *)

Inductive gentails : nat -> flow -> flow -> Prop :=

  | ge_base : forall f1 f2,
    (forall s1 s2 h1 h2 v,
      satisfies s1 s2 h1 h2 (norm v) f1 ->
      satisfies s1 s2 h1 h2 (norm v) f2) ->
    gentails O f1 f2

  | ge_shift : forall n f1 f2,
    (forall s1 s2 h1 h2 k fb fk,
      satisfies s1 s2 h1 h2 (shft k fb fk) f1 ->
      exists fb1 fk1,
        satisfies s1 s2 h1 h2 (shft k fb1 fk1) f2 /\
        gentails n fb fb1 /\
        forall v, gentails n (fk v) (fk1 v)) ->

    gentails (S n) f1 f2.

Notation "f1 '⊆' n f2" :=
  (gentails n f1 f2) (at level 90, only printing) : flow_scope.

Lemma entails_gentails: forall n f1 f2,
  entails f1 f2 -> gentails n f1 f2.
Proof.
  unfold entails.
  intros n. induction n; intros.
  { applys* ge_base. }
  { applys ge_shift. jauto. }
Qed.

Definition entails_under s1 f1 f2 :=
  forall h1 h2 s2 R,
    satisfies s1 s2 h1 h2 R f1 -> satisfies s1 s2 h1 h2 R f2.

Notation "env '⊢' f1 '⊑' f2" :=
  (entails_under env f1 f2) (at level 90, only printing) : flow_scope.

Lemma entails_under_gentails_under: forall n s1 f1 f2,
  entails_under s1 f1 f2 -> gentails_under s1 n f1 f2.
Proof.
  unfold entails_under.
  intros n. induction n; intros.
  { applys* geu_base. }
  { applys geu_shift. jauto. }
Qed.

Definition bientails (f1 f2:flow) : Prop :=
  forall h1 h2 R s1 s2,
    satisfies s1 s2 h1 h2 R f1 <-> satisfies s1 s2 h1 h2 R f2.

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

Instance gentails_refl : forall n, Reflexive (gentails n).
Proof.
  unfold Reflexive.
  intros n. induction n; intros.
  - applys ge_base. intros.
    assumption.
  - intros.
    applys ge_shift. intros.
    exs. splits*.
Qed.

(* This is the first lemma we need the index to prove. *)
Instance gentails_trans : forall n, Transitive (gentails n).
Proof.
  unfold Transitive.
  intros n. induction n; intros.
  - inverts H. inverts H0. applys ge_base. intros.
    eauto.
  - applys ge_shift. intros.
    inverts H as H. specializes H H1. destr H.
    inverts H0 as H0. specializes H0 H2. destr H0.
    exs. splits*.
Qed.

Instance gentails_preorder : forall n, PreOrder (gentails n).
Proof.
  constructor.
  apply gentails_refl.
  apply gentails_trans.
Qed.

Instance gentails_under_refl : forall n env, Reflexive (gentails_under env n).
Proof.
  unfold Reflexive.
  intros n. induction n; intros.
  - applys geu_base. intros.
    assumption.
  - intros.
    applys geu_shift. intros.
    exs. splits*.
Qed.

Instance gentails_under_trans : forall n env, Transitive (gentails_under env n).
Proof.
  unfold Transitive.
  intros n. induction n; intros.
  - inverts H. inverts H0. applys geu_base. intros.
    eauto.
  - applys geu_shift. intros.
    inverts H as H. specializes H H1. destr H.
    inverts H0 as H0. specializes H0 H2. destr H0.
    exs. splits*.
Qed.

Instance gentails_under_preorder : forall n env, PreOrder (gentails_under env n).
Proof.
  constructor.
  apply gentails_under_refl.
  apply gentails_under_trans.
Qed.

Instance entails_under_refl : forall env, Reflexive (entails_under env).
Proof.
  unfold Reflexive, entails_under.
  intros.
  eauto.
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

Definition flow_res (f:flow) (v:val) : Prop :=
  forall s1 s2 h1 h2, satisfies s1 s2 h1 h2 (norm v) f.

(* which definition of flow_res should be used? *)
Definition flow_res1 (f:flow) (v1:val) : Prop :=
  forall s1 s2 h1 h2 v, satisfies s1 s2 h1 h2 (norm v) f -> v1 = v.
