
(* From Coq Require Import ZArith Lia Bool List String Program.Equality Classes.RelationClasses. *)
From Coq Require Import Classes.RelationClasses.

Set Implicit Arguments.
From SLF Require Export LibString LibCore.
From SLF Require Export LibSepTLCbuffer LibSepFmap.
From SLF Require Export Heap.
Module Fmap := LibSepFmap.

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

Module Val.
  Definition val := val.
End Val.

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

Module Export Heap := Heap.HeapSetup(Val).

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

Lemma req_sep_split : forall H1 H2,
  entails (req (H1 \* H2)) (req H1;; req H2).
Proof.
  unfold entails.
  intros.
  inverts H as H.
  (* h3 is the piece satisfying H1*H2 *)
  destruct H as (h3 & r1 & H3 & H4).
  apply hstar_inv in H4.
  destruct H4 as (h0 & h4 & ? & ? & ? & ?).
  (* split h3. h0 is for H1, h4 for H2 *)
  subst h1.
  constructor.
  exists (h2 \u h4).
  exists r.
  split; constructor.
  exists h0. intuition fmap_eq.
  fmap_eq.
  exists h4. intuition fmap_eq.
Qed.

Lemma req_sep : forall H1 H2,
  bientails (req (H1 \* H2)) (req H1;; req H2).
Proof.
  intros.
  split.
  - apply req_sep_split.
  - apply req_sep_combine.
Qed.

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

  (* TODO plus *)
  (* TODO forall *)
  (* a lfp interpretation *)
  Definition sum :=
    disj
      (ens (fun r => \[r = vint 1]))
      (fex (fun r1 =>
        (unk "sum" (vint 1) r1;; ens (fun r => \[r = r1])))).

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