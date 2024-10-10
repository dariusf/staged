From Coq Require Import Classes.RelationClasses.
From Coq Require Morphisms Program.Basics.

From SLF Require LibSepFmap.
Module Fmap := LibSepFmap.

From SLF Require Export Extra Heap Tactics.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Set Implicit Arguments.

(** * Programs *)
(** The representation of programs, substitution, and the big-step semantics are mostly reused from SLF. *)
Definition ident : Type := string.
Definition ident_eq := String.string_dec.

Inductive val :=
| vunit : val
| vint : Z -> val
| vfun : ident -> expr -> val
| vfix : ident -> ident -> expr -> val

with expr : Type :=
| pvar (x : ident)
| pval (v : val)
| plet (x : ident) (e1 e2 : expr)
| pfix (f : ident) (x : ident) (e : expr)
| pfun (x : ident) (e : expr)
| padd (x y : val)
| pif (x : val) (e1 : expr) (e2 : expr)
| pcall (x : val) (a : val).

Instance Inhab_val : Inhab val.
Proof.
  constructor.
  exists vunit.
  constructor.
Qed.

Fixpoint subst (y : ident) (w : val) (e : expr) : expr :=
  let aux t := subst y w t in
  let if_y_eq x t1 t2 := if ident_eq x y then t1 else t2 in
  match e with
  | pval v => pval v
  | padd x y => padd x y
  | pvar x => if_y_eq x (pval w) e
  | pfun x t1 => pfun x (if_y_eq x t1 (aux t1))
  | pfix f x t1 => pfix f x (if_y_eq f t1 (if_y_eq x t1 (aux t1)))
  | pcall t1 t2 => pcall t1 t2
  | plet x t1 t2 => plet x (aux t1) (if_y_eq x t2 (aux t2))
  | pif t0 t1 t2 => pif t0 (aux t1) (aux t2)
  end.

Unset Implicit Arguments.

Module Val.
  Definition val := val.
End Val.

Module Export Heap := Heap.HeapSetup Val.

Definition empty_heap : heap := Fmap.empty.

Definition precond := hprop.
Definition postcond := val -> hprop.
Definition state := hprop.

Inductive result : Type :=
| top : result
| norm : val -> result.

(** * Staged formulae *)
(** Deeply embedded due to uninterpreted functions, which cannot immediately be given a semantics without an environment. *)
Inductive flow :=
| req : precond -> flow
| ens : postcond -> flow
| seq : flow -> flow -> flow
| fex : forall A, (A -> flow) -> flow
| fall : forall A, (A -> flow) -> flow
| unk : ident -> val -> val -> flow
| disj : flow -> flow -> flow.

(** An [ens] which doesn't have a useful return value. *)
Definition ens_ Q := ens (fun r => \[r = vunit] \* Q).

(** Function environments, for interpreting unknown functions. [ufun] is a HOAS way of substituting into a staged formula, which otherwise doesn't support this due to the shallow embedding that [hprop] uses. *)
Definition ufun : Type := val -> val -> flow. (* f(x, r) = \phi *)
Definition env : Type := fmap ident (option ufun).

Definition empty_env : env := Fmap.empty.

(** * Interpretation of a staged formula *)
(** Differs from the paper's definition in:

- the addition of an environment, to give interpretations for unknown functions
- the removal of stores, to sidestep impredicativity problems
- the definition of [req], whose variance has been fixed

An [Inductive] definition is used because the rule for unknown functions is not structurally recursive. *)
Inductive satisfies (e : env) : state -> state -> val -> flow -> Prop :=
(* req P *)
| s_req (S S' : state) (P : precond) :
  (S \* P ==> S') ->
  satisfies e S S' vunit (req P)
(* ens Q *)
| s_ens (S S' : state) (v : val) (Q : postcond) :
  (S ==> Q v) ->
  (S ==> S') ->
  satisfies e S S' v (ens Q)
(* F1 ; F2 *)
| s_seq (S0 S1 S2 : state) (v1 v2 : val) (F1 F2 : flow) :
  satisfies e S0 S1 v1 F1 ->
  satisfies e S1 S2 v2 F2 ->
  satisfies e S0 S2 v2 (seq F1 F2)
(* F1 \/ F2 when F1 *)
| s_disj_l (S S' : state) (v : val) (F1 F2 : flow) :
  satisfies e S S' v F1 ->
  satisfies e S S' v (disj F1 F2)
(* F1 \/ F2 when F2 *)
| s_disj_r (S S' : state) (v : val) (F1 F2 : flow) :
  satisfies e S S' v F2 ->
  satisfies e S S' v (disj F1 F2)
(* ex a, FA *)
| s_fex (S S' : state) (v : val) (A : Type) (FA : A -> flow) :
  (exists a, satisfies e S S' v (FA a)) ->
  satisfies e S S' v (fex A FA)
(* all a, FA *)
| s_fall (S S' : state) (v : val) (A : Type) (FA : A -> flow) :
  (forall a, satisfies e S S' v (FA a)) ->
  satisfies e S S' v (fall A FA).

Module Example.

  Goal exists S', satisfies empty_env \[True]  S' (vint 1) (fex Z (fun x => seq (req \[x = 1]) (ens (fun r => \[r = vint x])))).
    eexists.
    eapply s_fex. exists 1.
    eapply s_seq.
    - eapply s_req. apply himpl_refl.
    - eapply s_ens.
      + admit. (* provable, although idk how to write it *)
      + apply himpl_refl.
  Abort.

  (*
  Goal exists S', satisfies empty_env True S' (vint 1) (fex Z (fun x => seq (req (x <> 1)) (ens (fun r => r = vint x)))).
    eexists.
    eapply s_fex. exists 1.
    eapply s_seq.
    - eapply s_req. intro H. exact H.
    - eapply s_ens. tauto.
  Qed.
   *)

  Goal exists S', satisfies empty_env \[True] S' (vint 1) (fall Z (fun x => seq (req \[x = 1]) (ens (fun r => \[r = vint x])))).
    eexists.
    eapply s_fall. intros a.
    eexists. eapply s_seq.
    - eapply s_req. apply himpl_refl.
    - eapply s_ens.
      + admit.
      + apply himpl_refl.
  Admitted.

  (*
  Goal exists S', satisfies empty_env True S' (vint 1) (fall Z (fun x => seq (req (x = 2)) (ens (fun r => r = vint x)))).
    (* should fail *)
    eexists. eapply s_fall. intros a.
    eexists. eapply s_seq.
    - eapply s_req. intro H. exact H.
    - eapply s_ens. intuition. subst. (* fail *)
  Abort.

  Goal exists S', satisfies empty_env True S' (vint 1) (ens (fun r => r = vint 2)).
    (* should fail *)
    eexists. eapply s_ens. intuition. (* fail *)
  Abort.

  Goal (forall C : Prop)

                     ~  ( C /\ P ) ->
                     (Q -> Q1) ->
                     env, S, S', err |=  req P ; ens Q ->
         env, S, S', err |= req P1 ; ens Q1
   *)


End Example.

Lemma satisfies_req :
  forall (e : env)
         (S S' : state)
         (v : val)
         (P1 P2 : precond),
    (P2 ==> P1) ->
    satisfies e S S' v (req P1) ->
    satisfies e S S' v (req P2).
Proof.
  intros e S S' v P1 P2 H_impl H_sat.
  inverts H_sat as H_sat.
  constructor.
  Search (_ \* _ ==> _).
  Check (himpl_hstar_trans_r H_impl H_sat).
  exact (himpl_hstar_trans_r H_impl H_sat).
Qed.

Lemma satisfies_ens :
  forall (e : env)
         (S S' : state)
         (v : val)
         (Q1 Q2 : postcond),
    (Q1 ===> Q2) ->
    satisfies e S S' v (ens Q1) ->
    satisfies e S S' v (ens Q2).
Proof.
  intros e S S' v Q1 Q2 H_impl H_sat.
  inverts H_sat as H_sat H_S.
  specialize (H_impl v).
  constructor.
  - Search (_ ==> _ -> _ ==> _ -> _).
    Check (himpl_trans H_sat H_impl).
    exact (himpl_trans H_sat H_impl).
  - exact H_S.
Qed.

(** * Entailment *)
(** This is defined directly in terms of the semantics, in contrast to the paper's syntactic definition. *)

Definition entails_under (e : env) (S S' : state) (v : val) (F1 F2 : flow) : Prop :=
  satisfies e S S' v F1 -> satisfies e S S' v F2.

Definition entails (F1 F2 : flow) : Prop :=
  forall (e : env)
         (S S' : state)
         (v : val),
    entails_under e S S' v F1 F2.

Definition bientails (F1 F2 : flow) : Prop :=
  entails F1 F2 /\ entails F2 F1.

Infix "⊑" := entails (at level 90, right associativity) : flow_scope.

(* Unset Printing Notations. Set Printing Coercions. Set Printing Parentheses. *)
(* Check (forall f1 f2 f3, f1 ;; f3 ⊑ f2). *)

(** * Inversion/introduction lemmas *)
(*
Lemma ens__ret_inv :
  forall e H r,
  satisfies env (ens_ H) h1 h2 r ->
  r = norm vunit.
Proof.
  intros.
  inverts H0 as H0.
  destruct H0 as (?&h3&H1&H2&H3&H4).
  rewrite hstar_hpure_l in H2.
  destruct H2.
  congruence.
Qed.

Lemma ens_empty_inv : forall env h1 h2 r,
  satisfies env (ens (fun r => \[])) h1 h2 r -> h1 = h2.
Proof.
  intros.
  inverts H.
  destr H2.
  apply hempty_inv in H0.
  subst.
  fmap_eq.
Qed.

Lemma ens_empty_intro : forall env h1 v,
  satisfies env (ens (fun r => \[])) h1 h1 (norm v).
Proof.
  intros.
  apply s_ens.
  exists v.
  exists empty_heap.
  intuition fmap_eq.
  constructor.
Qed.

Lemma ens_pure_inv : forall P env h1 h2 r,
  satisfies env (ens (fun _ => \[P])) h1 h2 r -> P /\ h1 = h2.
Proof.
  intros.
  inverts H as H.
  destr H.
  inverts H.
  inverts H2.
  intuition.
Qed.

Lemma ens_pure_intro : forall P env h v,
  P -> satisfies env (ens (fun _ => \[P])) h h (norm v).
Proof.
  intros.
  constructor.
  exists v.
  exists empty_heap.
  intuition.
  apply hpure_intro; easy.
  fmap_eq.
Qed.

Lemma unk_inv : forall env h1 h2 r1 x f1 f r,
  satisfies env (unk f x r1) h1 h2 r ->
  Fmap.read env f = Some f1 ->
  satisfies env (f1 x r1) h1 h2 r.
Proof.
  intros.
  inverts H as H.
  rewrite H in H0.
  inj H0.
  easy.
Qed.

(** * Tactics for reasoning about entailments *)
Ltac felim H :=
  match type of H with
  | satisfies _ (fex _) _ _ _ => inverts H as H
  | satisfies _ (_ ;; _) _ _ _ => inverts H as H
  | satisfies _ (ens (fun _ => \[_])) _ _ _ => apply ens_pure_inv in H
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
  | |- satisfies _ (ens (fun _ => \[_])) _ _ _ => apply ens_pure_intro
  | |- satisfies _ (ens (fun _ => \[])) _ _ _ => apply ens_empty_intro
  | |- \[] _ => apply hempty_intro
  | |- \[_] _ => apply hpure_intro
  | |- (_ \* _) (_ \u _) => apply hstar_intro
  | |- (\[_] \* \[_]) _ => idtac "use rewrite hstar_hpure_l or hstar_hpure_r"
  | |- (\[_] \* _) _ => rewrite hstar_hpure_l
  | |- (_ \* \[_]) _ => rewrite hstar_hpure_r
  (* | |- satisfies _ (req \[]) _ _ _ => apply req_empty_intro *)
  (* | |- satisfies _ (req \[];; _) _ _ _ => apply seq_req_emp_intro_l *)
  end.

(* Ltac fexists v :=
  match goal with
  | |- satisfies _ (fex _) _ _ _ => unfold fex; exists v
  end. *)

(** * Entailment/normalization rules *)
(** Covariance of ens *)
Lemma satisfies_ens : forall Q1 Q2 env h1 h2 r,
  (forall v, Q1 v ==> Q2 v) ->
  satisfies env (ens Q1) h1 h2 r ->
  satisfies env (ens Q2) h1 h2 r.
Proof.
  intros.
  inverts H0.
  constructor.
  destruct H3 as (v&h3&?&?&?&?).
  exists v.
  exists h3.
  intuition.
  apply H.
  easy.
Qed.
*)

(* Lemma entails_ens : forall Q1 Q2,
  (forall v, Q1 v ==> Q2 v) -> entails (ens Q1) (ens Q2).
Proof.
  unfold entails.
  intros.
  split.
  { intros. left.
  (* Check satisfies_ens. *)
  (* rewrite satisfies_ens. *)
  apply (satisfies_ens Q1).
  }
  applys* satisfies_ens.
Qed.

Lemma entails_req : forall H1 H2 f,
  (H2 ==> H1) -> entails (req H1 f) (req H2 f).
Proof.
  unfold entails.
  intros.
  applys* satisfies_req H1.
Qed. *)

(** seq is associative *)
Lemma seq_assoc :
  forall (e : env)
         (S S' : state)
         (v : val)
         (F1 F2 F3 : flow),
    satisfies e S S' v (seq F1 (seq F2 F3)) <-> satisfies e S S' v (seq (seq F1 F2) F3).
Proof.
  intros e S S' v F1 F2 F3.
  split; intros H.
  { inverts H as H_1 H_23.
    inverts H_23 as H_2 H_3.
    eapply s_seq.
    eapply s_seq.
    - exact H_1.
    - exact H_2.
    - exact H_3. }
  { inverts H as H_12 H_3.
    inverts H_12 as H_1 H_2.
    eapply s_seq.
    2: eapply s_seq.
    - exact H_1.
    - exact H_2.
    - exact H_3. }
Qed.

Lemma ent_ens_seq :
  forall (Q1 Q2 : postcond)
         (F1 F2 : flow),
    (Q1 ===> Q2) ->
    entails F1 F2 ->
    entails (seq (ens Q1) F1) (seq (ens Q2) F2).
Proof.
  unfold entails in *.
  unfold entails_under in *.
  intros Q1 Q2 F1 F2 H_impl H_ent e S S' v H_sat.
  inverts H_sat as H_Q1 H_F1.
  eapply s_seq.
  - eapply satisfies_ens. exact H_impl. exact H_Q1.
  - eapply H_ent. exact H_F1.
Qed.

Lemma ent_req_seq :
  forall (P1 P2 : precond)
         (F1 F2 : flow),
    (P2 ==> P1) ->
    entails F1 F2 ->
    entails (seq (req P1) F1) (seq (req P2) F2).
Proof.
  unfold entails in *.
  unfold entails_under in *.
  intros P1 P2 F1 F2 H_impl H_ent e S S' v H_sat.
  inverts H_sat as H_P1 H_F1.
  eapply s_seq.
  - eapply satisfies_req. exact H_impl. exact H_P1.
  - eapply H_ent. exact H_F1.
Qed.

Lemma norm_req_req :
  forall P1 P2,
    bientails (req (P1 \* P2)) (seq (req P1) (req P2)).
Proof.
  unfold bientails.
  unfold entails.
  unfold entails_under.
  intros P1 P2.
  split.
  - intros e S S' v H_sat.
    inverts H_sat as H_sat.
    eapply s_seq.
    + eapply s_req. apply himpl_refl.
    + eapply s_req. rewrite hstar_assoc. exact H_sat.
  - intros e S S' v H_sat.
    inverts H_sat as H_P1 H_P2.
    inverts H_P1 as H_P1.
    inverts H_P2 as H_P2.
    eapply s_req. admit. (* provable *)
Admitted.

(** Reassociating req *)
(* Lemma satisfies_reassoc : forall H f env h1 h2 r,
  satisfies env (req_ H;; f) h1 h2 r ->
  satisfies env (req H f) h1 h2 r.
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

  (* find out about hr *)
  inverts H1 as H1. destr H1.
  finv H1. finv H1. finv H7. subst. rew_fmap *.
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
  specialize (H _ (hr \u hH2) H0).
  forward H. fmap_eq.
  forward H. fmap_disjoint.

  inverts H as H.
  specialize (H _ hr H5).
  forward H. fmap_eq.
  forward H. fmap_disjoint.

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
  specialize (H (hH1 \u hH2) hr).
  forward H. apply hstar_intro; auto.
  forward H. fmap_eq.
  forward H. fmap_disjoint.

  auto.
Qed.

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
  satisfies env (ens_ (H1 \* H2)) h1 h2 r <->
  satisfies env (ens_ H1;; ens_ H2) h1 h2 r.
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
    inv H3. destr H5. inv H4. destr H8. subst.
    constructor.
    exists v0.
    exists (h0 \u h3).
    rewrite hstar_hpure_l in H0.
    rewrite hstar_hpure_l in H3.
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

(** Splitting and combining [ens] with results is more complex, and there does not seem to be a single equivalence. *)
(* Lemma satisfies_ens_sep_combine : forall Q1 Q2 env h1 h2 r,
  satisfies env (ens Q1;; ens Q2) h1 h2 r ->
  satisfies env (ens (fun r0 : val => \exists r1 : val, Q1 r1 \* Q2 r0)) h1 h2 r.
Proof.
  intros.
  felim H.
  destruct H as (h3 & r1 & H1 & H2).

  constructor.
  (* destruct r. *)
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
Qed. *)

(* Lemma norm_ens_ens_combine : forall Q1 Q2,
  entails (ens Q1;; ens Q2) (ens (fun r => \exists r1, Q1 r1 \* Q2 r)).
Proof.
  unfold entails.
  apply satisfies_ens_sep_combine.
Qed. *)

Lemma satisfies_ens_sep_split : forall H Q env h1 h2 r,
  satisfies env (ens (Q \*+ H)) h1 h2 r  ->
  satisfies env (ens (fun _ : val => H);; ens Q) h1 h2 r.
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
  satisfies env (ens_ (x~~>a \* H1);; req (x~~>a \* H2) f) h1 h2 r ->
  satisfies env (ens_ H1;; req H2 f) h1 h2 r.
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

(** The [Float Pre] rule from the paper. *)
Lemma norm_ens_req_transpose : forall H2 H1 Ha Hf (v:val) f,
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
  Definition f2 : flow := fex (fun x => req_ (\[x = vint 1])).
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

  Example ex3_req_ret: flow_res f2 vunit.
  Proof.
    unfold flow_res.
    exists empty_heap.
    exists empty_heap.
    exists empty_env.
    unfold f2.
    apply (s_fex).
    exists (vint 1).
    constructor.
    intros.
    constructor.
    exists vunit.
    exists empty_heap.
    intuition.
    fmap_eq.
    rewrite hstar_hpure_r.
    intuition.
    fintro. reflexivity.
    finv H.
    subst. rew_fmap.
    unfold empty_heap in *.
    fmap_eq.
  Qed.

  Definition f4 : flow := empty ;; fex (fun r => unk "f" (vint 1) r).
  Definition f4_env : env :=
    Fmap.update empty_env "f" (Some (fun _ r => ens (fun r1 => \[r = vint 2]))).

  (* has to be 2 *)
  Example ex5_f_ret: flow_res f4 (vint 2).
  Proof.
    unfold flow_res.
    exists empty_heap. exists empty_heap. exists f4_env.
    unfold f4.
    constructor. exists empty_heap. exists (norm vunit). intuition.
    constructor.
    eexists.
    exists empty_heap.
    intuition.
    rewrite hstar_hpure_l.
    intuition.
    fintro. constructor.
    fmap_eq.

    constructor.
    exists (vint 2).
    econstructor.
    unfold f4_env.

    rewrite fmap_read_update.
    reflexivity.
    apply fmap_indom_empty.

    simpl.
    fintro.
    reflexivity.
  Qed.

  Example ex4: forall h,
    satisfies (Fmap.update empty_env "f" (Some (fun x r1 => ens (fun r => \[r1 = r /\ r = x])))) f4 h h (norm (vint 1)).
  Proof.
    intros.
    constructor.
    exists h.
    exists (norm vunit).
    split.

    - constructor.
      eexists.
      exists empty_heap.
      intuition.

      rewrite hstar_hpure_l.
      intuition.
      fintro.
      constructor.
      fmap_eq.

    - eapply s_fex.
      exists (vint 1).
      eapply s_unk.
      rew_fmap.
      reflexivity.

      apply fmap_indom_empty.
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
    satisfies empty_env (req_ \[x = 1]) empty_heap empty_heap (norm vunit).
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
    satisfies empty_env (req (x~~>vint 1) (ens_ (x~~>vint 1))) (Fmap.single x (vint 1)) (Fmap.single x (vint 1)) (norm vunit).
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
    satisfies empty_env ((ens_ (x~~>vint 1)) ;; req_ (x~~>vint 1)) empty_heap empty_heap (norm vunit).
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
    satisfies empty_env (req_ \[False])
      (Fmap.single x (vint 1)) (Fmap.single x (vint 2)) (norm vunit).
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

  (* lfp interpretation *)
  (*
    forall n res, sum(n, res) =
         n=0/\res=0
      \/ ex n1. ens n=n1/\n1>0; ex r1. sum(n-1,r1); ens res=1+r1
  *)
  Definition sum n res :=
    (* fall (fun n => fall (fun res => *)
    disj
      (ens (fun _ => \[exists n1, n = vint n1 /\ n1 <= 0 /\ res = vint 0]))
      (fex (fun n1 => ens (fun r => \[n = vint n1 /\ n1 > 0]);; fex (fun r1 =>
        (unk "sum" (vint (n1-1)) (vint r1);;
          ens (fun _ => \[res = vint (1 + r1)])))))
          (* )) *)
          .

  Definition sum_env := (Fmap.update empty_env "sum" (Some sum)).
  Definition sum_property (n res:val) := ens (fun _ => \[res = n]).

  (* Close Scope flow_scope. *)

  Lemma ex_sum : forall n1 n res, n1 >= 0 ->
    n = vint n1 ->
    entails_under sum_env (sum n res) (sum_property n res).
  Proof.
    unfold sum_property.
    (* do induction on the numeric value of n *)
    intros n.
    induction_wf IH: (downto 0) n.
    unfold sum.
    intros.
    inverts H1 as H1.
    (* base case *)
    { inverts H1 as H1. destr H1. finv H1. destr H1. subst. inj H1.
      constructor.
      exists v. exists empty_heap.
      intuition.
      fintro.
      f_equal.
      math. }
    (* recursive case *)
    { felim H1. destruct H1 as (v&H1).
      felim H1. destruct H1 as (h3&r1&H1&H2).

      felim H2. destruct H2 as (v0&H2).
      felim H2. destruct H2 as (h0&r0&H2&H3).
      (* H1: shape of input *)
      (* H2: call to sum *)
      (* H3: shape of res *)

      unfold sum_env in H2.
      inverts H2 as H4 Hr.
      rewrite fmap_read_update in H4. inj H4.

      (* Hr: known call to sum *)

      felim H1. destr H1.
      subst.
      inj H1.

      specialize (IH (v-1)).
      forward IH. unfold downto. math.
      specialize (IH (vint (v-1)) (vint v0)).
      forward IH. math.
      forward IH. reflexivity.
      specialize (IH _ _ _ Hr).

      felim IH. destr IH. inj H0.
      rewrite one_plus_minus_one_r in H3.
      exact H3.
      apply fmap_indom_empty. }
  Qed.

(* TODO *)
Definition foldr :=
  ens (fun _ => \[True]) ;;
  disj
    (unk "f" (vint 2) (vint 3))
    (unk "foldr" (vint 1) (vint 1);;
      unk "f" (vint 2) (vint 1)).

End Examples.

(** * Hoare rules *)
(* TODO define semantic triples, then define these as lemmas *)
Inductive forward : expr -> flow -> Prop :=
  | fw_val: forall n,
    forward (pval n) (ens (fun res => \[res = n]))

  (* there is no need for fw_var/a store because substitution will take care of it before it is reached *)

  | fw_let: forall x e1 e2 f1 f2 v,
    forward e1 f1 ->
    flow_res f1 v ->
    forward (subst x v e2) f2 ->
    forward (plet x e1 e2) (f1 ;; f2).

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

End ForwardExamples. *)