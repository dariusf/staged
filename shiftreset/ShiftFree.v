
Require Import Coq.Program.Equality.

From ShiftReset Require Import Basics.

Implicit Types H : hprop.

(* Section ShiftFreedom. *)

(** * Shift-freedom *)
(** Semantic definition of shift-freedom. *)
Definition shift_free (f:flow) : Prop :=
  forall s1 s2 h1 h2 k fb fk,
  (* exists v, *)
    (* satisfies s1 s2 h1 h2 (norm v) f /\ *)
      not (satisfies s1 s2 h1 h2 (shft k fb fk) f).

(** [Sh#], the syntactic analogue of [shft], or a CPS version of [Sh], where the continuation is shift-free. *)
(* Definition shs x fb vr c : flow :=
  ens_ \[forall r, shift_free (c r)];; shc x fb vr c. *)

(* Notation "'shs' '(' k '.' fb ')' '(' vr '.' '⟨' fk '⟩' ')'" := (shs k fb vr (fun r => rs fk r))
  (at level 80, format "'shs'  '(' k '.'  fb ')'  '(' vr '.'  '⟨'  fk  '⟩' ')'", only printing) : flow_scope. *)

Class ShiftFree (f:flow) : Prop :=
  { shift_free_pf: shift_free f }.

Lemma sf_ens : forall Q,
  shift_free (ens Q).
Proof.
  unfold shift_free, not. intros.
  inverts H as H. destr H.
  false.
Qed.
(* this works, but relies on typeclass internals *)
(* #[local] Hint Resolve sf_ens : typeclass_instances. *)

(* previous attempt at automation *)
(* #[local] Hint Resolve sf_ens : core. *)

Lemma sf_ens_ : forall H,
  shift_free (ens_ H).
Proof.
  unfold shift_free, not. intros.
  inverts H0. destr H7.
  false.
Qed.

Instance ShiftFreeEns : forall Q,
  ShiftFree (ens Q).
Proof.
  intros. constructor. apply sf_ens.
Qed.

Instance ShiftFreeEnsVoid : forall H,
  ShiftFree (ens_ H).
Proof.
  intros. constructor. apply sf_ens_.
Qed.

Lemma sf_defun : forall x uf,
  shift_free (defun x uf).
Proof.
  unfold shift_free, not. intros.
  inverts H as H.
Qed.

Instance ShiftFreeDefun : forall x uf,
  ShiftFree (defun x uf).
Proof.
  intros. constructor. apply sf_defun.
Qed.

Lemma sf_disj : forall f1 f2,
  shift_free f1 ->
  shift_free f2 ->
  shift_free (disj f1 f2).
Proof.
  unfold shift_free, not. intros.
  inverts H1.
  eauto.
  eauto.
Qed.

Instance ShiftFreeDisj : forall f1 f2,
  ShiftFree f1 ->
  ShiftFree f2 ->
  ShiftFree (disj f1 f2).
Proof.
  intros. inverts H. inverts H0. constructor. apply* sf_disj.
Qed.

Lemma sf_empty :
  shift_free empty.
Proof.
  unfold shift_free, not. intros.
  inverts H. destr H6. discriminate.
Qed.

Instance ShiftFreeEmpty :
  ShiftFree empty.
Proof.
  intros. constructor. apply* sf_empty.
Qed.

(* This means: you can disjointly split off a heap satisfying H
  from some arbitrary heap h1, thereby demonstrating that you can
  write a req doing that by starting at h1. *)
Definition req_provable H :=
  forall h1, exists hp hr, H hp /\ h1 = hr \u hp /\ Fmap.disjoint hr hp.

Lemma sf_req : forall H f,
  req_provable H ->
  shift_free f ->
  shift_free (req H f).
Proof.
  unfold not. introv Hreq Hsf. introv H1.
  inverts H1.
  unfolds in Hreq. specializes Hreq h1. destr Hreq.
  specializes H8 H0 H1 H3.
  false Hsf H8.
Qed.

Lemma sf_req_pure : forall P f,
  P ->
  shift_free f ->
  shift_free (req \[P] f).
Proof.
  unfold shift_free, not. intros.
  inverts H1 as H2.
  specializes H2 empty_heap h1 ___.
  hintro.
  assumption.
Qed.

Lemma sf_rs_val : forall f,
  shift_free f ->
  shift_free (rs f).
Proof.
  unfold shift_free, not; intros.
  inverts H0 as H0. destr H0.
  applys~ H H0.
Qed.

Lemma sf_rs : forall f,
  shift_free (rs f).
Proof.
  unfold shift_free, not; intros.
  (* TODO try this again without dependent induction? *)
  (* remember (rs f r) as e eqn:He.
  remember (shft x k r0 b) as r1 eqn:Hr.
  induction H; try inversion He; try inversion Hr.
  injects He. subst. clear TEMP TEMP0 H1. *)
  dependent induction H.
  eapply IHsatisfies2.
  reflexivity.
  reflexivity.
Qed.

Instance ShiftFreeRs : forall f,
  ShiftFree (rs f).
Proof.
  intros.
  constructor. apply* sf_rs.
Qed.

Lemma sf_seq : forall f1 f2,
  shift_free f1 ->
  shift_free f2 ->
  shift_free (f1;; f2).
Proof.
  unfold shift_free, not. intros.
  inverts H1 as H1; destr H1.
  { specializes~ H0 H9. }
  { specializes~ H H1. }
Qed.

Instance ShiftFreeSeq : forall f1 f2,
  ShiftFree f1 ->
  ShiftFree f2 ->
  ShiftFree (f1;; f2).
Proof.
  intros.
  inverts H as H.
  inverts H0 as H0.
  constructor. apply* sf_seq.
Qed.

Lemma sf_bind : forall f fk,
  shift_free f ->
  (forall v, shift_free (fk v)) ->
  shift_free (bind f fk).
Proof.
  unfold shift_free, not; intros.
  inverts H1.
  - false H0 H10.
  - false H H7.
Qed.

Instance ShiftFreeBind : forall f fk,
  ShiftFree f ->
  (forall v, ShiftFree (fk v)) ->
  ShiftFree (bind f fk).
Proof.
  intros.
  inverts H.
  constructor. apply* sf_bind.
  intros. specializes H0 v. inverts* H0.
Qed.

(* Definition returns_value (f:flow) : Prop :=
  forall s1 s2 h1 h2 v, satisfies s1 s2 h1 h2 (norm v) f.

Lemma sf_seq_inv : forall f1 f2,
  shift_free (f1;; f2) ->
  shift_free f1 /\ (returns_value f1 -> shift_free f2).
Proof.
  unfold shift_free, not. intros.
  split; intros.
  { eapply H.
    eapply s_seq_sh.
    exact H0. }
  { unfold returns_value in H0.
  (* destr H0. *)
    eapply H.
    eapply s_seq.
    2: eassumption.
    apply H0.

    }
Qed. *)

Lemma sf_fex : forall A (p:A->flow),
  (forall b, shift_free (p b)) ->
  shift_free (@fex A p).
Proof.
  unfold shift_free, not. intros.
  inverts H0 as H0. destr H0.
  eapply H.
  exact H1.
Qed.

Lemma sf_fall : forall A (p:A->flow) b,
  shift_free (p b) ->
  shift_free (@fall A p).
Proof.
  unfold shift_free, not. intros.
  inverts H0 as H0. destr H0.
  specializes H0 b.
  eapply H.
  eassumption.
Qed.

Lemma sf_seq_inv : forall f1 f2,
  shift_free (f1;; f2) ->
  shift_free f1 /\ shift_free f2.
Proof.
  unfold shift_free, not. intros.
  split; intros.
  { eapply H.
    apply s_bind_sh.
    eassumption. }
  { eapply H.
    eapply s_seq.
    2: eassumption.
    (* TODO need to know that shift-free means
      f1 goes to norm, possible to add *)
    admit.
  }
Abort.

Lemma sf_seq_inv1 : forall f1 f2,
  shift_free (f1;; f2) ->
  shift_free f1.
Proof.
  unfold shift_free, not. intros.
  eapply H.
  apply s_bind_sh.
  eassumption.
Qed.

(* Ltac shiftfree :=
  lazymatch goal with
  | |- shift_free (rs _) => apply sf_rs
  | |- shift_free (defun _ _) => apply sf_defun
  | |- shift_free (ens _) => apply sf_ens
  (* | |- shift_free (req _ _) => apply sf_req *)
  | |- shift_free (ens_ _) => unfold ens_; apply sf_ens
  | |- shift_free (_ ;; _) => apply sf_seq; shiftfree
  | |- shift_free (bind _ _) => apply sf_bind; shiftfree
  | |- shift_free (fex _) => apply sf_fex; intros; shiftfree
  | _ => auto
  end. *)

Create HintDb staged_shiftfree.
Global Hint Resolve
  sf_ens sf_ens_ sf_defun sf_seq sf_bind sf_disj sf_empty
  sf_req_pure sf_fex sf_fall sf_rs
  (* sf_rs_val *)
  : staged_shiftfree.

Ltac shiftfree := intros; auto with staged_shiftfree.

(* Immediately dispatch goals where we have an assumption that
  a shift-free thing produces a shift,
  or a shift_free assumption that can be used *)
Ltac no_shift :=
  lazymatch goal with
  | H: satisfies _ _ _ _ (shft _ _ _) empty |- _ =>
    false sf_empty H
  | H: satisfies _ _ _ _ (shft _ _ _) (ens _) |- _ =>
    false sf_ens H
  | H: satisfies _ _ _ _ (shft _ _ _) (ens_ _) |- _ =>
    unfold ens_ in H; false sf_ens H
  | H: satisfies _ _ _ _ (shft _ _ _) (rs _ _) |- _ =>
    false sf_rs H
  | H: satisfies _ _ _ _ (shft _ _ _) (defun _ _) |- _ =>
    false sf_defun H
  | H: satisfies _ _ _ _ (shft _ _ _) ?f, Hsf: shift_free ?f |- _ =>
    false Hsf H
  | _ => idtac
  end.

(* Ltac vacuity ::= false; no_shift. *)

(* knowing that there is one norm execution does not mean
  that there are no shift executions *)
Lemma norm_sf_attempt : forall s1 s2 h1 h2 v f,
  satisfies s1 s2 h1 h2 (norm v) f ->
  shift_free f.
Proof.
  intros * Hf.
  unfold shift_free. intros * H.
Abort.

Definition det f := forall s1 s2 h1 h2 R1 R2,
  satisfies s1 s2 h1 h2 R1 f ->
  satisfies s1 s2 h1 h2 R2 f ->
  R1 = R2.

(* if all executions end in norm and f is deterministic,
  then f is shift-free. *)
Lemma norm_sf : forall f,
  det f ->
  (forall s1 s2 h1 h2, exists v, satisfies s1 s2 h1 h2 (norm v) f) ->
  shift_free f.
Proof.
  intros * Hd Hf.
  unfold shift_free. intros * H.
  specializes Hf s1 s2 h1 h2.
  destr Hf.
  specializes Hd H H0.
  discriminate.
Qed.

(* End ShiftFreedom. *)