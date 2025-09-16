
From ShiftReset Require Import Basics Norm ShiftFree Satisfies.

Lemma gentl_disj_l : forall n f1 f2 f3,
  gentails n f1 f3 ->
  gentails n f2 f3 ->
  gentails n (disj f1 f2) f3.
Proof.
  intros n. induction n as [n IH] using lt_wf_ind.
  destruct n; intros.
  { inverts H. inverts H0.
    applys* ge_base. intros.
    inverts* H0. }
  { inverts H. inverts H0.
    applys* ge_shift; intros.
    {
      specializes H2 H.
      specializes H1 H.
      specializes IH H2 H1. lia.
    }
    { inverts H.
      { specializes H3 H10. destr H3.
        exs. splits*. }
      { specializes H4 H10. destr H4.
        exs. splits*. } } }
Qed.

Lemma gentl_ex_l : forall n f A (fctx:A -> flow),
  (forall b, gentails n (fctx b) f) ->
  gentails n (fex (fun b => fctx b)) f.
Proof.
Admitted.

Lemma gentl_seq_ex_l : forall n f f1 A (fctx:A -> flow),
  (forall b, shift_free (fctx b)) ->
  (forall b, gentails n (fctx b;; f1) f) ->
  gentails n ((∃ b, fctx b);; f1) f.
Proof.
Admitted.

Lemma gentl_seq_ens_pure_l : forall n f f1 (P:val->Prop),
  (forall r, P r -> gentails n f1 f) ->
  gentails n (ens (fun r => \[P r]);; f1) f.
Proof.
Admitted.

Lemma gentl_seq_defun_ens_pure_l : forall n (f:var) u f2 f1 (P:val->Prop),
  (forall r, P r -> gentails n (defun f u;; f1) f2) ->
  gentails n (defun f u;; ens (fun r => \[P r]);; f1) f2.
Proof.
Admitted.

Lemma gentl_seq_ens_void_pure_l : forall n f f1 P,
  (P -> gentails n f1 f) ->
  gentails n (ens_ \[P];; f1) f.
Proof.
Admitted.

Lemma gentl_seq_defun_ens_void_pure_l : forall n (f:var) u f2 f1 P,
  (P -> gentails n (defun f u;; f1) f2) ->
  gentails n (defun f u;; ens_ \[P];; f1) f2.
Proof.
Admitted.

Lemma gentl_ens_single : forall n Q Q1,
  (Q1 ===> Q) ->
  gentails n (ens Q1) (ens Q).
Proof.
Admitted.

Lemma gentl_req_req : forall n f1 f2 H1 H2,
  H2 ==> H1 ->
  gentails n f1 f2 ->
  gentails n (req H1 f1) (req H2 f2).
Proof.
Admitted.

Lemma gentl_defun_req_req: forall n (f:var) u f1 f2 H1 H2,
  H2 ==> H1 ->
  gentails n (defun f u;; f1) f2 ->
  gentails n (defun f u;; req H1 f1) (req H2 f2).
Proof.
Admitted.

Lemma gentl_req_l : forall n f f1 P,
  P ->
  gentails n f1 f ->
  gentails n (req \[P] f1) f.
Proof.
Admitted.

Lemma gentl_defun_req_l : forall n (f:var) u f1 f2 P,
  P ->
  gentails n (defun f u;; f1) f2 ->
  gentails n (defun f u;; req \[P] f1) f2.
Proof.
Admitted.


Lemma gentl_req_r : forall n f f1 H,
  gentails n (ens_ H;; f) f1 ->
  gentails n f (req H f1).
Proof.
Admitted.
