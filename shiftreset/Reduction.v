
From ShiftReset Require Import Basics ShiftFree.

(** * New reduction rules *)

Lemma red_init : forall fb k,
  entails (sh k fb) (shc k fb (fun v => ens (fun r => \[r = v]))).
Proof.
  unfold sh.
  intros. reflexivity.
Qed.

Lemma red_extend : forall k fb fk fk1,
  entails (bind (shc k fb fk) fk1)
    (shc k fb (fun v => bind (fk v) fk1)).
Proof.
  unfold entails. intros.
  inverts H.
  inverts H7.
  inverts H6.
  applys* s_shc.
Qed.

(* RNorm1 is seq_assoc *)
(* RNorm2 is ?? *)

(* aka red_skip *)
Lemma red_rs_float1 : forall f1 f2,
  shift_free f1 ->
  entails (rs (f1;; f2)) (f1;; rs f2).
Proof.
  introv Hsf.
  unfold entails. intros.
  inverts H as H; destr H.
  { (* if either f1 or f2 produce a shift *)
    inverts H as H. destr H.
    { (* f2 produces a shift *)
      eapply s_seq.
      exact H.
      eapply s_rs_sh.
      exact H8. eassumption. }
    { (* f1 cannot produce a shift as it is shift-free *)
      apply Hsf in H.
      false. } }
  { (* if f1 returns *)
    inverts H as H. destr H.
    eapply s_seq.
    exact H.
    apply s_rs_val.
    assumption. }
Qed.

(* TODO <-? *)
Lemma red_rs_float2 : forall f1 f2,
  entails (rs (disj f1 f2)) (disj (rs f1) (rs f2)).
Proof.
  introv H.
  unfold entails. intros.
  inverts H.
  { inverts H1.
    { applys s_disj_l.
      applys* s_rs_sh. }
    { applys s_disj_r.
      applys* s_rs_sh. } }
  { inverts H6.
    { applys s_disj_l. applys* s_rs_val. }
    { applys s_disj_r. applys* s_rs_val. } }
Qed.


Lemma red_rs_elim : forall f,
  shift_free f ->
  bientails (rs f) f.
Proof.
  introv Hsf. iff H.
  { inverts* H. }
  { destruct* R.
    applys* s_rs_val. }
Qed.

(* this one is slightly easier to use *)
Lemma red_rs_ens : forall Q,
  bientails (rs (ens Q)) (ens Q).
Proof.
  iff H.
  { applys red_rs_elim. shiftfree. assumption. }
  { applys red_rs_elim. shiftfree. assumption. }
Qed.

Lemma red_rs_sh_elim : forall k fb fk,
  entails (rs (shc k fb fk))
    (defun k (fun v => rs (fk v));; rs fb).
Proof.
  unfold entails. intros.
  inverts H. 2: { false_invert H6. }
  inverts H1.
  inverts H7.
  { (* body has shift *)
    applys s_seq. { applys* s_defun. }
    applys* s_rs_sh. }
  { (* body has no shift *)
    applys s_seq. { applys* s_defun. }
    applys* s_rs_val. }
Qed.