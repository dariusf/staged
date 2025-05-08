
From ShiftReset Require Import Basics ShiftFree.

(** * Reduction rules *)
Lemma red_normal : forall f,
  shift_free f ->
  entails (rs f) f.
Proof.
  introv Hsf.
  unfold entails. intros.
  inverts H as H; destr H.
  { (* this case cannot be as f is shift-free *)
    apply Hsf in H.
    false. }
  { assumption. }
Qed.

Lemma red_skip : forall f1 f2,
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

Lemma red_skip_conv : forall f1 f2,
    shift_free f1 ->
    entails (f1;; rs f2) (rs (f1;; f2)).
Proof.
  introv Hsf. unfold entails. intros.

  inverts H as H. 2: { apply Hsf in H. false. }
  inverts H7 as H7.

  { eapply s_rs_sh.
    apply* s_seq.
    eassumption. }
  { apply s_rs_val.
    apply* s_seq. }
Qed.

Lemma red_skip2 : forall f1 f2,
    shift_free f1 ->
    bientails (rs (f1;; f2)) (f1;; rs f2).
Proof.
  introv Hsf.
  unfold bientails. iff H.
  { apply* red_skip. }

  inverts H as H. 2: { apply Hsf in H. false. }
  inverts H7 as H7.

  { eapply s_rs_sh.
    apply* s_seq.
    eassumption. }
  { apply s_rs_val.
    apply* s_seq. }
Qed.

(* Lemma red_init : forall x b r,
  entails (sh x b r)
    (shs x b r (fun r2 => rs (ens (fun r1 => \[r1 = r])) r2)).
Proof.
  unfold entails. intros.
  inverts H as H.
  (* note that the application of this rule is very sensitive
    to the precise terms appearing in the equality... *)
    (* Unset Printing Notations. Set Printing Coercions. Set Printing Parentheses. *)
  intro_shs. intros. shiftfree.
  apply s_shc.
Qed. *)

(* Lemma red_extend : forall f2 x b fk v,
  shift_free f2 ->
  entails (shs x b v (fun r2 => rs fk r2);; f2)
    (shs x b v (fun r2 => rs (fk;; f2) r2)).
Proof.
  unfold entails. introv Hsf. introv H.
  inverts H as H.
  { destr H. elim_shs H. vacuous. }
  { elim_shs H.
    intro_shs. intros r2. specializes H0 r2. apply~ sf_rs.
    inverts H7 as H7.
    cont_eq.
    apply s_shc. }
Qed. *)

(* Lemma red_acc : forall f2 x v r fk fb,
  entails (rs (shs x fb v (fun r2 => rs fk r2);; f2) r)
    (rs (shs x fb v (fun r2 => rs (fk;; f2) r2)) r).
Proof.
  intros.
  unfold entails. intros.
  (* invert the rs *)
  inverts H as H.
  2: {
    (* the body of the reset doesn't produce a value *)
    (* s_rs_val case *)
    inverts H as H. destr H.
    (* TODO extend vacuous to elim shs *)
    elim_shs H. vacuous. }
  {
    (* the body produces a shift *)
    (* s_rs_sh case *)
    (* invert the seq *)
    inverts H as H. { destr H. elim_shs H. vacuous. }
    cont_eq.
    elim_shs H.
    (* we know that the shs is what produces a shift *)
    (* f2 goes in the continuation and under a reset *)
    (* now start reasoning backwards *)
    inverts H8 as H8.
    cont_eq.
    eapply s_rs_sh.
    intro_shs. apply sf_rs.
    apply s_shc.
    assumption.
  }
Qed. *)

(* Lemma red_shift_elim : forall x v r fk fb,
  entails (rs (shs x fb v (fun r2 => rs fk r2)) r)
    (defun x (fun a r =>
      rs (ens_ \[v = a];; fk) r);; rs fb r).
Proof.
  unfold entails. intros.
  inverts H as H. 2: { inverts H as H. destr H. vacuous. }
  elim_shs H. clear H0.
  inverts H8 as H8.
  cont_eq.
  eapply s_seq.
  apply s_defun.
  (* assumption. *)
  reflexivity.
  applys_eq H7.
Qed. *)

(* try to prove the continuation is shift-free *)
(* Lemma red_shift_elim1 : forall x v r fk fb a1 r1,
  entails (rs (shs x fb v (fun r2 => rs fk r2)) r)
    (defun x (fun a r =>
      rs (ens_ \[v = a];; fk) r);; ens_ \[shift_free (unk x a1 r1)];; rs fb r).
Proof.
  unfold entails. intros.
  inverts H as H. 2: { inverts H as H. destr H. vacuous. }
  elim_shs H. clear H0.
  inverts H8 as H8.
  cont_eq.
  eapply s_seq.
  apply s_defun.
  (* assumption. *)
  reflexivity.
  applys_eq H7.
  (* eapply s_seq. *)
Abort. *)