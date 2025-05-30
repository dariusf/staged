
From ShiftReset Require Import Basics Norm ShiftFree.

(* sadly this has to be proven from scratch *)
Lemma gent_seq_defun_idem : forall n s x uf f1 f2,
  Fmap.indom s x ->
  Fmap.read s x = uf ->
  gentails_under s n f1 f2 ->
  gentails_under s n (defun x uf;; f1) f2.
Proof.
  intros.
  inverts H1.
  { apply geu_base. intros.
    inverts H1.
    inverts H10.
    lets: update_idem H H0.
    rewrite H1 in H11.
    jauto. }
  { apply geu_shift. intros.
    inverts H1. 2: { no_shift. }
    inverts H10.
    rewrites (>> update_idem H H0) in H11.
    specializes H2 H11.
    assumption. }
Qed.

Lemma gent_seq_ens_pure_l : forall n s1 f f1 (P:val->Prop),
  (forall r, P r -> gentails_under s1 n f1 f) ->
  gentails_under s1 n (ens (fun r => \[P r]);; f1) f.
Proof.
Abort.

Lemma gent_seq_ens_void_pure_l : forall n s1 f f1 P,
  (P -> gentails_under s1 n f1 f) ->
  gentails_under s1 n (ens_ \[P];; f1) f.
Proof.
Abort.

Definition precise (H:hprop) :=
  forall h1 h2, H h1 -> H h2 -> h1 = h2.

Lemma gent_req_req : forall n f1 f2 H1 H2 env,
  precise H1 ->
  req_provable H1 ->
  H2 ==> H1 ->
  gentails_under env n f1 f2 ->
  gentails_under env n (req H1 f1) (req H2 f2).
Proof.
  intros n. induction n; introv Hprecise Hreq He H.
  { applys geu_base. introv Hf1.
    applys s_req. intros * HH2 **.
    apply He in HH2.
    inverts Hf1 as Hf1. specializes* Hf1.
    inverts* H. }
  { applys geu_shift. intros.
    specializes Hreq h1. destr Hreq. inverts H0. specializes* H13.
    inverts H. specializes H7 H13.
    zap.
    applys s_req. intros.
    apply He in H5.
    specializes Hprecise H3 H5.
    subst. lets*: Fmap.union_eq_inv_of_disjoint H8. subst*. }
Qed.

Lemma gent_all_r : forall n f A (fctx:A -> flow) env,
  (forall b, gentails_under env n f (fctx b)) ->
  gentails_under env n f (∀ b, fctx b).
Proof.
Abort.

Lemma gent_all_r1 : forall n f A (fctx:A -> flow) s1,
  (forall b, gentails_under s1 n f (fctx b)) ->
  gentails_under s1 n f (∀ b, fctx b).
Proof.
Abort.

Lemma gent_all_l : forall n f A (fctx:A -> flow) s1,
  (exists b, gentails_under s1 n (fctx b) f) ->
  gentails_under s1 n (∀ b, fctx b) f.
Proof.
Abort.

Lemma gent_ex_l : forall n f A (fctx:A -> flow) s1,
  (forall b, gentails_under s1 n (fctx b) f) ->
  gentails_under s1 n (fex (fun b => fctx b)) f.
Proof.
Abort.

Lemma gent_ex_r : forall n f A (fctx:A -> flow) s1,
  (exists b, gentails_under s1 n f (fctx b)) ->
  gentails_under s1 n f (fex (fun b => fctx b)).
Proof.
Abort.

Lemma gent_seq_all_l : forall n f f1 A (fctx:A -> flow) s1,
  (exists b, gentails_under s1 n (fctx b;; f1) f) ->
  gentails_under s1 n ((∀ b, fctx b);; f1) f.
Proof.
Abort.

Lemma gent_seq_ex_l : forall n f f1 A (fctx:A -> flow) s1,
  (forall b, shift_free (fctx b)) ->
  (forall b, gentails_under s1 n (fctx b;; f1) f) ->
  gentails_under s1 n ((∃ b, fctx b);; f1) f.
Proof.
Abort.

Lemma gent_seq_ex_r : forall n f f1 A (fctx:A -> flow) s1,
  (forall b, shift_free (fctx b)) ->
  (exists b, gentails_under s1 n f (fctx b;; f1)) ->
  gentails_under s1 n f ((∃ b, fctx b);; f1).
Proof.
Abort.

Lemma gent_req_l : forall n f f1 P env,
  P ->
  gentails_under env n f1 f ->
  gentails_under env n (req \[P] f1) f.
Proof.
Abort.

Lemma gent_req_r : forall n f f1 H env,
  gentails_under env n (ens_ H;; f) f1 ->
  gentails_under env n f (req H f1).
Proof.
Abort.

Lemma gent_ens_void_l : forall n env f P,
  (P -> gentails_under env n empty f) ->
  gentails_under env n (ens_ \[P]) f.
Proof.
Abort.

Lemma gent_ens_single_pure : forall n env P P1,
  (P1 -> P) ->
  gentails_under env n (ens_ \[P1]) (ens_ \[P]).
Proof.
Abort.

Lemma gent_ens_void_single : forall n env H H1,
  (H1 ==> H) ->
  gentails_under env n (ens_ H1) (ens_ H).
Proof.
Abort.

Lemma gent_ens_single : forall n env Q Q1,
  (Q1 ===> Q) ->
  gentails_under env n (ens Q1) (ens Q).
Proof.
Abort.

Lemma gent_seq_disj_l : forall n s f1 f2 f3,
  gentails_under s n f1 f3 ->
  gentails_under s n f2 f3 ->
  gentails_under s n (disj f1 f2) f3.
Proof.
Abort.

Lemma gent_seq_disj_r_l : forall n s f1 f2 f3 f4,
  gentails_under s n f3 (f1;; f4) ->
  gentails_under s n f3 (disj f1 f2;; f4).
Proof.
Abort.

Lemma gent_seq_disj_r_r : forall n s f1 f2 f3 f4,
  gentails_under s n f3 (f2;; f4) ->
  gentails_under s n f3 (disj f1 f2;; f4).
Proof.
Abort.

Lemma gent_disj_r_l : forall n s f1 f2 f3,
  gentails_under s n f3 f1 ->
  gentails_under s n f3 (disj f1 f2).
Proof.
  intros.
  inverts H.
  { applys geu_base. intros.
    applys* s_disj_l. }
  { applys geu_shift. intros.
    specializes H0 H.
    zap. applys* s_disj_l. }
Qed.

Lemma gent_disj_r_r : forall n s f1 f2 f3,
  gentails_under s n f3 f2 ->
  gentails_under s n f3 (disj f1 f2).
Proof.
Abort.

Lemma gent_disj_l : forall n f1 f2 f3 env,
  gentails_under env n f1 f3 ->
  gentails_under env n f2 f3 ->
  gentails_under env n (disj f1 f2) f3.
Proof.
Abort.
