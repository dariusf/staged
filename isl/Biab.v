
From ISL Require Import Basics Norm Satisfies Propriety.

Implicit Types H : hprop.

(** * Biabduction *)

Inductive biab : hprop -> hprop -> hprop -> hprop -> Prop :=

  | b_trivial : forall H,
    biab \[] H H \[]

  | b_base_empty : forall Hf,
    biab \[] Hf \[] Hf

  | b_pts_match : forall a b H1 H2 Ha Hf l,
    biab Ha H1 H2 Hf ->
    biab (\[a=b] \* Ha) (l~~>a \* H1) (l~~>b \* H2) Hf

  | b_any_match : forall H H1 H2 Ha Hf,
    biab Ha H1 H2 Hf ->
    biab Ha (H \* H1) (H \* H2) Hf

  | b_pts_diff : forall a b H1 H2 Ha Hf l1 l2,
    biab Ha H1 H2 Hf ->
    biab (l2~~>b \* Ha) (l1~~>a \* H1) (l2~~>b \* H2) (l1~~>a \* Hf).

Lemma b_pts_single : forall l a b,
  biab \[a=b] (l~~>a) (l~~>b) \[].
Proof.
  intros.
  rewrite <- (hstar_hempty_r (l~~>a)).
  rewrite <- (hstar_hempty_r (l~~>b)).
  applys_eq b_pts_match.
  instantiate (1 := \[]).
  xsimpl.
  intuition.
  intuition.
  apply b_base_empty.
Qed.

Lemma ens_reduce_frame : forall s1 s2 h1 h hf R H,
  H h ->
  Fmap.disjoint h (hf \u h1) ->
  satisfies s1 s2 (hf \u h1) (hf \u h1 \u h) R (ens_ H) ->
  satisfies s1 s2 h1 (h1 \u h) R (ens_ H).
Proof.
  introv H0 Hd. intros.
  inverts H1 as H1. destr H1.
  rewrite hstar_hpure_l in H1. destr H1.

  constructor. exists v. exists h3.
  intuition.
  rewrite hstar_hpure_l. intuition.
  fmap_eq.

  forwards: Fmap.union_eq_inv_of_disjoint (hf \u h1) h h3.
  fmap_disjoint.
  fmap_disjoint.
  { asserts_rewrite (h \u hf \u h1 = hf \u h1 \u h). fmap_eq.
    asserts_rewrite (h3 \u hf \u h1 = (hf \u h1) \u h3). fmap_eq.
    assumption. }

  assumption.
Qed.

(* Lemma transpose_pts_diff : forall Ha H1 H2 Hf f (x y:loc) (a b:val),
  entailed (ens_ H1;; req H2 f) (req Ha (ens_ Hf;; f)) ->
  entailed
    (ens_ (x ~~> a \* H1);; req (y ~~> b \* H2) f)
    (req (y ~~> b \* Ha) (ens_ (x ~~> a \* Hf);; f)).
Proof.
  (* the idea of this proof is to demonstrate that we can commute adding x~~>a and removing y~~>b, by showing that: we can start from a heap without x~~>a (using the lemma ens_reduce_frame), perform the operations, and arrive at the same result. *)

  unfold entailed. intros.
  inverts H0 as H0.

  (* extract everything we can first. start with x->a *)
  rewrite norm_ens_ens_void in H0.
  inverts H0 as H0.
  inverts H0 as H0. destr H0.
  hinv H0. hinv H0.

  (* and y->b and Ha *)
  rewrite norm_req_req.
  apply s_req. intros.
  apply s_req. intros.

  (* now, start supplying stuff. x->a is easy *)
  rewrite norm_ens_ens_void.
  rewrite <- norm_seq_assoc_sf; shiftfree.
  applys s_seq (hr0 \u x1) vunit.
  apply s_ens. exists vunit x1. splits*. hintro. jauto.

  (* supply y->b. to do this, we need to find h3-h(y->b).
    h3 = h(H1) + h0
       = h(H1) + h(x->a) + h1
       = h(H1) + h(x->a) + hr + h(y->b)

    h3 - h(y->b) = h(H1) + h(x->a) + hr
  *)
  pose proof H11.

  inverts H11 as H11. destr H11. hinv H11. hinv H11. (* find out h(H1) *)
  rewrite norm_req_req in H10.
  inverts H10 as H32. specializes H32 hp (x1 \u hr \u x3) H12.
  forward H32 by fmap_eq. forward H32 by fmap_disjoint.

  (* now we are trying to supply the premise of H. to do this
    we need to remove h(y->2) from both sides of H10. *)
  (* subst. rew_fmap *. *)
  subst h0 h3 h1 h5. lets: ens_reduce_frame (hr \u h4) x3 hp H21.
  forward H4 by fmap_disjoint.
  specializes H4. applys_eq H18. fmap_eq. fmap_eq.
  clear H18.

  (* finally, we can use H. build a seq to do that *)
  lets H13: s_seq H4. specializes H13. applys_eq H32. fmap_eq. clear H4 H32.

  specializes H H13. clear H13.

  (* Ha is in the way, but otherwise we are done *)
  subst. rew_fmap *.
  inverts H as H13.
  specializes H13 hp0 H15.
Qed.

Lemma biab_single_h : forall H s1 s2 h1 h2 R H1 H2 f,
  satisfies s1 s2 h1 h2 R (ens_ H1;; req H2 f) ->
  satisfies s1 s2 h1 h2 R (ens_ (H \* H1);; req (H \* H2) f).
Proof.
  intros.
  inverts H0 as H0. destr H0.
  (* ens adds a location to the heap *)
  inverts H0 as H0.
  (* use that to figure out what is in h3 *)
  destr H0. hinv H0. hinv H0. hinv H5. subst h0 h3 x0 x. rew_fmap *.

  (* prove just the first part *)
  rewrite norm_req_req in H10.
  inverts H10 as H10. specializes H10 x1 (h1 \u x2) ___.

  applys s_seq (h1 \u x2) vunit.
  { constructor. exists vunit. exists x2.
    splits*. hintro; jauto. }
  { assumption. }
Qed.

(** Biabduction for a single location. *)
Lemma biab_single : forall (x:loc) (a:val) s1 s2 h1 h2 R H1 H2 f,
  satisfies s1 s2 h1 h2 R (ens_ (x~~>a \* H1);; req (x~~>a \* H2) f)->
  satisfies s1 s2 h1 h2 R (ens_ H1;; req H2 f).
Proof.
  intros.
  applys* biab_single_h (x~~>a).
Qed.

(* This is proved elsewhere *)
Lemma norm_ens_req_transpose : forall H1 H2 Ha Hf f,
  biab Ha H1 H2 Hf ->
  entailed (ens_ H1;; req H2 f)
    (req Ha (ens_ Hf;; f)).
Proof.
  unfold entailed.
  introv Hbi.
  induction Hbi.

  { (* trivial *)
    introv H2.
    apply ens_req_inv in H2.
    rewrite norm_seq_req_emp.
    rewrite norm_seq_ens_empty.
    assumption. }

  { (* base case *)
    fold entailed.
    introv H2.
    rewrite norm_seq_req_emp.
    pose proof entails_ens_seq. specializes H Hf Hf H2.
    rewrite norm_seq_req_emp.
    apply entails_refl. }

  { (* b_pts_match *)
    intros.

    (* use the req *)
    rewrite norm_req_req.
    constructor. intros. hinv H0. subst. rew_fmap.

    apply (IHHbi s1 s2).
    applys biab_single H. }

  { (* b_any_match *)
    intros.
    apply IHHbi.
    applys* biab_single_h H. }

  { (* b_pts_diff *)
    introv H3.
    pose proof transpose_pts_diff.
    unfold entailed in H.
    specializes H IHHbi H3. }
Qed. *)
