
From Staged Require Import Logic Automation.
Local Open Scope string_scope.

(** * Basic example *)
Definition hello : ufun := fun args res =>
  match args with
  | vtup (vstr f) (vtup (vloc x) (vloc y)) =>
    ∀ a, req (x~~>vint a) (ens_ (x~~>vint (a+1));;
    ∃ r, unk f (vloc y) (vint r);;
    ∀ b b1, req (x~~>vint b \* y~~>vint b1)
      (ens_ (x~~>vint b \* y~~>res \* \[res = vint (b+r)])))
  | _ => empty
  end.

Definition hello_env (x y:loc) :=
  Fmap.update
    (Fmap.single "f"
      (fun y r => ∀ b,
        req (x~~>vint b)
          (ens_ ((x~~>vint (b+1) \* \[r = vint 0])))))
      "hello" hello.

(* [f] is allowed to capture [x] *)
Lemma hello_capture : forall x y res,
  (* x <> y is implied by the precondition *)
  entails_under (hello_env x y)
    (unk "hello" (vtup (vstr "f") (vtup (vloc x) (vloc y))) res)
    (∀ a b, req (x~~>vint a \* y~~>vint b)
      (ens_ (x~~>vint (a+2) \* y~~>res \* \[res = vint (a+2)]))).
Proof.
  intros x y res.
  funfold1 "hello".
  simpl.
  fintro a.
  fintro b.
  finst a.
  fassume.

  rewrite (norm_ens_req_transpose).
  2: { 
    rewrite <- (hstar_hempty_r (x~~>vint a)) at 2.
    apply b_pts_match.
    apply b_base_empty.
  }

  (* norm. *)
  (* prove trivial reqs *)
  rewrite hstar_hempty_r.
  apply ent_req_l. reflexivity.

  (* combine everything into the SL context *)
  rewrite norm_seq_assoc.
  rewrite norm_ens_ens_void_combine.

  (* rewrite under the existential *)
  rewrites (>> ent_ex_seq_unk (hello_env x y)).
  { unfold hello_env. resolve_fn_in_env. }
  simpl.

  (* intro the existential, and specialize the forall *)
  fintro v.
  rewrite norm_seq_forall_distr_r.
  finst (a + 1).
  rewrite norm_reassoc.

  rewrite (norm_ens_req_transpose).
  2: { 
    rewrite hstar_comm.
    rewrite <- (hstar_hempty_r (x~~>vint (a + 1))) at 2.
    apply b_pts_match.
    apply b_base_empty.
  }

  (* norm *)
  rewrite hstar_hempty_r. apply ent_req_l. reflexivity.

  (* move the pure assumption up... *)
  rewrite norm_ens_ens_void_split.
  rewrite norm_seq_assoc.
  rewrite norm_seq_assoc.
  rewrite norm_ens_ens_void_combine.
  rewrite norm_ens_ens_pure_comm.
  rewrite <- norm_seq_assoc.
  fassume H.

  (* instantiate before biabduction *)
  finst (a + 2).
  finst b.

  rewrite norm_ens_req_transpose.
  2: {
    rewrite hstar_comm.
    apply b_pts_match.
    apply b_pts_single.
  }

  (* dispatch trivial req again *)
  rewrite hstar_hpure_conj.
  apply ent_req_l.
  { split. f_equal. math. reflexivity. }
  rewrite norm_seq_ens_empty.

  (* close *)
  apply ent_ens_single.
  injects H.
  xsimpl.
  intros. rewrite H. f_equal. math.
Qed.

(** * Preventing the use of an [f] that captures [x] *)
(* Suppose we have a hello that does not release x,
    and it is called with an f that captures x *)
Definition hello1 : ufun := fun args res =>
  match args with
  | vtup (vstr f) (vtup (vloc x) (vloc y)) =>
    ∀ a, req (x~~>vint a)
    (∃ r, unk f (vloc y) (vint r);;
    ∀ b1, req (y~~>vint b1)
      (ens_ (x~~>vint (a+1) \* y~~>res \* \[res = vint (a+1+r)])))
  | _ => empty
  end.

(* same as before except for using hello1 *)
Definition hello_env1 (x y:loc) :=
  Fmap.update
    (Fmap.single "f"
      (fun y r => ∀ b,
        req (x~~>vint b)
          (ens_ ((x~~>vint (b+1) \* \[r = vint 0])))))
      "hello" hello1.

(* the proof should not go through *)
Lemma hello_capture1 : forall x y res,
  entails_under (hello_env1 x y)
    (unk "hello" (vtup (vstr "f") (vtup (vloc x) (vloc y))) res)
    (∀ a b, req (x~~>vint a \* y~~>vint b)
      (ens_ \[True])).
Proof.
  intros.
  fintro a.
  fintro b.
  fassume.
  funfold1 "hello". simpl.
  finst a.

  rewrite norm_ens_req_transpose.
  2: {
    (* rewrite hstar_comm. *)
    rewrite <- (hstar_hempty_r (x ~~> vint a)) at 2.
    apply b_pts_match.
    apply b_base_empty.
  }

  (* norm *)
  rewrite hstar_hempty_r.
  apply ent_req_l. reflexivity.

  rewrites (>> ent_ex_seq_unk (hello_env1 x y) "f").
  { unfold hello_env1. resolve_fn_in_env. }
  simpl.
  fintro v.
  (* f cannot capture x *)
Abort.