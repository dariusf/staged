From Staged Require Import Logic.

Check empty_env.
Check fall.
Check (fun x => req (x ~~> vint 1) (ens (fun v => \[v = vint 10]))).

Goal satisfies empty_env empty_heap empty_heap (norm (vint 1))
  (fall (fun x => req
                    (x ~~> vint 1)
                    (ens (fun v => \[v = vint 10])))).
Proof.
  apply s_fall.
  intro v.
  apply s_req.
  intros hp hr H_hp H_union H_disjoint.
  Search (_ \u _ = Fmap.empty -> _).
  symmetry in H_union.
  assert (hp_eq_empty := Fmap.union_eq_empty_inv_r H_union).
  rewrite hp_eq_empty in H_hp. (* (v ~~> vint 1) Fmap.empty *)
  assert (~ (v ~~> vint 1) Fmap.empty) by admit.
  contradiction.
Admitted.
