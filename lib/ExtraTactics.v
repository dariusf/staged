
Tactic Notation "ok" := intuition auto; try easy.

Ltac inv H := inversion H; clear H; subst.

Ltac destr H :=
  match type of H with
  | ex (fun x => _) =>
    let L := fresh x in
    let R := fresh in
    destruct H as [L R]; destr R
  | _ /\ _ =>
    let L := fresh in
    let R := fresh in
    destruct H as [L R]; destr L; destr R
  | _ => idtac
  end.

(* https://github.com/mattam82/Coq-Equations/blob/main/theories/Init.v#L148 *)
Ltac forward_gen H tac :=
  match type of H with
  | forall (_ : ?X), _ => let H' := fresh in assert (H':X) ; [tac|specialize (H H'); clear H']
  end.

Tactic Notation "forward" constr(H) := forward_gen H ltac:(idtac).
Tactic Notation "forward" constr(H) "by" tactic(tac) := forward_gen H tac.

Ltac exs :=
  lazymatch goal with
  | |- ex _ => eexists; exs
  | _ => idtac
  end.

(* Extensible notion of vacuity *)
Ltac vacuity := false.

(* Ltac vacuous H := solve [inversion H]. *)
Tactic Notation "vacuous" :=
  vacuity;
  match goal with
  | H: _ |- _ => solve [inversion H]
  | _ => fail
  end.
