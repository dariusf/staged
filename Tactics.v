(* some old tactics *)

Tactic Notation "inj" constr(h) := injection h as h; subst.
Tactic Notation "ok" := intuition auto; try easy.

(* these could be made less powerful in future, so they can't be used wrongly *)
Tactic Notation "vacuous" := easy.
(* Tactic Notation "ih" := ok. *)

Tactic Notation "case_on" constr(e) := let H := fresh in destruct e eqn:H; ok.
Tactic Notation "case_on" constr(e) ident(x) := destruct e eqn:x; ok.
(* Tactic Notation "gen" ident_list(x) := generalize dependent x. *)

(* new ones *)

Ltac inv H := inversion H; clear H; subst.
(* Tactic Notation "inv" constr(h) := inversion h; subst. *)
(* Ltac invp H P := inversion H as P; clear H; subst. *)
Tactic Notation "invp" constr(h) simple_intropattern(p) := inversion h as p; subst; clear h.

(* Ltac rw := rewrite. *)
(* Ltac con := constructor. *)

(* https://github.com/tchajed/coq-tricks/blob/master/src/Deex.v *)
(* Ltac deex :=
  repeat match goal with
         | [ H: exists (name:_), _ |- _ ] =>
           let name' := fresh name in
           destruct H as [name' H]
         end. *)

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

Ltac destr_all :=
  match goal with
  | H : _ /\ _ |- _ => destr H; destr_all
  | H : ex _ |- _ => destr H; destr_all
  | _ => idtac
  end.

(* https://github.com/mattam82/Coq-Equations/blob/main/theories/Init.v#L148 *)
Ltac forward_gen H tac :=
  match type of H with
  | forall (_ : ?X), _ => let H' := fresh in assert (H':X) ; [tac|specialize (H H'); clear H']
  end.

Tactic Notation "forward" constr(H) := forward_gen H ltac:(idtac).
Tactic Notation "forward" constr(H) "by" tactic(tac) := forward_gen H tac.

(* https://softwarefoundations.cis.upenn.edu/plf-current/LibTactics.html *)
Ltac get_head E :=
  match E with
  | ?E' ?x => get_head E'
  | _ => constr:(E)
  end.

Ltac apply_to_head_of E cont :=
  let go E :=
    let P := get_head E in cont P in
  match E with
  | forall _,_ => intros; apply_to_head_of E cont
  | ?A = ?B => first [ go A | go B ]
  | ?A => go A
  end.
Ltac unfolds_base :=
  match goal with |- ?G =>
   apply_to_head_of G ltac:(fun P => unfold P) end.

(* Tactic Notation "unfolds" :=
  unfolds_base. *)

(* TODO unfolds does not terminate when given an implication? *)

Ltac unfolds_in_base H :=
  match type of H with ?G =>
   apply_to_head_of G ltac:(fun P => unfold P in H) end.
(* Tactic Notation "unfolds" "in" hyp(H) :=
  unfolds_in_base H. *)
