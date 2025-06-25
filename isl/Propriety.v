
From Coq Require Import Classes.RelationClasses.
From Coq Require Morphisms Program.Basics.

From ISL Require Import Basics.

Local Open Scope string_scope.

Infix "====>" := Morphisms.respectful (at level 80, right associativity).
Notation Proper := Morphisms.Proper.
Notation respectful := Morphisms.respectful.
Notation impl := Program.Basics.impl.
Notation flip := Basics.flip.

(** Incantations for setoid rewriting *)
Section Propriety.

  (*
    We have to prove (at most) m*n instances,
    for the m things we want to rewrite with,
    and the n things we want to rewrite in:

    |     | ⊑ | ⊢ ⊑ | <-> | ⊑ n | ⊢ ⊑ n | req | seq | bind | rs | ... | (n) |
    |   ⊑ |   |     |     |     |       |     |     |      |    |     |     |
    | ⊢ ⊑ |   |     |     |     |       |     |     |      |    |     |     |
    | <-> |   |     |     |     |       |     |     |      |    |     |     |
    | ... |   |     |     |     |       |     |     |      |    |     |     |
    | (m) |   |     |     |     |       |     |     |      |    |     |     |

    The definitions here are grouped by column.
    The naming convention is Proper_[col]_[row].

  *)

  #[global]
  Instance Proper_entails_entails : Proper
    (flip entailed ====> entailed ====> impl)
    entailed.
  Proof.
    unfold entailed, Proper, respectful, impl. intros. auto.
  Qed.

  Example rewrite :
    entailed (ens_ \[1 = 1]) (ens_ \[2 = 2]) ->
    entailed (ens_ \[1 = 1]) empty.
  Proof.
    intros H.
    rewrite H.
  Abort.

  (** entailed is proper wrt satisfies *)
  #[global]
  Instance Proper_satisfies_entails : Proper
    (eq ====> eq ====> eq ====> eq ====> eq ====> entailed ====> flip impl)
    satisfies.
  Proof.
    unfold entailed, Proper, respectful, flip, impl.
    intros. subst.
    auto.
  Qed.

  #[global]
  Instance Proper_seq_entailed : Proper (entailed ====> entailed ====> entailed) seq.
  Proof.
    unfold Proper, entailed, respectful.
    intros.
    inverts H1 as H1; destr H1.
    { apply* s_bind. }
  Qed.

  #[global]
  Instance Proper_bind_entailed : Proper (entailed ====> Morphisms.pointwise_relation val entailed ====> entailed) bind.
  Proof.
    unfold Proper, entailed, respectful. intros.
    inverts H1.
    { subst. applys* s_bind. }
  Qed.

  Example rewrite :
    entailed (ens_ \[1 = 1]) (ens_ \[2 = 2]) ->
    entailed
      (bind (ens_ \[1 = 1]) (fun v => empty))
      empty.
  Proof.
    intros H.
    rewrite H.
  Abort.

  Example rewrite :
    entailed (ens_ \[1 = 1]) (ens_ \[2 = 2]) ->
    entailed
      (bind empty (fun v => ens_ \[1 = 1]))
      empty.
  Proof.
    intros H.
    (* setoid_rewrite H. *)
  Abort.

  #[global]
  Instance Proper_req_entails : Proper (eq ====> entailed ====> entailed) req.
  Proof.
    unfold Proper, entailed, respectful, flip.
    intros.
    constructor. intros.
    rewrite H in H2.
    inverts H1 as H5.
    specializes H5 H3 ___.
  Qed.

End Propriety.
