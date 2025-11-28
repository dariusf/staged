
From Stdlib Require Import Utf8 Classes.Morphisms Program.

Module Type StagedLogic.

  (* Binding *)
  Parameter inc : Set → Set.
  Parameter empty : Set.
  Notation "∅" := empty.
  Parameter v : ∀ {V}, nat → V.
  Notation "& n" := (v n) (at level 5).

  (* Expressions *)
  Parameter expr : Set → Set.
  Parameter app : ∀ {V:Set}, expr V → expr V → expr V.
  Parameter var : ∀ {V:Set}, V → expr V.
  Parameter lambda : ∀ {V:Set}, expr (inc V) → expr V.

  (* Equivalence *)
  Parameter eqv : ∀ {V}, expr V → expr V → Prop.
  Parameter Reflexive_eqv : ∀ {V:Set}, Reflexive (@eqv V).
  Parameter Symmetric_eqv : ∀ {V:Set}, Symmetric (@eqv V).
  Parameter Transitive_eqv : ∀ {V:Set}, Transitive (@eqv V).

  (* Entailment *)
  Parameter entails : ∀ {V}, expr V → expr V → Prop.
  Parameter Reflexive_entails : ∀ {V:Set}, Reflexive (@entails V).
  Parameter Transitive_entails : ∀ {V:Set}, Transitive (@entails V).

  (* Proper instances *)
  Parameter Proper_iff_eqv : ∀ {V:Set}, Proper (@eqv V ==> @eqv V ==> iff) eqv.
  Parameter Proper_eqv_app : ∀ {V:Set}, Proper (@eqv V ==> @eqv V ==> @eqv V) app.
  Parameter Proper_eqv_lambda : ∀ {V:Set}, Proper (@eqv (inc V) ==> @eqv V) lambda.

  Parameter Proper_impl_entails : ∀ {V:Set},
    Proper (flip (@entails V) ==> @entails V ==> impl) entails.
  Parameter Proper_entails_app : ∀ {V:Set},
    Proper (@entails V ==> @entails V ==> @entails V) app.
  Parameter Proper_entails_lambda : ∀ {V:Set},
    Proper (@entails (inc V) ==> @entails V) lambda.

  (* Substitution *)
  Parameter subst : ∀ {V}, expr (inc V) → expr V → expr V.
  (* TODO equations *)
  Parameter subst_app : ∀ {V} (e1 e2:expr (inc V)) (v:expr V),
    subst (app e1 e2) v = app (subst e1 v) (subst e2 v).

  (* Parameter subst_lambda : ∀ {V V1} (e: expr (inc (inc V))) (v:expr (inc V)),
    subst (lambda e) v = lambda (subst e v). *)

  (* Lemmas *)
  Parameter red_beta : ∀ {V} (e:expr (inc V)) (v:expr V),
    eqv (app (lambda e) v) (subst e v).

End StagedLogic.

Module WithInstances (SL: StagedLogic).

  Import SL.

  #[global]
  Instance Reflexive_eqv {V:Set} : Reflexive (@eqv V) := Reflexive_eqv.

  #[global]
  Instance Proper_eqv_app {V:Set} : Proper (@eqv V ==> @eqv V ==> @eqv V) app :=
    Proper_eqv_app.

  #[global]
  Instance Proper_iff_eqv {V:Set} : Proper (@eqv V ==> @eqv V ==> iff) eqv :=
    Proper_iff_eqv.

  #[global]
  Instance Proper_eqv_lambda {V:Set} : Proper (@eqv (inc V) ==> @eqv V) lambda :=
    SL.Proper_eqv_lambda.

  Export SL.

End WithInstances.

Module CaseStudy (SL : StagedLogic).

  Module M := WithInstances(SL).
  Import M.

  Parameter red_hello : ∀ {V} (e1 e2:expr V), eqv e1 e2.

  Example e1 (e1 e2:expr ∅):
    eqv (app e2 e1) (app e1 e2).
  Proof.
    rewrite (red_hello e1 e2).
    reflexivity.
  Qed.

  Definition id_exp : expr ∅ := lambda (var &0).

  Example e2 (e1 e2:expr ∅):
    eqv (app (app id_exp e1) e2) (app (e1) e2).
  Proof.
    unfold id_exp.
    (* rewrite (red_beta (ret (var &0)) v1). *)
    rewrite red_beta.
    (* need equations for subst *)
  Abort.

End CaseStudy.

(* Module StagedLogicIxFree : StagedLogic.
End StagedLogicIxFree. *)

(* Module M := CaseStudy(StagedLogicIxFree).
Check M. *)
