
From Stdlib Require Import Utf8.
From Binding Require Import Lib Auto.
Require Import Binding.Set.

From Stdlib Require Import Classes.Morphisms Program.

Module Type StagedLogic.

  Parameter expr : Set → Set.
  Parameter val : Set → Set.

  Parameter ret : ∀ {V:Set}, val V → expr V.
  Parameter app : ∀ {V:Set}, expr V → expr V → expr V.
  Parameter var : ∀ {V:Set}, V → val V.
  Parameter lambda : ∀ {V:Set}, expr (inc V) → val V.

  Parameter emap : ∀ {A B:Set}, (A [→] B) → expr A → expr B.
  Parameter vmap : ∀ {A B:Set}, (A [→] B) → val A → val B.

  (* equivalence *)
  Parameter eqv : ∀ {V}, expr V → expr V → Prop.
  Parameter Reflexive_eqv : ∀ {V:Set}, Reflexive (@eqv V).
  Parameter Symmetric_eqv : ∀ {V:Set}, Symmetric (@eqv V).
  Parameter Transitive_eqv : ∀ {V:Set}, Transitive (@eqv V).

  (* entailment *)
  Parameter entails : ∀ {V}, expr V → expr V → Prop.
  Parameter Reflexive_entails : ∀ {V:Set}, Reflexive (@entails V).
  Parameter Transitive_entails : ∀ {V:Set}, Transitive (@entails V).

(* TODO just have one expr type? *)

  (* equivalence for values *)
  Parameter eqv_val : ∀ {V}, val V → val V → Prop.
  Parameter Reflexive_eqv_val : ∀ {V:Set}, Reflexive (@eqv_val V).
  Parameter Symmetric_eqv_val : ∀ {V:Set}, Symmetric (@eqv_val V).
  Parameter Transitive_eqv_val : ∀ {V:Set}, Transitive (@eqv_val V).

  Parameter Proper_eqv_app : ∀ {V:Set}, Proper (@eqv V ==> @eqv V ==> @eqv V) app.
  Parameter Proper_iff_eqv : ∀ {V:Set}, Proper (@eqv V ==> @eqv V ==> iff) eqv.
  Parameter Proper_eqv_lambda : ∀ {V:Set}, Proper (@eqv (inc V) ==> @eqv_val V) lambda.

  Parameter Proper_impl_entails : ∀ {V:Set},
    Proper (flip (@entails V) ==> @entails V ==> impl) entails.
  Parameter Proper_entails_app : ∀ {V:Set},
    Proper (@entails V ==> @entails V ==> @entails V) app.

  Section Bind.

  Context `{SetPureCore val}.

  Parameter ebind : ∀ {A B:Set}, (A [⇒] B) → expr A → expr B.
  Parameter vbind : ∀ {A B:Set}, (A [⇒] B) → val A → val B.

  Context `{BindCore Set (@Sub val _) expr}.

  Parameter red_beta : ∀ {V} (e:expr (inc V)) (v:val V),
    eqv
      (app (ret (lambda e)) (ret v))
      (subst e v).

  End Bind.

End StagedLogic.

Module MakeInstances (SL: StagedLogic).

  Import SL.

  #[global]
  Instance SetPureCore_value : SetPureCore val :=
    { set_pure := @var }.

  #[global]
  Instance FunctorCore_emap : FunctorCore expr := @emap.

  #[global]
  Instance FunctorCore_vmap : FunctorCore val := @vmap.

  #[global]
  Instance BindCore_ebind : BindCore expr := @ebind SetPureCore_value.

  #[global]
  Instance BindCore_vbind : BindCore val := @vbind SetPureCore_value.

  #[global]
  Instance Reflexive_eqv : ∀ {V:Set}, Reflexive (@eqv V).
  Proof.
    intros.
    eapply Reflexive_eqv.
  Qed.

  #[global]
  Instance Proper_eqv_app : ∀ {V:Set}, Proper (@eqv V ==> @eqv V ==> @eqv V) app.
  Proof.
    intros.
    eapply Proper_eqv_app.
  Qed.

  #[global]
  Instance Proper_iff_eqv : ∀ {V:Set}, Proper (@eqv V ==> @eqv V ==> iff) eqv.
  Proof.
    intros.
    eapply Proper_iff_eqv.
  Qed.

  #[global]
  Instance Proper_eqv_lambda : ∀ {V:Set}, Proper (@eqv (inc V) ==> @eqv_val V) lambda.
  Proof.
    intros.
    eapply Proper_eqv_lambda.
  Qed.

  Export SL.

End MakeInstances.

Module CaseStudy (SL : StagedLogic).

  Module M := MakeInstances(SL).
  Import M.

  Parameter red_hello : ∀ {V} (e1 e2:expr V), eqv e1 e2.

  Example e1 (e1 e2:expr ∅):
    eqv (app e2 e1) (app e1 e2).
  Proof.
    rewrite (red_hello e1 e2).
    reflexivity.
  Qed.

  Definition id_exp : expr ∅ := ret (lambda (ret (var &0))).

  Example e2 (v1:val ∅) (e2:expr ∅):
    eqv (app (app id_exp (ret v1)) e2) (app (ret v1) e2).
  Proof.
    unfold id_exp.
    (* rewrite (red_beta (ret (var &0)) v1). *)
    rewrite red_beta.
    simpl.
    (* cannot perform this subst without a definition for bind *)
  Abort.

End CaseStudy.

(* Module StagedLogicIxFree : StagedLogic.
End StagedLogicIxFree. *)

(* Module M := CaseStudy(StagedLogicIxFree).
Check M. *)
