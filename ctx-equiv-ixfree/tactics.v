
From Stdlib Require Import Utf8.

From Ltac2 Require Import Ltac2 Printf Option.
Import Constr.
Import Unsafe.

Ltac2 inspect_kind (c:constr) :=
  match Constr.Unsafe.kind c with
  | Rel _ => Message.print (Message.of_string "Rel")
  | Var _ => Message.print (Message.of_string "Var")
  | Meta _ => Message.print (Message.of_string "Meta")
  | Evar _ _ => Message.print (Message.of_string "Evar")
  | Sort _ => Message.print (Message.of_string "Sort")
  | Cast _ _ _ => Message.print (Message.of_string "Cast")
  | Prod _ _ => Message.print (Message.of_string "Prod")
  | Lambda _ _ => Message.print (Message.of_string "Lambda")
  | LetIn _ _ _ => Message.print (Message.of_string "LetIn")
  | App _ _ => Message.print (Message.of_string "App")
  | Constant _ _ => Message.print (Message.of_string "Constant")
  | Ind _ _ => Message.print (Message.of_string "Ind")
  | Constructor _ _ => Message.print (Message.of_string "Constructor")
  | Case _ _ _ _ _ => Message.print (Message.of_string "Case")
  | Fix _ _ _ _ => Message.print (Message.of_string "Fix")
  | CoFix _ _ _ => Message.print (Message.of_string "CoFix")
  | Proj _ _ _ => Message.print (Message.of_string "Proj")
  | Uint63 _ => Message.print (Message.of_string "Uint63")
  | Float _ => Message.print (Message.of_string "Float")
  | String _ => Message.print (Message.of_string "String")
  | Array _ _ _ _ => Message.print (Message.of_string "Array")
  end.

Ltac2 print_goals0 () :=
  Control.enter (fun () =>
  match! goal with
  [ |- ?t] => printf "the goal is %t" t
  end).

(* Ltac2 Eval (inspect_kind '(0)).
Ltac2 Eval (inspect_kind '(1)).
Ltac2 Eval (inspect_kind '(true)). *)

(* determine if an evar or a goal should be used to supply an argument of this type *)
Ltac2 should_use_evar (t:constr) :=
  (* inspect_kind t; *)
  match Constr.Unsafe.kind t with
  | App _ _ => false
  | Var i =>
    match Unsafe.kind (Constr.type (Control.hyp i)) with
    | Sort _ => false
    | _ => true
    end
  | _ => true
  end.

(* Ltac2 Eval (should_use_evar '(1)).
Ltac2 Eval (should_use_evar '(true)).
Ltac2 Eval (should_use_evar '(True)).
Ltac2 Eval (should_use_evar '(1 < 2)). *)

(* https://rocq-prover.zulipchat.com/#narrow/channel/278935-Ltac2/topic/a.20variant.20of.20.22specialize.22 *)
Ltac2 fresh_goal_of_constr type :=
  let t := '(_ :> $type) in
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Evar evar _ => Control.new_goal evar; t
  | _ => Control.zero Match_failure
  end.

Ltac2 rec specialise_many (h:ident) (hs:constr list) :=
  match hs with
  | [] =>
    (* Message.print (Message.of_string "done"); *)
    ()
  | h1 :: hs1 =>
    (* print_goals0 (); *)
    (* Message.print (Message.of_string "working on arg"); *)
    (* Message.print (Message.of_ident h); *)
    let p := Control.hyp h in
    let np := h1 in
    (* Message.print (Message.of_constr p);
    Message.print (Message.of_constr (Constr.type p));
    Message.print (Message.of_constr np);
    Message.print (Message.of_constr (Constr.type np)); *)

    Control.plus
      (fun () =>
        specialize ($p $np);
        (* Message.print (Message.of_string "managed to specialise"); *)
        specialise_many h hs1 (* only here do we advance *)
        )
      (fun _ =>
        (* Message.print (Message.of_string "placeholder case"); *)
        match! Constr.type p with
        | ?a -> _  =>
          (* Message.print (Message.of_string "type is"); *)
          (* Message.print (Message.of_constr a); *)
          match should_use_evar a with
          | true =>
            (* Message.print (Message.of_string "generated evar"); *)
            let n := '(_ :> $a) in
            Std.specialize ('($p $n), Std.NoBindings) None;
            specialise_many h hs
          | false =>
            let n := fresh_goal_of_constr a in
            (* Message.print (Message.of_string "generated goal"); *)
            (* exclude the newly-created goal *)
            Control.focus 1 (Int.sub (Control.numgoals ()) 1) (fun _ =>
              Std.specialize ('($p $n), Std.NoBindings) None;
              specialise_many h hs
            )
          end
        | _ =>
          Message.print (Message.of_string "not a function");
          ()
        end)
  end.

  (* Ltac2 fresh_goal_of_constr type :=
    let t := '(_ :> $type) in
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.Evar evar _ => Control.new_goal evar; t
    | _ => Control.zero Match_failure
    end. *)

   (* Ltac2 rec spec_by bfirst hyp :=
    let hyp' := Control.hyp hyp in
    lazy_match! Std.eval_hnf (Constr.type hyp') with
    | ?x -> _ =>
      let pf_term := fresh_goal_of_constr x in
      Control.focus 1 (Int.sub (Control.numgoals ()) 1) (fun _ =>
        Std.specialize ('($hyp' $pf_term), Std.NoBindings) None;
        spec_by false hyp
      )
    | _ => if bfirst then Control.zero (Tactic_failure (Some (fprintf "Not a product")))
           else ()
    end.

Ltac2 Notation "specialize_by" hyp(ident) := spec_by true hyp. *)


Ltac2 Notation "specialise" h(ident) args(list1(constr)) := specialise_many h args.

Example ex1_basics : forall (P Q R U T:Prop), U → T → R → P → (U → T → P → R → Q) → Q.
Proof.
  intros * Hu Ht Hr Hp H.
  specialise H Ht Hr.
  assumption.
  exact Hp.
  exact Hu.
Qed.

Example ex2_dependent A (y:A) P Q : P y → (∀ x, P x → Q) → Q.
Proof.
  intros Hp H.
  specialise H Hp.
  assumption.
Qed.

(* https://rocq-prover.zulipchat.com/#narrow/channel/278935-Ltac2/topic/pose.20proof.20.2F.20issues.20with.20ltac2.20in.20assert *)

Example some_lemma b : b = true → b = true.
Proof. auto. Qed.

Example ex3_lemma : True.
Proof.
  (* Proof Mode "Classic". *)
  (* this doesn't fail in lsp, but does in batch mode *)
  Proof Mode "Ltac2".
  pose (some_lemma).
  specialise e true.
  pose (some_lemma).
  assert (true = true). reflexivity.
  specialise e0 H.
  specialise e e0.
  constructor.
Qed.

(* FFI hell *)
(* https://rocq-prover.zulipchat.com/#narrow/channel/278935-Ltac2/topic/.E2.9C.94.20Ltac2.20Notations.20from.20ltac1.3F *)

Tactic Notation "specialise" ident(h) constr(t1) :=
  let tac := ltac2:(h t1 |-
    (* Message.print (Message.of_ident (Option.get (Ltac1.to_ident h))); *)
    (* Message.print (Message.of_constr (Option.get (Ltac1.to_constr t1))); *)
    specialise_many
      (Option.get (Ltac1.to_ident h))
      (List.map (fun t => Option.get (Ltac1.to_constr t))
        [t1])) in
  tac h t1.

Tactic Notation "specialise" ident(h) constr(t1) constr(t2) :=
  let tac := ltac2:(h t1 t2 |- specialise_many
    (Option.get (Ltac1.to_ident h))
    (List.map (fun t => Option.get (Ltac1.to_constr t))
      [t1; t2])) in
  tac h t1 t2.

Tactic Notation "specialise" ident(h) constr(t1) constr(t2) constr(t3) :=
  let tac := ltac2:(h t1 t2 t3 |- specialise_many
    (Option.get (Ltac1.to_ident h))
    (List.map (fun t => Option.get (Ltac1.to_constr t))
      [t1; t2; t3])) in
  tac h t1 t2 t3.

Tactic Notation "specialise" ident(h) constr(t1) constr(t2) constr(t3) constr(t4) :=
  let tac := ltac2:(h t1 t2 t3 t4 |- specialise_many
    (Option.get (Ltac1.to_ident h))
    (List.map (fun t => Option.get (Ltac1.to_constr t))
      [t1; t2; t3; t4])) in
  tac h t1 t2 t3 t4.

Tactic Notation "specialise" ident(h) constr(t1) constr(t2) constr(t3) constr(t4) constr(t5) :=
  let tac := ltac2:(h t1 t2 t3 t4 t5 |- specialise_many
    (Option.get (Ltac1.to_ident h))
    (List.map (fun t => Option.get (Ltac1.to_constr t))
      [t1; t2; t3; t4; t5])) in
  tac h t1 t2 t3 t4 t5.

Tactic Notation "specialise" ident(h) constr(t1) constr(t2) constr(t3) constr(t4) constr(t5) constr(t6) :=
  let tac := ltac2:(h t1 t2 t3 t4 t5 t6 |- specialise_many
    (Option.get (Ltac1.to_ident h))
    (List.map (fun t => Option.get (Ltac1.to_constr t))
      [t1; t2; t3; t4; t5; t6])) in
  tac h t1 t2 t3 t4 t5 t6.

Tactic Notation "specialise" ident(h) constr(t1) constr(t2) constr(t3) constr(t4) constr(t5) constr(t6) constr(t7) :=
  let tac := ltac2:(h t1 t2 t3 t4 t5 t6 t7 |- specialise_many
    (Option.get (Ltac1.to_ident h))
    (List.map (fun t => Option.get (Ltac1.to_constr t))
      [t1; t2; t3; t4; t5; t6; t7])) in
  tac h t1 t2 t3 t4 t5 t6 t7.
