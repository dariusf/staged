
From Stdlib Require Import Utf8.

From Ltac2 Require Import Ltac2 Printf Option.
Import Constr.
Import Unsafe.

Ltac2 debug s := Message.print (Message.of_string s).

Ltac2 inspect_kind (c:constr) :=
  match Constr.Unsafe.kind c with
  | Rel _ => debug "Rel"
  | Var _ => debug "Var"
  | Meta _ => debug "Meta"
  | Evar _ _ => debug "Evar"
  | Sort _ => debug "Sort"
  | Cast _ _ _ => debug "Cast"
  | Prod _ _ => debug "Prod"
  | Lambda _ _ => debug "Lambda"
  | LetIn _ _ _ => debug "LetIn"
  | App _ _ => debug "App"
  | Constant _ _ => debug "Constant"
  | Ind _ _ => debug "Ind"
  | Constructor _ _ => debug "Constructor"
  | Case _ _ _ _ _ => debug "Case"
  | Fix _ _ _ _ => debug "Fix"
  | CoFix _ _ _ => debug "CoFix"
  | Proj _ _ _ => debug "Proj"
  | Uint63 _ => debug "Uint63"
  | Float _ => debug "Float"
  | String _ => debug "String"
  | Array _ _ _ _ => debug "Array"
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
    (* debug "done"; *)
    ()
  | h1 :: hs1 =>
    (* print_goals0 (); *)
    (* debug "working on arg"; *)
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
        (* debug "managed to specialise"; *)
        specialise_many h hs1 (* only here do we advance *)
        )
      (fun _ =>
        (* debug "placeholder case"; *)
        match! Constr.type p with
        | ?a -> _  =>
          (* debug "type is"; *)
          (* Message.print (Message.of_constr a); *)
          match should_use_evar a with
          | true =>
            (* debug "generated evar"; *)
            let n := '(_ :> $a) in
            Std.specialize ('($p $n), Std.NoBindings) None;
            specialise_many h hs
          | false =>
            let n := fresh_goal_of_constr a in
            (* debug "generated goal"; *)
            (* put the new goal first *)
            (* this is not released yet... *)
            (* Control.cycle -1; *)
            ltac1:(cycle -1);
            (* exclude the newly-created goal *)
            (* Control.focus 1 (Int.sub (Control.numgoals ()) 1) (fun _ => *)
            Control.focus 2 (Control.numgoals ()) (fun _ =>
              Std.specialize ('($p $n), Std.NoBindings) None;
              specialise_many h hs
            )
          end
        | _ =>
          debug "not a function";
          ()
        end)
  end.

Ltac2 Notation "specialise" h(ident) args(list1(constr)) :=
  specialise_many h args.

(* TODO some lemmas can't be posed cleanly. build an app and pose it all at once? *)
Ltac2 applyy0 (h:constr) (h1:constr list) :=
  let x := Fresh.in_goal @H in
  (* this assumes new goals get added to the front.
    focus the goals that are after those, which should be
    the ones we started with *)
  let n := Control.numgoals () in
  assert ($x := $h);
  specialise_many x h1;
  let n1 := Int.sub (Control.numgoals ()) n in
  Control.focus (Int.add 1 n1) (Control.numgoals ()) (fun () =>
    let a := Control.hyp x in
    eapply $a
  );
  clear $x.

Ltac2 Notation "applyy" h(constr) args(list0(constr)) := applyy0 h args.

Ltac2 poseproof0 (h:constr) (hs:constr list) (name:ident option) :=
  let x := match name with | Some n => n | None => Fresh.in_goal @H end in
  assert ($x := $h);
  specialise_many x hs.

Ltac2 Notation "have:" h(constr) args(list0(constr)) :=
  poseproof0 h args None.

Ltac2 Notation "have" n(ident) ":" h(constr) args(list0(constr)) :=
  poseproof0 h args (Some n).

Example some_lemma b : b = true → b = true.
Proof. auto. Qed.

Example ex1_pose_proof : forall (P Q R:Prop), P → R → (P → R → Q) → Q.
Proof.
  intros * Hp Hr H.
  assert (true = true) as H1. reflexivity.
  have: some_lemma H1.
  have H2: some_lemma true.
  auto.
Qed.

Example ex1_applyy : forall (P Q R T:Prop),
  P → R → T → (P → R → T → Q) → Q.
Proof.
  intros * Hp Hr Ht H.
  applyy H Hr.
  exact Hp.
  exact Ht.
Qed.

Example ex2_applyy_external: True.
Proof.
  applyy I.
Qed.

Example ex3_applyy_external1 b: b = true → b = true.
Proof.
  intros H.
  applyy some_lemma H.
Qed.

Example ex1_basics : forall (P Q R U T:Prop), U → T → R → P → (U → T → P → R → Q) → Q.
Proof.
  intros * Hu Ht Hr Hp H.
  specialise H Ht Hr.
  exact Hu.
  exact Hp.
  assumption.
Qed.

Example ex2_dependent A (y:A) P Q : P y → (∀ x, P x → Q) → Q.
Proof.
  intros Hp H.
  specialise H Hp.
  assumption.
Qed.

(* https://rocq-prover.zulipchat.com/#narrow/channel/278935-Ltac2/topic/pose.20proof.20.2F.20issues.20with.20ltac2.20in.20assert *)

Example ex3_lemma : True.
Proof.
  (* Proof Mode "Classic". *)
  (* this doesn't fail in lsp, but does in batch mode *)
  Proof Mode "Ltac2".
  assert (e := some_lemma).
  specialise e true.
  assert (e0 := some_lemma).
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

(* applyy *)

Tactic Notation "applyy" constr(h) :=
  let tac := ltac2:(h t1 |-
    applyy0
      (Option.get (Ltac1.to_constr h))
      (List.map (fun t => Option.get (Ltac1.to_constr t))
        [t1])) in
  tac h.

Tactic Notation "applyy" constr(h) constr(t1) :=
  let tac := ltac2:(h t1 |-
    applyy0
      (Option.get (Ltac1.to_constr h))
      (List.map (fun t => Option.get (Ltac1.to_constr t))
        [t1])) in
  tac h t1.

Tactic Notation "applyy" constr(h) constr(t1) constr(t2) :=
  let tac := ltac2:(h t1 t2 |- applyy0
    (Option.get (Ltac1.to_constr h))
    (List.map (fun t => Option.get (Ltac1.to_constr t))
      [t1; t2])) in
  tac h t1 t2.

Tactic Notation "applyy" constr(h) constr(t1) constr(t2) constr(t3) :=
  let tac := ltac2:(h t1 t2 t3 |- applyy0
    (Option.get (Ltac1.to_constr h))
    (List.map (fun t => Option.get (Ltac1.to_constr t))
      [t1; t2; t3])) in
  tac h t1 t2 t3.

Tactic Notation "applyy" constr(h) constr(t1) constr(t2) constr(t3) constr(t4) :=
  let tac := ltac2:(h t1 t2 t3 t4 |- applyy0
    (Option.get (Ltac1.to_constr h))
    (List.map (fun t => Option.get (Ltac1.to_constr t))
      [t1; t2; t3; t4])) in
  tac h t1 t2 t3 t4.

Tactic Notation "applyy" constr(h) constr(t1) constr(t2) constr(t3) constr(t4) constr(t5) :=
  let tac := ltac2:(h t1 t2 t3 t4 t5 |- applyy0
    (Option.get (Ltac1.to_constr h))
    (List.map (fun t => Option.get (Ltac1.to_constr t))
      [t1; t2; t3; t4; t5])) in
  tac h t1 t2 t3 t4 t5.

Tactic Notation "applyy" constr(h) constr(t1) constr(t2) constr(t3) constr(t4) constr(t5) constr(t6) :=
  let tac := ltac2:(h t1 t2 t3 t4 t5 t6 |- applyy0
    (Option.get (Ltac1.to_constr h))
    (List.map (fun t => Option.get (Ltac1.to_constr t))
      [t1; t2; t3; t4; t5; t6])) in
  tac h t1 t2 t3 t4 t5 t6.

Tactic Notation "applyy" constr(h) constr(t1) constr(t2) constr(t3) constr(t4) constr(t5) constr(t6) constr(t7) :=
  let tac := ltac2:(h t1 t2 t3 t4 t5 t6 t7 |- applyy0
    (Option.get (Ltac1.to_constr h))
    (List.map (fun t => Option.get (Ltac1.to_constr t))
      [t1; t2; t3; t4; t5; t6; t7])) in
  tac h t1 t2 t3 t4 t5 t6 t7.

(* have: *)

Tactic Notation "have:" constr(h) :=
  let tac := ltac2:(h |-
    poseproof0
      (Option.get (Ltac1.to_constr h))
      (List.map (fun t => Option.get (Ltac1.to_constr t))
        []) None) in
  tac h.

Tactic Notation "have:" constr(h) constr(t1) :=
  let tac := ltac2:(h t1 |-
    poseproof0
      (Option.get (Ltac1.to_constr h))
      (List.map (fun t => Option.get (Ltac1.to_constr t))
        [t1]) None) in
  tac h t1.

Tactic Notation "have:" constr(h) constr(t1) constr(t2) :=
  let tac := ltac2:(h t1 t2 |- poseproof0
    (Option.get (Ltac1.to_constr h))
    (List.map (fun t => Option.get (Ltac1.to_constr t))
      [t1; t2]) None) in
  tac h t1 t2.

Tactic Notation "have:" constr(h) constr(t1) constr(t2) constr(t3) :=
  let tac := ltac2:(h t1 t2 t3 |- poseproof0
    (Option.get (Ltac1.to_constr h))
    (List.map (fun t => Option.get (Ltac1.to_constr t))
      [t1; t2; t3]) None) in
  tac h t1 t2 t3.

Tactic Notation "have:" constr(h) constr(t1) constr(t2) constr(t3) constr(t4) :=
  let tac := ltac2:(h t1 t2 t3 t4 |- poseproof0
    (Option.get (Ltac1.to_constr h))
    (List.map (fun t => Option.get (Ltac1.to_constr t))
      [t1; t2; t3; t4]) None) in
  tac h t1 t2 t3 t4.

Tactic Notation "have:" constr(h) constr(t1) constr(t2) constr(t3) constr(t4) constr(t5) :=
  let tac := ltac2:(h t1 t2 t3 t4 t5 |- poseproof0
    (Option.get (Ltac1.to_constr h))
    (List.map (fun t => Option.get (Ltac1.to_constr t))
      [t1; t2; t3; t4; t5]) None) in
  tac h t1 t2 t3 t4 t5.

Tactic Notation "have:" constr(h) constr(t1) constr(t2) constr(t3) constr(t4) constr(t5) constr(t6) :=
  let tac := ltac2:(h t1 t2 t3 t4 t5 t6 |- poseproof0
    (Option.get (Ltac1.to_constr h))
    (List.map (fun t => Option.get (Ltac1.to_constr t))
      [t1; t2; t3; t4; t5; t6]) None) in
  tac h t1 t2 t3 t4 t5 t6.

Tactic Notation "have:" constr(h) constr(t1) constr(t2) constr(t3) constr(t4) constr(t5) constr(t6) constr(t7) :=
  let tac := ltac2:(h t1 t2 t3 t4 t5 t6 t7 |- poseproof0
    (Option.get (Ltac1.to_constr h))
    (List.map (fun t => Option.get (Ltac1.to_constr t))
      [t1; t2; t3; t4; t5; t6; t7]) None) in
  tac h t1 t2 t3 t4 t5 t6 t7.

(* have H: ... *)

Tactic Notation "have" ident(n) ":" constr(h) :=
  let tac := ltac2:(n h |-
    poseproof0
      (Option.get (Ltac1.to_constr h))
      (List.map (fun t => Option.get (Ltac1.to_constr t))
        []) (Ltac1.to_ident n)) in
  tac n h.

Tactic Notation "have" ident(n) ":" constr(h) constr(t1) :=
  let tac := ltac2:(n h t1 |-
    poseproof0
      (Option.get (Ltac1.to_constr h))
      (List.map (fun t => Option.get (Ltac1.to_constr t))
        [t1]) (Ltac1.to_ident n)) in
  tac n h t1.

Tactic Notation "have" ident(n) ":" constr(h) constr(t1) constr(t2) :=
  let tac := ltac2:(n h t1 t2 |- poseproof0
    (Option.get (Ltac1.to_constr h))
    (List.map (fun t => Option.get (Ltac1.to_constr t))
      [t1; t2]) (Ltac1.to_ident n)) in
  tac n h t1 t2.

Tactic Notation "have" ident(n) ":" constr(h) constr(t1) constr(t2) constr(t3) :=
  let tac := ltac2:(n h t1 t2 t3 |- poseproof0
    (Option.get (Ltac1.to_constr h))
    (List.map (fun t => Option.get (Ltac1.to_constr t))
      [t1; t2; t3]) (Ltac1.to_ident n)) in
  tac n h t1 t2 t3.

Tactic Notation "have" ident(n) ":" constr(h) constr(t1) constr(t2) constr(t3) constr(t4) :=
  let tac := ltac2:(n h t1 t2 t3 t4 |- poseproof0
    (Option.get (Ltac1.to_constr h))
    (List.map (fun t => Option.get (Ltac1.to_constr t))
      [t1; t2; t3; t4]) (Ltac1.to_ident n)) in
  tac n h t1 t2 t3 t4.

Tactic Notation "have" ident(n) ":" constr(h) constr(t1) constr(t2) constr(t3) constr(t4) constr(t5) :=
  let tac := ltac2:(n h t1 t2 t3 t4 t5 |- poseproof0
    (Option.get (Ltac1.to_constr h))
    (List.map (fun t => Option.get (Ltac1.to_constr t))
      [t1; t2; t3; t4; t5]) (Ltac1.to_ident n)) in
  tac n h t1 t2 t3 t4 t5.

Tactic Notation "have" ident(n) ":" constr(h) constr(t1) constr(t2) constr(t3) constr(t4) constr(t5) constr(t6) :=
  let tac := ltac2:(n h t1 t2 t3 t4 t5 t6 |- poseproof0
    (Option.get (Ltac1.to_constr h))
    (List.map (fun t => Option.get (Ltac1.to_constr t))
      [t1; t2; t3; t4; t5; t6]) (Ltac1.to_ident n)) in
  tac n h t1 t2 t3 t4 t5 t6.

Tactic Notation "have" ident(n) ":" constr(h) constr(t1) constr(t2) constr(t3) constr(t4) constr(t5) constr(t6) constr(t7) :=
  let tac := ltac2:(n h t1 t2 t3 t4 t5 t6 t7 |- poseproof0
    (Option.get (Ltac1.to_constr h))
    (List.map (fun t => Option.get (Ltac1.to_constr t))
      [t1; t2; t3; t4; t5; t6; t7]) (Ltac1.to_ident n)) in
  tac n h t1 t2 t3 t4 t5 t6 t7.
