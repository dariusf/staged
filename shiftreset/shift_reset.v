Inductive type : Type :=
| TyPure : Type -> type
| TyFunc : type -> type -> type -> type -> type.

(* Notation "t / a --> s / b" := (Func t s a b) (at level 40, a at next level, s at next level). *)

Section Syntax.
  Variable var : type -> Type.

  Inductive expr (var : type -> Type) : type -> type -> type -> Type :=
  | Var : forall t a, var t -> expr var t a a
  | Const : forall (t : Type) a, t -> expr var (TyPure t) a a
  | Abs : forall dom ran a b c, (var dom -> expr var ran a b) -> expr var (TyFunc dom ran a b) c c
  | App : forall dom ran a b c d, expr var (TyFunc dom ran a b) c d -> expr var dom b c -> expr var ran a d
  | Lift : forall dom ran a b, (dom -> ran) -> expr var (TyPure dom) a b -> expr var (TyPure ran) a b
  | Shift : forall t a b c d, (var (TyFunc t a d d) -> expr var c c b) -> expr var t a b
  | Reset : forall t a b, expr var a a t -> expr var t b b.
End Syntax.

Fixpoint type_denote (t : type) : Type :=
  match t with
  | TyPure t => t
  | TyFunc dom ran a b => type_denote dom -> (type_denote ran -> type_denote a) -> type_denote b
  end.

Lemma fold_unfold_type_denote_TyPure :
  forall (t : Type),
    type_denote (TyPure t) =
    t.
Proof. auto. Qed.

Lemma fold_unfold_type_denote_TyFunc :
  forall (dom ran a b : type),
    type_denote (TyFunc dom ran a b) =
    (type_denote dom -> (type_denote ran -> type_denote a) -> type_denote b).
Proof. auto. Qed.

(** [x : Expr t a b] means that the term [x] has type [t] and evaluation of it changes the answer type from [a] to [b]. *)
Definition Expr t a b := forall var, expr var t a b.

Fixpoint interpret_aux (t a b : type) (e : expr type_denote t a b) (k : type_denote t -> type_denote a) : type_denote b.
Proof.
  inversion e as
    [ t' a' x Eq_t Eq_a Eq_b
    | t' a' v Eq_t Eq_a Eq_b
    | dom ran a' b' c f Eq_t Eq_a Eq_b
    | dom ran a' b' c d e1 e2 Eq_t Eq_a Eq_b
    | dom ran a' b' f e' Eq_t Eq_a Eq_b
    | t' a' b' c d f Eq_t Eq_a Eq_b
    | t' a' b' e' Eq_t Eq_a Eq_b]; clear e.
  - rewrite <- Eq_b.
    exact (k x).
  - rewrite <- Eq_t in k.
    rewrite <- Eq_b.
    exact (k v).
  - rewrite <- Eq_t in k.
    rewrite <- Eq_b.
    exact (k (fun x => interpret_aux ran a' b' (f x))).
  - exact (interpret_aux (TyFunc dom t a b') c b e1 (fun f => interpret_aux dom b' c e2 (fun x => f x k))).
  - rewrite <- Eq_t in k.
    exact (interpret_aux (TyPure dom) a b e' (fun x => k (f x))).
  - exact (interpret_aux c c b (f (fun x k' => k' (k x))) (fun x => x)).
  - rewrite <- Eq_b.
    exact (k (interpret_aux a' a' t e' (fun x => x))).
Defined.

Definition interpret (t : type) (e : expr type_denote t t t) : type_denote t :=
  interpret_aux t t t e (fun x => x).

Lemma fold_unfold_interpret_aux_Var :
  forall (t a : type)
         (x : type_denote t)
         (k : type_denote t -> type_denote a),
    interpret_aux t a a (Var type_denote t a x) k =
    k x.
Proof. auto. Qed.

Lemma fold_unfold_interpret_aux_Const :
  forall (t : Type)
         (a : type)
         (v : t)
         (k : t -> type_denote a),
    interpret_aux (TyPure t) a a (Const type_denote t a v) k =
    k v.
Proof. auto. Qed.

Lemma fold_unfold_interpret_aux_Abs :
  forall (dom ran a b c : type)
         (f : type_denote dom -> expr type_denote ran a b)
         (k : (type_denote dom -> (type_denote ran -> type_denote a) -> type_denote b) -> type_denote c),
    interpret_aux (TyFunc dom ran a b) c c (Abs type_denote dom ran a b c f) k =
    k (fun x => interpret_aux ran a b (f x)).
Proof. auto. Qed.

Lemma fold_unfold_interpret_aux_App :
  forall (dom ran a b c d : type)
         (e1 : expr type_denote (TyFunc dom ran a b) c d)
         (e2 : expr type_denote dom b c)
         (k : type_denote ran -> type_denote a),
    interpret_aux ran a d (App type_denote dom ran a b c d e1 e2) k =
    interpret_aux (TyFunc dom ran a b) c d e1 (fun f => interpret_aux dom b c e2 (fun x => f x k)).
Proof. auto. Qed.

Lemma fold_unfold_interpret_aux_Lift :
  forall (dom ran : Type)
         (a b : type)
         (f : dom -> ran)
         (e : expr type_denote (TyPure dom) a b)
         (k : ran -> type_denote a),
    interpret_aux (TyPure ran) a b (Lift type_denote dom ran a b f e) k =
    interpret_aux (TyPure dom) a b e (fun x => k (f x)).
Proof. auto. Qed.

Lemma fold_unfold_interpret_aux_Shift :
  forall (t a b c d : type)
         (f : (type_denote t -> (type_denote a -> type_denote d) -> type_denote d) -> expr type_denote c c b)
         (k : type_denote t -> type_denote a),
    interpret_aux t a b (Shift type_denote t a b c d f) k =
    interpret_aux c c b (f (fun x k' => k' (k x))) (fun x => x).
Proof. auto. Qed.

Lemma fold_unfold_interpret_aux_Reset :
  forall (t a b : type)
         (e : expr type_denote a a t)
         (k : type_denote t -> type_denote b),
    interpret_aux t b b (Reset type_denote t a b e) k =
    k (interpret_aux a a t e (fun x => x)).
Proof. auto. Qed.

Require Import List Arith.
Import ListNotations.

Fixpoint append_delim_aux (A : Type) (xs : list A) :
  expr type_denote
    (TyPure (list A))
    (TyPure (list A))
    (TyFunc (TyPure (list A)) (TyPure (list A)) (TyPure (list A)) (TyPure (list A))) :=
  match xs with
  | [] => Shift _ _ _ _ _ _ (fun k => Var _ _ _ k)
  | x :: xs' => Lift _ _ _ _ _ (cons x) (append_delim_aux A xs')
  end.

Lemma fold_unfold_append_delim_aux_nil :
  forall (A : Type),
    append_delim_aux A [] =
    Shift _ _ _ _ _ _ (fun k => Var _ _ _ k).
Proof. auto. Qed.

Lemma fold_unfold_append_delim_aux_cons :
  forall (A : Type)
         (x : A)
         (xs' : list A),
    append_delim_aux A (x :: xs') =
    Lift _ _ _ _ _ (cons x) (append_delim_aux A xs').
Proof. auto. Qed.

Definition append_delim (A : Type) (xs ys : list A) :
  expr type_denote
    (TyPure (list A))
    (TyPure (list A))
    (TyPure (list A)) :=
  App _ _ _ _ _ _ _ (Reset _ _ _ _ (append_delim_aux A xs)) (Const _ _ _ ys).

Definition append_delim_unit_tests : bool :=
  let unit_test xs ys := if list_eq_dec Nat.eq_dec (interpret _ (append_delim nat xs ys)) (xs ++ ys) then true else false in
  unit_test [] []
  && unit_test [] [0]
  && unit_test [0] []
  && unit_test [0; 1] []
  && unit_test [] [0; 1]
  && unit_test [0] [1]
  && unit_test [0; 1] [2]
  && unit_test [0] [1; 2]
  && unit_test [0; 1] [2; 3].

Compute append_delim_unit_tests.

Lemma fold_unfold_app_nil :
  forall (A : Type)
         (ys : list A),
    [] ++ ys = ys.
Proof. auto. Qed.

Lemma fold_unfold_app_cons :
  forall (A : Type)
         (x : A)
         (xs ys : list A),
    (x :: xs) ++ ys = x :: xs ++ ys.
Proof. auto. Qed.

Lemma append_delim_is_equivalence_to_append_aux :
  forall (A : Type)
         (xs ys : list A)
         (k : list A -> list A),
    interpret_aux
      (TyPure (list A))
      (TyPure (list A))
      (TyFunc (TyPure (list A)) (TyPure (list A)) (TyPure (list A)) (TyPure (list A)))
      (append_delim_aux A xs) k ys (fun x => x) =
    k (xs ++ ys).
Proof.
  intros A xs ys.
  induction xs as [| x xs' IHxs']; intros k.
  - rewrite -> fold_unfold_append_delim_aux_nil.
    rewrite -> fold_unfold_interpret_aux_Shift.
    rewrite -> fold_unfold_interpret_aux_Var.
    rewrite -> app_nil_l.
    reflexivity.
  - rewrite -> fold_unfold_append_delim_aux_cons.
    rewrite -> fold_unfold_interpret_aux_Lift.
    rewrite -> fold_unfold_app_cons.
    rewrite -> (IHxs' (fun r : type_denote (TyPure (list A)) => k (x :: r))).
    reflexivity.
Qed.

Theorem append_delim_is_equivalence_to_append :
  forall (A : Type)
         (xs ys : list A),
    interpret (TyPure (list A)) (append_delim A xs ys) =
    xs ++ ys.
Proof.
  intros A xs ys.
  unfold interpret, append_delim.
  rewrite -> fold_unfold_interpret_aux_App.
  rewrite -> fold_unfold_interpret_aux_Reset.
  rewrite -> fold_unfold_interpret_aux_Const.
  exact (append_delim_is_equivalence_to_append_aux A xs ys (fun x => x)).
Qed.

Fixpoint times_delim_aux (xs : list nat) :
  expr type_denote
    (TyPure nat)
    (TyPure nat)
    (TyPure nat) :=
  match xs with
  | [] => Const _ _ _ 1
  | x :: xs' => match x with
                | O => Shift _ _ _ _ _ (TyPure nat) (fun _ => Const _ _ _ 0)
                | _ => Lift _ _ _ _ _ (Nat.mul x) (times_delim_aux xs')
                end
  end.

Definition times_delim (xs : list nat) :
  expr type_denote
    (TyPure nat)
    (TyPure nat)
    (TyPure nat) :=
  Reset _ _ _ _ (times_delim_aux xs).

Lemma fold_unfold_times_delim_aux_nil :
  times_delim_aux [] =
  Const _ _ _ 1.
Proof. auto. Qed.

Lemma fold_unfold_times_delim_aux_cons :
  forall (x : nat)
         (xs' : list nat),
    times_delim_aux (x :: xs') =
    match x with
    | O => Shift _ _ _ _ _ (TyPure nat) (fun _ => Const _ _ _ 0)
    | _ => Lift _ _ _ _ _ (Nat.mul x) (times_delim_aux xs')
    end.
Proof. auto. Qed.

Fixpoint times (xs : list nat) : nat :=
  match xs with
  | [] => 1
  | x :: xs' => x * times xs'
  end.

Lemma fold_unfold_times_nil :
  times [] = 1.
Proof. auto. Qed.

Lemma fold_unfold_times_cons :
  forall (x : nat)
         (xs' : list nat),
    times (x :: xs') =
    x * times xs'.
Proof. auto. Qed.

Lemma times_delim_is_equivalence_to_times_aux :
  forall (xs : list nat)
         (k : nat -> nat),
    interpret_aux (TyPure nat) (TyPure nat) (TyPure nat) (times_delim_aux xs) k =
    match times xs with
    | O => O
    | S r' => k (S r')
    end.
Proof.
  intros xs.
  induction xs as [| x xs' IHxs']; intros k.
  - rewrite -> fold_unfold_times_delim_aux_nil.
    rewrite -> fold_unfold_interpret_aux_Const.
    rewrite -> fold_unfold_times_nil.
    reflexivity.
  - rewrite -> fold_unfold_times_delim_aux_cons.
    rewrite -> fold_unfold_times_cons.
    destruct x as [| x'].
    + rewrite -> fold_unfold_interpret_aux_Shift.
      rewrite -> fold_unfold_interpret_aux_Const.
      reflexivity.
    + rewrite -> fold_unfold_interpret_aux_Lift.
      rewrite -> (IHxs' (fun r : type_denote (TyPure nat) => k (S x' * r))).
      destruct (times xs') as [| r'].
      * rewrite -> Nat.mul_0_r.
        reflexivity.
      * reflexivity.
Qed.

Theorem times_delim_is_equivalence_to_times :
  forall (xs : list nat),
    interpret (TyPure nat) (times_delim xs) =
    times xs.
Proof.
  intros xs.
  unfold interpret, times_delim.
  rewrite -> fold_unfold_interpret_aux_Reset.
  assert (ly := times_delim_is_equivalence_to_times_aux xs (fun x => x)).
  destruct (times xs) as [| r'].
  - exact ly.
  - exact ly.
Qed.
