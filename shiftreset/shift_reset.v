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

Require Import List Arith.
Import ListNotations.

Fixpoint append_delim_aux (A : Type) (xs : list A) :=
  match xs with
  | [] => Shift type_denote _ _ _ _ (TyPure (list A)) (fun k => Var _ _ _ k)
  | x :: xs' => Lift _ _ _ (TyPure (list A)) _ (cons x) (append_delim_aux A xs')
  end.

Definition append_delim (A : Type) (xs ys : list A) : list A :=
  interpret _ (App _ _ _ _ _ _ _ (Reset _ _ _ _ (append_delim_aux A xs)) (Const _ _ _ ys)).

Definition append_delim_unit_tests : bool :=
  let unit_test xs ys := if list_eq_dec Nat.eq_dec (append_delim nat xs ys) (xs ++ ys) then true else false in
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
