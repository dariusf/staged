(* remove when https://github.com/coq/coq/pull/19673 is merged *)
Set Warnings "-notation-incompatible-prefix".
From Staged Require Import HeapF.
Set Warnings "notation-incompatible-prefix".
From Staged Require Import LibFmap.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Set Implicit Arguments.

Definition Z_eq_dec := Z.eq_dec.
Definition nat_eq_dec := Nat.eq_dec.
Definition bool_eq_dec := Bool.bool_dec.
Definition string_eq_dec := String.string_dec.

Inductive var : Set := var_of : string -> var.
Definition of_var (v : var) : string := match v with var_of s => s end.

Lemma var_eq_dec : forall (x1 x2 : var), {x1 = x2} + {x1 <> x2}.
Proof. decide equality. apply string_eq_dec. Defined.

Inductive loc : Set := loc_of : nat -> loc.
Definition null : loc := loc_of 0.
Definition of_loc (l : loc) : nat := match l with loc_of n => n end.

Lemma loc_eq_dec : forall (l1 l2 : loc), {l1 = l2} + {l1 <> l2}.
Proof. decide equality. apply nat_eq_dec. Defined.

Inductive prim1 : Set :=
| prim1_neg : prim1
| prim1_ref : prim1
| prim1_get : prim1
| prim1_free : prim1
| prim1_fst : prim1
| prim1_snd : prim1.

Definition prim1_eq_dec : forall (op1 op2 : prim1), {op1 = op2} + {op1 <> op2}.
Proof. decide equality. Defined.

Inductive prim2 : Set :=
| prim2_add : prim2
| prim2_sub : prim2
| prim2_mul : prim2
| prim2_eq : prim2
| prim2_lt : prim2
| prim2_set : prim2
| prim2_cat : prim2 (* string *)
| prim2_pair : prim2.

Definition prim2_eq_dec : forall (op1 op2 : prim2), {op1 = op2} + {op1 <> op2}.
Proof. decide equality. Defined.

Inductive val : Set :=
| val_unit : val
| val_bool : bool -> val
| val_int : Z -> val
| val_loc : loc -> val
| val_fun : var -> expr -> val
| val_fix : var -> var -> expr -> val
| val_str : string -> val
| val_pair : val -> val -> val
with expr : Set :=
| expr_val : val -> expr
| expr_var : var -> expr
| expr_fun : var -> expr -> expr
| expr_fix : var -> var -> expr -> expr
| expr_app : expr -> expr -> expr
| expr_seq : expr -> expr -> expr
| expr_let : var -> expr -> expr -> expr
| expr_if : expr -> expr -> expr -> expr
| expr_prim1 : prim1 -> expr -> expr
| expr_prim2 : prim2 -> expr -> expr -> expr
| expr_shift : var -> expr -> expr (* shift *)
| expr_reset : expr -> expr (* reset *)
| expr_cont : expr -> var -> expr -> expr.

#[global] Instance Inhab_val : Inhab val.
Proof. exact (Inhab_of_val val_unit). Qed.

#[global] Instance Inhab_expr : Inhab expr.
Proof. exact (Inhab_of_val (expr_val val_unit)). Qed.

Lemma val_eq_dec : forall (v1 v2 : val), {v1 = v2} + {v1 <> v2}
with expr_eq_dec : forall (e1 e2 : expr), {e1 = e2} + {e1 <> e2}.
Proof.
  { decide equality; auto using bool_eq_dec, Z_eq_dec, loc_eq_dec, var_eq_dec, string_eq_dec. }
  { decide equality; auto using var_eq_dec, prim1_eq_dec, prim2_eq_dec. }
Defined.

Definition val_eqb (v1 v2 : val) : bool := if val_eq_dec v1 v2 then true else false.
Definition expr_eqb (e1 e2 : expr) : bool := if expr_eq_dec e1 e2 then true else false.

Module CoerceVal.
  Coercion val_bool : bool >-> val.
  Coercion val_int : Z >-> val.
  Coercion val_loc : loc >-> val.
  Coercion val_str : string >-> val.
End CoerceVal.

Module CoerceExpr.
  Coercion expr_val : val >-> expr.
  Coercion expr_var : var >-> expr.
End CoerceExpr.

Module ProgramNotations.
  Declare Custom Entry expr.
  Declare Scope val_scope.
  Declare Scope expr_scope.

  Notation "<{ e }>" := e (e custom expr at level 99) : expr_scope.
  Notation "( e )" := e (in custom expr, e at level 99) : expr_scope.
  Notation "{ e }" := e (in custom expr, e constr) : expr_scope.
  Notation "e" := e (in custom expr at level 0, e constr at level 0) : expr_scope.
  Notation "'begin' e 'end'" := e (in custom expr, e custom expr at level 99, only parsing) : expr_scope.

  Notation "e1 e2" :=
    (expr_app e1 e2)
      (in custom expr at level 10,
          e1 custom expr,
          e2 custom expr,
          left associativity) : expr_scope.

  Notation "'if' e1 'then' e2 'else' e3" :=
    (expr_if e1 e2 e3)
      (in custom expr at level 69,
          e1 custom expr,
          e2 custom expr,
          e3 custom expr) : expr_scope.

  Notation "e1 ; e2" :=
    (expr_seq e1 e2)
      (in custom expr at level 69,
          e1 custom expr,
          e2 custom expr,
          right associativity) : expr_scope.

  Notation "'let' x '=' e1 'in' e2" :=
    (expr_let (var_of x) e1 e2)
      (in custom expr at level 69,
          x at level 0,
          e1 custom expr,
          e2 custom expr,
          right associativity) : expr_scope.

  Notation "'let' f x1 .. xn '=' e1 'in' e2" :=
    (expr_let (var_of f) (expr_fun (var_of x1) .. (expr_fun (var_of xn) e1) ..) e2)
      (in custom expr at level 69,
          f, x1, xn at level 0,
          e1 custom expr,
          e2 custom expr,
          right associativity) : expr_scope.

  Notation "'let' 'rec' f x '=' e1 'in' e2" :=
    (expr_let (var_of f) (expr_fix (var_of f) (var_of x) e1) e2)
      (in custom expr at level 69,
          f, x at level 0,
          e1 custom expr,
          e2 custom expr,
          right associativity) : expr_scope.

  Notation "'let' 'rec' f x1 x2 .. xn '=' e1 'in' e2" :=
    (expr_let (var_of f) (expr_fix (var_of f) (var_of x1) (expr_fun (var_of x2) .. (expr_fun (var_of xn) e1) ..)) e2)
      (in custom expr at level 69,
          f, x1, x2, xn at level 0,
          e1 custom expr,
          e2 custom expr,
          right associativity) : expr_scope.

  Notation "'fun' x1 .. xn '=>' e" :=
    (expr_fun (var_of x1) .. (expr_fun (var_of xn) e) ..)
      (in custom expr at level 69,
          x1, xn at level 0,
          e custom expr at level 99) : expr_scope.

  Notation "'fix' f x '=>' e" :=
    (expr_fix (var_of f) (var_of x) e)
      (in custom expr at level 69,
          f, x at level 0,
          e custom expr at level 99) : expr_scope.

  Notation "'fix' f x1 x2 .. xn '=>' e" :=
    (expr_fix f (var_of x1) (expr_fun (var_of x2) .. (expr_fun (var_of xn) e) ..))
      (in custom expr at level 69,
          f, x1, x2, xn at level 0,
          e custom expr at level 99) : expr_scope.

  (* shift *)
  Notation "'shift' k '=>' e" :=
    (expr_shift (var_of k) e)
      (in custom expr at level 69,
          k at level 0,
          e custom expr at level 99) : expr_scope.

  (* reset *)
  Notation "< e >" :=
    (expr_reset e) (in custom expr at level 69, e custom expr) : expr_scope.

  (* function value *)
  Notation "'\fun' x '=>' e" :=
    (val_fun (var_of x) e)
      (in custom expr at level 69,
          x at level 0,
          e custom expr at level 99) : val_scope.

  Notation "'\fun' x1 x2 .. xn '=>' e" :=
    (val_fun (var_of x1) (expr_fun (var_of x2) .. (expr_fun (var_of xn) e) ..))
      (in custom expr at level 69,
          x1, x2, xn at level 0,
          e custom expr at level 99) : val_scope.

  Notation "'\fix' f x '=>' e" :=
    (val_fix (var_of f) (var_of x) e)
      (in custom expr at level 69,
          f, x at level 0,
          e custom expr at level 99) : val_scope.

  Notation "'\fix' f x1 x2 .. xn '=>' e" :=
    (val_fix (var_of f) (var_of x1) (expr_fun (var_of x2) .. (expr_fun (var_of xn) e) ..))
      (in custom expr at level 69,
          f, x1, x2, xn at level 0,
          e custom expr at level 99) : val_scope.

  Notation "()" := (expr_val val_unit) (in custom expr at level 0) : expr_scope.

  Notation "'not' e" :=
    (expr_prim1 prim1_neg e)
      (in custom expr at level 23, e custom expr at level 0) : expr_scope.

  Notation "'ref' e" :=
    (expr_prim1 prim1_ref e)
      (in custom expr at level 23, e custom expr at level 0) : expr_scope.

  Notation "! e" :=
    (expr_prim1 prim1_get e)
      (in custom expr at level 23, e custom expr at level 0) : expr_scope.

  Notation "'free' e" :=
    (expr_prim1 prim1_free e)
      (in custom expr at level 23, e custom expr at level 0) : expr_scope.

  Notation "'fst' e" :=
    (expr_prim1 prim1_fst e)
      (in custom expr at level 23, e custom expr at level 0) : expr_scope.

  Notation "'snd' e" :=
    (expr_prim1 prim1_snd e)
      (in custom expr at level 23, e custom expr at level 0) : expr_scope.

  Notation "e1 + e2" :=
    (expr_prim2 prim2_add e1 e2)
      (in custom expr at level 40,
          e1 custom expr,
          e2 custom expr,
          left associativity) : expr_scope.

  Notation "e1 - e2" :=
    (expr_prim2 prim2_sub e1 e2)
      (in custom expr at level 40,
          e1 custom expr,
          e2 custom expr,
          left associativity) : expr_scope.

  Notation "e1 * e2" :=
    (expr_prim2 prim2_mul e1 e2)
      (in custom expr at level 39,
          e1 custom expr,
          e2 custom expr,
          left associativity) : expr_scope.

  Notation "e1 = e2" :=
    (expr_prim2 prim2_eq e1 e2)
      (in custom expr at level 50,
          e1 custom expr,
          e2 custom expr,
          left associativity) : expr_scope.

  Notation "e1 < e2" :=
    (expr_prim2 prim2_lt e1 e2)
      (in custom expr at level 50,
          e1 custom expr,
          e2 custom expr,
          left associativity) : expr_scope.

  Notation "e1 := e2" :=
    (expr_prim2 prim2_set e1 e2)
      (in custom expr at level 65,
          e1 custom expr,
          e2 custom expr,
          right associativity) : expr_scope.

  Notation "e1 ^ e2" :=
    (expr_prim2 prim2_cat e1 e2)
      (in custom expr at level 65,
          e1 custom expr,
          e2 custom expr,
          right associativity) : expr_scope.

  Notation "e1 , e2" :=
    (expr_prim2 prim2_pair e1 e2)
      (in custom expr at level 65,
          e1 custom expr,
          e2 custom expr,
          right associativity) : expr_scope.
End ProgramNotations.

Module TestProgramNotations.
  Import ProgramNotations.
  Import CoerceVal.
  Import CoerceExpr.

  Local Open Scope val_scope.
  Local Open Scope expr_scope.
  Set Printing Coercions.
  Unset Printing Notations.

  Definition test_app1 e1 e2 : expr := <{ e1 e2 }>.
  Print test_app1.

  Definition test_app2 e1 e2 e3 : expr := <{ e1 e2 e3 }>.
  Print test_app2.

  Definition test_app3 e1 e2 e3 : expr := <{ e1 (e2 e3) }>.
  Print test_app3.

  Definition test_fun1 x e : expr := <{ fun x => e }>.
  Print test_fun1.

  Definition test_fun2 x1 x2 e : expr := <{ fun x1 x2 => e }>.
  Print test_fun2.

  Definition test_fun3 x1 x2 x3 e : expr := <{ fun x1 x2 x3 => e }>.
  Print test_fun3.

  Definition test_fix1 f x e : expr := <{ fix f x => e }>.
  Print test_fix1.

  Definition test_fix2 f x1 x2 e : expr := <{ fix f x1 x2 => e }>.
  Print test_fix2.

  Definition test_fix3 f x1 x2 x3 e : expr := <{ fix f x1 x2 x3 => e }>.
  Print test_fix3.

  Definition test_letfun1 f x e1 e2 : expr := <{ let f x = e1 in e2 }>.
  Print test_letfun1.

  Definition test_letfun2 f x1 x2 e1 e2 : expr := <{ let f x1 x2 = e1 in e2 }>.
  Print test_letfun2.

  Definition test_letfun3 f x1 x2 x3 e1 e2 : expr := <{ let f x1 x2 x3 = e1 in e2 }>.
  Print test_letfun3.

  Definition test_letfun_coerce1 f x e : expr := <{ let f x = x in e }>.
  Print test_letfun_coerce1.

  Definition test_letfun_coerce2 f x e : expr := <{ let f x = e in f }>.
  Print test_letfun_coerce2.

  Definition test_letfun_app1 f g e1 e2 : expr := <{ let f g = g e1 in e2 }>.
  Print test_letfun_app1.

  Definition test_letfix1 f x e1 e2 : expr := <{ let rec f x = e1 in e2 }>.
  Print test_letfix1.

  Definition test_letfix2 f x1 x2 e1 e2 : expr := <{ let rec f x1 x2 = e1 in e2 }>.
  Print test_letfix2.

  Definition test_unit1 : expr := <{ () }>.
  Print test_unit1.

  Definition test_ref1 : expr := <{ ref false }>.
  Print test_ref1.

  Definition test_ref2 : expr := <{ ref 1 }>.
  Print test_ref2.

  Definition test_ref3 : expr := <{ ref (1 + 2) }>.
  Print test_ref3.

  Definition test_get1 : expr := <{ ! null }>.
  Print test_get1.

  Definition test_add1 e : expr := <{ e + 1 }>.
  Print test_add1.

  Definition test_lt1 : expr := <{ 1 < 2 }>.
  Print test_lt1.

  Definition test_arithmetic1 : expr := <{ 1 + 2 * 3 }>.
  Print test_arithmetic1.

  Definition test_arithmetic2 : expr := <{ 1 + 2 < 3 * 4 }>.
  Print test_arithmetic2.

  Definition test_arithmetic3 : expr := <{ 1 + 2 * 0 = 3 * 4 }>.
  Print test_arithmetic3.

  Definition test_arithmetic4 : expr := <{ 1 = 2 - 1 = false }>.
  Print test_arithmetic4.

  Definition test_set1 x e : expr := <{ x := e }>.
  Print test_set1.

  Definition test_set_arithmetic1 : expr := <{ ref 0 := 42 + 6 * 9 }>.
  Print test_set_arithmetic1.

  Definition test_set_arithmetic2 e1 e2 : expr := <{ e1 e2 := true = false }>.
  Print test_set_arithmetic2.

  Definition test_shift1 k e : expr := <{ shift k => e }>.
  Print test_shift1.

  Definition test_reset1 : expr := <{ <1 + 1> }>.
  Print test_reset1.

  Definition test_shift_reset1 x k : expr :=
    <{ <let x = shift k => k 1 in x + 1> }>.
  Print test_shift_reset1.

  Set Printing Notations.
  Unset Printing Coercions.
End TestProgramNotations.

Fixpoint expr_subst (y : var) (w : val) (e : expr) : expr :=
  let aux := expr_subst y w in
  let if_y_eq x e1 e2 := if var_eq_dec x y then e1 else e2 in
  match e with
  | expr_val v => expr_val v
  | expr_var x => if_y_eq x (expr_val w) e
  | expr_fun x e' => expr_fun x (if_y_eq x e' (aux e'))
  | expr_fix f x e' => expr_fix f x (if_y_eq f e' (if_y_eq x e' (aux e')))
  | expr_app e1 e2 => expr_app (aux e1) (aux e2)
  | expr_seq e1 e2 => expr_seq (aux e1) (aux e2)
  | expr_let x e1 e2 => expr_let x (aux e1) (if_y_eq x e2 (aux e2))
  | expr_if e1 e2 e3 => expr_if (aux e1) (aux e2) (aux e3)
  | expr_prim1 op e' => expr_prim1 op (aux e')
  | expr_prim2 op e1 e2 => expr_prim2 op (aux e1) (aux e2)
  | expr_shift k e' => expr_shift k (if_y_eq k e' (aux e'))
  | expr_reset e' => expr_reset (aux e')
  | expr_cont e' x k => expr_cont (aux e') x (if_y_eq x k (aux k))
  end.

Definition heap := Fmap.fmap loc val.
Definition empty_heap : heap := Fmap.empty.

Inductive eval_prim1_aux : heap -> prim1 -> val -> heap -> val -> Prop :=
| eval_prim1_aux_neg h b :
  eval_prim1_aux h prim1_neg (val_bool b) h (val_bool (neg b))
| eval_prim1_aux_ref h v p :
  ~ Fmap.indom h p ->
  eval_prim1_aux h prim1_ref v (Fmap.update h p v) (val_loc p)
| eval_prim1_aux_get h p v :
  Fmap.indom h p ->
  Fmap.read h p = v ->
  eval_prim1_aux h prim1_get (val_loc p) h v
| eval_prim1_aux_free h p :
  Fmap.indom h p ->
  eval_prim1_aux h prim1_free (val_loc p) (Fmap.remove h p) val_unit
| eval_prim1_aux_fst h v1 v2 :
  eval_prim1_aux h prim1_fst (val_pair v1 v2) h v1
| eval_prim1_aux_snd h v1 v2 :
  eval_prim1_aux h prim1_snd (val_pair v1 v2) h v2.

Inductive eval_prim2_aux : heap -> prim2 -> val -> val -> heap -> val -> Prop :=
(* arithmetic *)
| eval_prim2_aux_add h n1 n2 :
  eval_prim2_aux h prim2_add (val_int n1) (val_int n2) h (val_int (n1 + n2))
| eval_prim2_aux_sub h n1 n2 :
  eval_prim2_aux h prim2_sub (val_int n1) (val_int n2) h (val_int (n1 - n2))
| eval_prim2_aux_mul h n1 n2 :
  eval_prim2_aux h prim2_mul (val_int n1) (val_int n2) h (val_int (n1 * n2))
(* comparision *)
| eval_prim2_aux_eq h v1 v2 :
  eval_prim2_aux h prim2_eq v1 v2 h (val_bool (val_eqb v1 v2))
| eval_prim2_aux_lt h n1 n2 :
  eval_prim2_aux h prim2_lt (val_int n1) (val_int n2) h (val_bool (Z.ltb n1 n2))
| eval_prim2_aux_set h p v :
  Fmap.indom h p ->
  eval_prim2_aux h prim2_set (val_loc p) v (Fmap.update h p v) val_unit
(* string concatenation *)
| eval_prim2_aux_cat h s1 s2 :
  eval_prim2_aux h prim2_cat (val_str s1) (val_str s2) h (val_str (s1 ++ s2))
(* pair construction *)
| eval_prim2_aux_pair h v1 v2 :
  eval_prim2_aux h prim2_pair v1 v2 h (val_pair v1 v2).

Definition not_expr_val (e : expr) : Prop :=
  match e with | expr_val _ => False | _ => True end.

Inductive eval : heap -> expr -> heap -> val -> Prop :=
| eval_val h v :
  eval h (expr_val v) h v
| eval_fun h x e :
  eval h (expr_fun x e) h (val_fun x e)
| eval_fix h f x e :
  eval h (expr_fix f x e) h (val_fix f x e)
(* fun application *)
| eval_app_fun h1 h2 h3 h4 e1 x e e2 v r :
  eval h1 e1 h2 (val_fun x e) ->
  eval h2 e2 h3 v ->
  eval h3 (expr_subst x v e) h4 r ->
  eval h1 (expr_app e1 e2) h4 r
(* fix application *)
| eval_app_fix h1 h2 h3 h4 e1 f x e e2 v r :
  eval h1 e1 h2 (val_fix f x e) ->
  eval h2 e2 h3 v ->
  eval h3 (expr_subst x v (expr_subst f (val_fix f x e) e)) h4 r ->
  eval h1 (expr_app e1 e2) h4 r
(* seq *)
| eval_seq h1 h2 h3 e1 v e2 r :
  eval h1 e1 h2 v ->
  eval h2 e2 h3 r ->
  eval h1 (expr_seq e1 e2) h3 r
(* let binding *)
| eval_let h1 h2 h3 x e1 v e2 r :
  eval h1 e1 h2 v ->
  eval h2 (expr_subst x v e2) h3 r ->
  eval h1 (expr_let x e1 e2) h3 r
(* if then else *)
| eval_if_true h1 h2 h3 e1 e2 e3 r :
  eval h1 e1 h2 (val_bool true) ->
  eval h2 e2 h3 r ->
  eval h1 (expr_if e1 e2 e3) h3 r
| eval_if_false h1 h2 h3 e1 e2 e3 r :
  eval h1 e1 h2 (val_bool false) ->
  eval h2 e3 h3 r ->
  eval h1 (expr_if e1 e2 e3) h3 r
(* prim1 *)
| eval_prim1 h1 h2 h3 op e v r :
  eval h1 e h2 v ->
  eval_prim1_aux h2 op v h3 r ->
  eval h1 (expr_prim1 op e) h3 r
(* prim2 *)
| eval_prim2 h1 h2 h3 h4 op e1 v1 e2 v2 r :
  eval h1 e1 h2 v1 ->
  eval h2 e2 h3 v2 ->
  eval_prim2_aux h3 op v1 v2 h4 r ->
  eval h1 (expr_prim2 op e1 e2) h4 r
(* shift outside of reset cannot be evaluated *)
(* reset *)
| eval_reset h1 h2 e r :
  eval_cont_aux h1 e (var_of "x") (expr_var (var_of "x")) h2 r ->
  eval h1 (expr_reset e) h2 r
(* cont *)
| eval_cont h1 h2 e x k r :
  eval_cont_aux h1 e x k h2 r ->
  eval h1 (expr_cont e x k) h2 r
with eval_cont_aux : heap -> expr -> var -> expr -> heap -> val -> Prop :=
| eval_cont_aux_val h1 h2 v x k r :
  eval h1 (expr_subst x v k) h2 r ->
  eval_cont_aux h1 (expr_val v) x k h2 r
| eval_cont_aux_fun h1 h2 x e x' k r :
  eval h1 (expr_subst x' (val_fun x e) k) h2 r ->
  eval_cont_aux h1 (expr_fun x e) x' k h2 r
| eval_cont_aux_fix h1 h2 f x e x' k r :
  eval h1 (expr_subst x' (val_fix f x e) k) h2 r ->
  eval_cont_aux h1 (expr_fix f x e) x' k h2 r
(* cont of application *)
| eval_cont_aux_app_arg1 h1 h2 e1 e2 x k r :
  not_expr_val e1 ->
  eval_cont_aux h1 e1
    (var_of "f")
    (expr_cont (expr_app (expr_var (var_of "f")) e2) x k)
    h2 r ->
  eval_cont_aux h1 (expr_app e1 e2) x k h2 r
| eval_cont_aux_app_arg2 h1 h2 v1 e2 x k r :
  not_expr_val e2 ->
  eval_cont_aux h1 e2
    (var_of "x")
    (expr_cont (expr_app (expr_val v1) (expr_var (var_of "x"))) x k)
    h2 r ->
  eval_cont_aux h1 (expr_app (expr_val v1) e2) x k h2 r
| eval_cont_aux_app_fun h1 h2 x e v x' k r :
  eval_cont_aux h1 (expr_subst x v e) x' k h2 r ->
  eval_cont_aux h1 (expr_app (expr_val (val_fun x e)) (expr_val v)) x' k h2 r
| eval_cont_aux_app_fix h1 h2 f x e v x' k r :
  eval_cont_aux h1 (expr_subst x v (expr_subst f (val_fix f x e) e)) x' k h2 r ->
  eval_cont_aux h1 (expr_app (expr_val (val_fix f x e)) (expr_val v)) x' k h2 r
(* cont of seq *)
| eval_cont_aux_seq h1 h2 e1 e2 x k r :
  eval_cont_aux h1 e1 (var_of "_") (expr_cont e2 x k) h2 r ->
  eval_cont_aux h1 (expr_seq e1 e2) x k h2 r
(* cont of let binding *)
| eval_cont_aux_let h1 h2 x e1 e2 x' k r :
  eval_cont_aux h1 e1 x (expr_cont e2 x' k) h2 r ->
  eval_cont_aux h1 (expr_let x e1 e2) x' k h2 r
(* cont of if then else *)
| eval_cont_aux_if_arg h1 h2 e1 e2 e3 x k r :
  not_expr_val e1 ->
  eval_cont_aux h1 e1
    (var_of "b")
    (expr_cont (expr_if (expr_var (var_of "b")) e2 e3) x k)
    h2 r ->
  eval_cont_aux h1 (expr_if e1 e2 e3) x k h2 r
| eval_cont_aux_if_true h1 h2 e1 e2 x k r :
  eval_cont_aux h1 e1 x k h2 r ->
  eval_cont_aux h1 (expr_if (expr_val (val_bool true)) e1 e2) x k h2 r
| eval_cont_aux_if_false h1 h2 e1 e2 x k r :
  eval_cont_aux h1 e2 x k h2 r ->
  eval_cont_aux h1 (expr_if (expr_val (val_bool false)) e1 e2) x k h2 r
(* cont of prim1 *)
| eval_cont_aux_prim1_arg h1 h2 op e x k r :
  not_expr_val e ->
  eval_cont_aux h1 e
    (var_of "x")
    (expr_cont (expr_prim1 op (expr_var (var_of "x"))) x k)
    h2 r ->
  eval_cont_aux h1 (expr_prim1 op e) x k h2 r
| eval_cont_aux_prim1_val h1 h2 h3 op v v' x k r :
  eval_prim1_aux h1 op v h2 v' ->
  eval h2 (expr_subst x v' k) h3 r ->
  eval_cont_aux h1 (expr_prim1 op (expr_val v)) x k h3 r
(* cont of prim2 *)
| eval_cont_aux_prim2_arg1 h1 h2 op e1 e2 x k r :
  not_expr_val e1 ->
  eval_cont_aux h1 e1
    (var_of "x")
    (expr_cont (expr_prim2 op (expr_var (var_of "x")) e2) x k)
    h2 r ->
  eval_cont_aux h1 (expr_prim2 op e1 e2) x k h2 r
| eval_cont_aux_prim2_arg2 h1 h2 op v1 e2 x k r :
  not_expr_val e2 ->
  eval_cont_aux h1 e2
    (var_of "y")
    (expr_cont (expr_prim2 op (expr_val v1) (expr_var (var_of "y"))) x k)
    h2 r ->
  eval_cont_aux h1 (expr_prim2 op (expr_val v1) e2) x k h2 r
| eval_cont_aux_prim2_val h1 h2 h3 op v1 v2 v x k r :
  eval_prim2_aux h1 op v1 v2 h2 v ->
  eval h2 (expr_subst x v k) h3 r ->
  eval_cont_aux h1 (expr_prim2 op (expr_val v1) (expr_val v2)) x k h3 r
(* shift inside cont context *)
| eval_cont_aux_shift h1 h2 k e x k' r :
  eval_cont_aux h1
    (expr_subst k (val_fun x k') e)
    (var_of "x")
    (expr_var (var_of "x"))
    h2 r ->
  eval_cont_aux h1 (expr_shift k e) x k' h2 r
(* reset inside cont context *)
| eval_cont_aux_reset h1 h2 h3 e v x k r :
  eval_cont_aux h1 e (var_of "x") (expr_var (var_of "x")) h2 v ->
  eval h2 (expr_subst x v k) h3 r ->
  eval_cont_aux h1 (expr_reset e) x k h3 r
| eval_cont_aux_cont h1 h2 h3 e x k v x' k' r :
  eval_cont_aux h1 e x k h2 v ->
  eval h2 (expr_subst x' v k') h3 r ->
  eval_cont_aux h1 (expr_cont e x k) x' k' h3 r.

Module TestProgramSemantics.

  Import CoerceVal.
  Import CoerceExpr.
  Import ProgramNotations.

  Local Open Scope val_scope.
  Local Open Scope expr_scope.

  Local Create HintDb auto_eval_hints discriminated.

  Local Hint Resolve eval_val : auto_eval_hints.
  Local Hint Resolve eval_fun : auto_eval_hints.
  Local Hint Resolve eval_fix : auto_eval_hints.
  Local Hint Constructors eval_prim1_aux : auto_eval_hints.
  Local Hint Constructors eval_prim2_aux : auto_eval_hints.

  Ltac expr_subst := simpl expr_subst.
  Ltac auto_eval := auto with nocore auto_eval_hints; expr_subst.

  Definition one_plus_one : expr :=
    <{ let "f" "x" = {var_of "x"} + 1 in {var_of "f"} 1 }>.
  Print one_plus_one.

  Goal eval empty_heap one_plus_one empty_heap 2.
  Proof.
    unfold one_plus_one.
    eapply eval_let; auto_eval.
    eapply eval_app_fun; auto_eval.
    eapply eval_prim2; auto_eval.
  Qed.

  Definition factorial_3 : expr :=
    <{ let rec "f" "x" =
             if {var_of "x"} = 0 then
               1
             else
               {var_of "x"} * {var_of "f"} ({var_of "x"} - 1)
       in
       {var_of "f"} 3 }>.
  Print factorial_3.

  Goal eval empty_heap factorial_3 empty_heap 6.
  Proof.
    unfold factorial_3.
    eapply eval_let; auto_eval.
    eapply eval_app_fix; auto_eval.
    eapply eval_if_false.
    eapply eval_prim2; auto_eval.
    eapply eval_prim2; auto_eval.
    eapply eval_app_fix; auto_eval.
    eapply eval_prim2; auto_eval.
    ring_simplify (3 - 1).
    eapply eval_if_false.
    eapply eval_prim2; auto_eval.
    eapply eval_prim2; auto_eval.
    eapply eval_app_fix; auto_eval.
    eapply eval_prim2; auto_eval.
    ring_simplify (2 - 1).
    eapply eval_if_false.
    eapply eval_prim2; auto_eval.
    eapply eval_prim2; auto_eval.
    eapply eval_app_fix; auto_eval.
    eapply eval_prim2; auto_eval.
    ring_simplify (1 - 1).
    eapply eval_if_true.
    eapply eval_prim2; auto_eval.
    eapply eval_val.
    eapply eval_prim2_aux_mul.
  Qed.

  Definition sum_2_ref : expr :=
    <{ let "s" = ref 0 in
       let rec "f" "x" =
             if {var_of "x"} = 0 then
               ()
             else
               let "_" = {var_of "s"} := !{var_of "s"} + {var_of "x"} in
               {var_of "f"} ({var_of "x"} - 1)
       in
       {var_of "f"} 2; !{var_of "s"} }>.
  Print sum_2_ref.

  Goal eval empty_heap sum_2_ref (Fmap.single (loc_of 1) (val_int 3)) 3.
  Proof.
    unfold sum_2_ref.
    eapply eval_let; auto_eval.
    eapply eval_prim1; auto_eval.
    eapply (@eval_prim1_aux_ref _ _ (loc_of 1)).
    eapply fmap_not_indom_empty.
    rewrite -> Fmap.update_empty.
    eapply eval_let; auto_eval.
    eapply eval_seq.
    eapply eval_app_fix; auto_eval.
    eapply eval_if_false.
    eapply eval_prim2; auto_eval.
    eapply eval_let; auto_eval.
    eapply eval_prim2; auto_eval.
    eapply eval_prim2; auto_eval.
    eapply eval_prim1; auto_eval.
    eapply eval_prim1_aux_get.
    eapply Fmap.indom_single.
    eapply Fmap.read_single.
    ring_simplify (0 + 2).
    eapply eval_prim2_aux_set.
    eapply Fmap.indom_single.
    rewrite -> Fmap.update_eq_union_single.
    rewrite -> fmap_single_union_single_eq_single.
    eapply eval_app_fix; auto_eval.
    eapply eval_prim2; auto_eval.
    ring_simplify (2 - 1).
    eapply eval_if_false.
    eapply eval_prim2; auto_eval.
    eapply eval_let; auto_eval.
    eapply eval_prim2; auto_eval.
    eapply eval_prim2; auto_eval.
    eapply eval_prim1; auto_eval.
    eapply eval_prim1_aux_get.
    eapply Fmap.indom_single.
    eapply Fmap.read_single.
    ring_simplify (2 + 1).
    eapply eval_prim2_aux_set.
    eapply Fmap.indom_single.
    rewrite -> Fmap.update_eq_union_single.
    rewrite -> fmap_single_union_single_eq_single.
    eapply eval_app_fix; auto_eval.
    eapply eval_prim2; auto_eval.
    ring_simplify (1 - 1).
    eapply eval_if_true.
    eapply eval_prim2; auto_eval.
    eapply eval_val.
    eapply eval_prim1; auto_eval.
    eapply eval_prim1_aux_get.
    eapply Fmap.indom_single.
    eapply Fmap.read_single.
  Qed.

  Definition reset_trivial : expr :=
    <{ <1> }>.
  Print reset_trivial.

  Goal eval empty_heap reset_trivial empty_heap 1.
  Proof.
    unfold reset_trivial.
    eapply eval_reset.
    eapply eval_cont_aux_val. expr_subst.
    eapply eval_val.
  Qed.

  Definition app_inside_reset : expr :=
    <{ <(fun "x" => {var_of "x"} + 1) 1> }>.
  Print app_inside_reset.

  Goal eval empty_heap app_inside_reset empty_heap 2.
  Proof.
    unfold app_inside_reset.
    eapply eval_reset.
    eapply eval_cont_aux_app_arg1. exact I.
    eapply eval_cont_aux_fun. expr_subst.
    eapply eval_cont.
    eapply eval_cont_aux_app_fun. expr_subst.
    eapply eval_cont_aux_prim2_val; auto_eval.
    eapply eval_val.
  Qed.

  Definition let_inside_reset : expr :=
    <{ < let "x" = 1 in {var_of "x"} > }>.
  Print let_inside_reset.

  Goal eval empty_heap let_inside_reset empty_heap 1.
  Proof.
    unfold let_inside_reset.
    eapply eval_reset.
    eapply eval_cont_aux_let. expr_subst.
    eapply eval_cont_aux_val; expr_subst.
    eapply eval_cont.
    eapply eval_cont_aux_val. expr_subst.
    eapply eval_val.
  Qed.

  Definition prim1_inside_reset : expr :=
    <{ <not false> }>.
  Print prim1_inside_reset.

  Goal eval empty_heap prim1_inside_reset empty_heap true.
  Proof.
    unfold prim1_inside_reset.
    eapply eval_reset.
    eapply eval_cont_aux_prim1_val; auto_eval.
    eapply eval_val.
  Qed.

  Definition if_inside_reset : expr :=
    <{ <if 1 = 1 then 69 else 42> }>.
  Print if_inside_reset.

  Goal eval empty_heap if_inside_reset empty_heap 69.
  Proof.
    unfold if_inside_reset.
    eapply eval_reset.
    eapply eval_cont_aux_if_arg. exact I.
    eapply eval_cont_aux_prim2_val; auto_eval.
    eapply eval_cont.
    eapply eval_cont_aux_if_true.
    eapply eval_cont_aux_val. expr_subst.
    eapply eval_val.
  Qed.

  Definition shift_reset1 : expr :=
    <{ <1 + shift "k" => {var_of "k"} 1> }>.
  Print shift_reset1.

  Goal eval empty_heap shift_reset1 empty_heap 2.
  Proof.
    unfold shift_reset1.
    eapply eval_reset.
    eapply eval_cont_aux_prim2_arg2. exact I.
    eapply eval_cont_aux_shift. expr_subst.
    eapply eval_cont_aux_app_fun. expr_subst.
    eapply eval_cont_aux_cont; auto_eval.
    eapply eval_cont_aux_prim2_val; auto_eval.
    eapply eval_val.
    eapply eval_val.
  Qed.

  Definition shift_reset2 : expr :=
    <{ < 3 * shift "k" => {var_of "k"} > 23 }>.
  Print shift_reset2.

  Goal eval empty_heap shift_reset2 empty_heap 69.
  Proof.
    unfold shift_reset2.
    eapply eval_app_fun; auto_eval.
    eapply eval_reset.
    eapply eval_cont_aux_prim2_arg2. exact I.
    eapply eval_cont_aux_shift. expr_subst.
    eapply eval_cont_aux_val. expr_subst.
    eapply eval_val. expr_subst.
    eapply eval_cont.
    eapply eval_cont_aux_prim2_val; auto_eval.
    eapply eval_val.
  Qed.

  Definition state_monad : expr :=
    <{ let "get" "_" =
             shift "k" =>
             fun "s" => {var_of "k"} {var_of "s"} {var_of "s"}
       in
       let "tick" "_" =
             shift "k" =>
             fun "s" => {var_of "k"} () ({var_of "s"} + 1)
       in
       let "run_state" "t" =
             < let "r" = {var_of "t"} () in
               fun "_" => {var_of "r"} > 0
       in
       let "thunk" "_" = {var_of "tick"} (); {var_of "get"} () in
       {var_of "run_state"} {var_of "thunk"} }>.
  Print state_monad.

  Goal eval empty_heap state_monad empty_heap 1.
  Proof.
    unfold state_monad.
    eapply eval_let; auto_eval.
    eapply eval_let; auto_eval.
    eapply eval_let; auto_eval.
    eapply eval_let; auto_eval.
    eapply eval_app_fun; auto_eval.
    eapply eval_app_fun; auto_eval.
    eapply eval_reset.
    eapply eval_cont_aux_let.
    eapply eval_cont_aux_app_fun. expr_subst.
    eapply eval_cont_aux_seq.
    eapply eval_cont_aux_app_fun. expr_subst.
    eapply eval_cont_aux_shift. expr_subst.
    eapply eval_cont_aux_fun. expr_subst.
    eapply eval_val. expr_subst.
    eapply eval_app_fun; auto_eval.
    eapply eval_app_fun; auto_eval.
    eapply eval_cont.
    eapply eval_cont_aux_app_fun. expr_subst.
    eapply eval_cont_aux_shift. expr_subst.
    eapply eval_cont_aux_fun. expr_subst.
    eapply eval_val.
    eapply eval_prim2; auto_eval. expr_subst.
    eapply eval_app_fun; auto_eval.
    eapply eval_app_fun; auto_eval.
    eapply eval_cont.
    eapply eval_cont_aux_fun. expr_subst.
    eapply eval_val. expr_subst.
    eapply eval_val.
  Qed.

  Definition hello_printf : expr :=
    <{ <(shift "k" => {var_of "k"}) ^ (shift "k" => {var_of "k"}) ^ "!"> "a" "b" }>.
  Print hello_printf.

  Goal eval empty_heap hello_printf empty_heap "ab!".
  Proof.
    unfold hello_printf.
    eapply eval_app_fun; auto_eval.
    eapply eval_app_fun; auto_eval.
    eapply eval_reset.
    eapply eval_cont_aux_prim2_arg1. exact I.
    eapply eval_cont_aux_shift. expr_subst.
    eapply eval_cont_aux_val. expr_subst.
    eapply eval_val. expr_subst.
    eapply eval_cont.
    eapply eval_cont_aux_prim2_arg2. exact I.
    eapply eval_cont_aux_prim2_arg1. exact I.
    eapply eval_cont_aux_shift. expr_subst.
    eapply eval_cont_aux_val. expr_subst.
    eapply eval_val. expr_subst.
    eapply eval_cont.
    eapply eval_cont_aux_prim2_val; auto_eval.
    eapply eval_cont.
    eapply eval_cont_aux_prim2_val; auto_eval.
    eapply eval_val.
  Qed.

  Definition either : expr :=
    <{ let "either" "a" "b" =
             shift "k" =>
             {var_of "k"} {var_of "a"}; {var_of "k"} {var_of "b"}
       in
       let "r" = ref 0 in
       let "_" = < let "x" = {var_of "either"} 60 9 in
                   {var_of "r"} := !{var_of "r"} + {var_of "x"} >
       in
       !{var_of "r"} }>.
  Print either.

  Goal eval empty_heap either (Fmap.single (loc_of 10) (val_int 69)) 69.
  Proof.
    unfold either.
    eapply eval_let; auto_eval.
    eapply eval_let; auto_eval.
    eapply eval_prim1; auto_eval.
    eapply (@eval_prim1_aux_ref _ _ (loc_of 10)).
    eapply fmap_not_indom_empty.
    rewrite -> Fmap.update_empty.
    eapply eval_let; auto_eval.
    eapply eval_reset.
    eapply eval_cont_aux_let.
    eapply eval_cont_aux_app_arg1. exact I.
    eapply eval_cont_aux_app_fun. expr_subst.
    eapply eval_cont_aux_fun. expr_subst.
    eapply eval_cont.
    eapply eval_cont_aux_app_fun. expr_subst.
    eapply eval_cont_aux_shift. expr_subst.
    eapply eval_cont_aux_seq.
    eapply eval_cont_aux_app_fun. expr_subst.
    eapply eval_cont_aux_cont; auto_eval.
    eapply eval_cont_aux_prim2_arg2. exact I.
    eapply eval_cont_aux_prim2_arg1. exact I.
    eapply eval_cont_aux_prim1_val.
    eapply eval_prim1_aux_get.
    eapply Fmap.indom_single.
    eapply Fmap.read_single. expr_subst.
    eapply eval_cont.
    eapply eval_cont_aux_prim2_val; auto_eval.
    ring_simplify (0 + 60).
    eapply eval_cont.
    eapply eval_cont_aux_prim2_val; auto_eval.
    eapply eval_prim2_aux_set.
    eapply Fmap.indom_single.
    rewrite -> Fmap.update_eq_union_single.
    rewrite -> fmap_single_union_single_eq_single.
    eapply eval_val.
    eapply eval_cont.
    eapply eval_cont_aux_app_fun. expr_subst.
    eapply eval_cont_aux_cont; auto_eval.
    eapply eval_cont_aux_prim2_arg2. exact I.
    eapply eval_cont_aux_prim2_arg1. exact I.
    eapply eval_cont_aux_prim1_val; auto_eval.
    eapply eval_prim1_aux_get.
    eapply Fmap.indom_single.
    eapply Fmap.read_single.
    eapply eval_cont.
    eapply eval_cont_aux_prim2_val; auto_eval.
    ring_simplify (60 + 9).
    eapply eval_cont.
    eapply eval_cont_aux_prim2_val; auto_eval.
    eapply eval_prim2_aux_set.
    eapply Fmap.indom_single.
    rewrite -> Fmap.update_eq_union_single.
    rewrite -> fmap_single_union_single_eq_single.
    eapply eval_val.
    eapply eval_val.
    eapply eval_prim1; auto_eval.
    eapply eval_prim1_aux_get.
    eapply Fmap.indom_single.
    eapply Fmap.read_single.
  Qed.

  Definition append_with_shift : expr :=
    <{ let rec "append_aux" "xs" =
             if {var_of "xs"} = null then
               shift "k" => {var_of "k"}
             else
               let "x" = fst {var_of "xs"} in
               let "xs'" = snd {var_of "xs"} in
               {var_of "x"}, {var_of "append_aux"} {var_of "xs'"}
       in
       let "append" "xs" "ys" =
             < {var_of "append_aux"} {var_of "xs"} > {var_of "ys"}
       in
       {var_of "append"} (1, (2, null)) (3, (4, null)) }>.
  Print append_with_shift.

  Goal eval empty_heap append_with_shift empty_heap
    (val_pair (val_int 1)
       (val_pair (val_int 2)
          (val_pair (val_int 3)
             (val_pair (val_int 4)
                (val_loc null))))).
  Proof.
    unfold append_with_shift.
    eapply eval_let; auto_eval.
    eapply eval_let; auto_eval.
    eapply eval_app_fun; auto_eval.
    eapply eval_app_fun; auto_eval.
    eapply eval_prim2; auto_eval.
    eapply eval_prim2; auto_eval.
    eapply eval_fun.
    eapply eval_prim2; auto_eval.
    eapply eval_prim2; auto_eval. expr_subst.
    eapply eval_app_fun; auto_eval.
    eapply eval_reset.
    eapply eval_cont_aux_app_fix. expr_subst.
    eapply eval_cont_aux_if_arg. exact I.
    eapply eval_cont_aux_prim2_val; auto_eval.
    eapply eval_cont.
    eapply eval_cont_aux_if_false.
    eapply eval_cont_aux_let.
    eapply eval_cont_aux_prim1_val; auto_eval.
    eapply eval_cont.
    eapply eval_cont_aux_let.
    eapply eval_cont_aux_prim1_val; auto_eval.
    eapply eval_cont.
    eapply eval_cont_aux_prim2_arg2. exact I.
    eapply eval_cont_aux_app_fix. expr_subst.
    eapply eval_cont_aux_if_arg. exact I.
    eapply eval_cont_aux_prim2_val; auto_eval.
    eapply eval_cont.
    eapply eval_cont_aux_if_false.
    eapply eval_cont_aux_let.
    eapply eval_cont_aux_prim1_val; auto_eval.
    eapply eval_cont.
    eapply eval_cont_aux_let.
    eapply eval_cont_aux_prim1_val; auto_eval.
    eapply eval_cont.
    eapply eval_cont_aux_prim2_arg2. exact I.
    eapply eval_cont_aux_app_fix. expr_subst.
    eapply eval_cont_aux_if_arg. exact I.
    eapply eval_cont_aux_prim2_val; auto_eval.
    eapply eval_cont.
    eapply eval_cont_aux_if_true.
    eapply eval_cont_aux_shift. expr_subst.
    eapply eval_cont_aux_val. expr_subst.
    eapply eval_val. expr_subst.
    eapply eval_cont.
    eapply eval_cont_aux_prim2_val; auto_eval.
    eapply eval_cont.
    eapply eval_cont_aux_prim2_val; auto_eval.
    eapply eval_val.
  Qed.

End TestProgramSemantics.

Module ClosedProgram.

  Import List.ListNotations.
  Local Open Scope list_scope.

  Definition ctx := list var.

  Fixpoint closed_val (v : val) : Prop :=
    match v with
    | val_fun x e => closed_expr_under [x] e
    | val_fix f x e => closed_expr_under [f; x] e
    | val_pair v1 v2 => closed_val v1 /\ closed_val v2
    | _ => True
    end with
  closed_expr_under (c : ctx) (e : expr) : Prop :=
    match e with
    | expr_val v => closed_val v
    | expr_var x => List.In x c
    | expr_fun x e' => closed_expr_under (x :: c) e'
    | expr_fix f x e' => closed_expr_under (f :: x :: c) e'
    | expr_app e1 e2 => closed_expr_under c e1 /\ closed_expr_under c e2
    | expr_seq e1 e2 => closed_expr_under c e1 /\ closed_expr_under c e2
    | expr_let x e1 e2 => closed_expr_under c e1 /\ closed_expr_under (x :: c) e2
    | expr_if e1 e2 e3 => closed_expr_under c e1 /\ closed_expr_under c e2 /\ closed_expr_under c e3
    | expr_prim1 _ e' => closed_expr_under c e'
    | expr_prim2 _ e1 e2 => closed_expr_under c e1 /\ closed_expr_under c e2
    | expr_shift k e' => closed_expr_under (k :: c) e'
    | expr_reset e' => closed_expr_under c e'
    | expr_cont e' x k => closed_expr_under c e' /\ closed_expr_under (x :: c) k
    end.

  Definition closed_expr := closed_expr_under [].
  Definition closed_cont (x : var) := closed_expr_under [x].
  Definition closed_heap (h : heap) := forall (p : loc), Fmap.indom h p -> closed_val (Fmap.read h p).

  Lemma expr_subst_with_nonfree_var :
    forall (c : ctx)
           (e : expr)
           (x : var)
           (v : val),
      closed_expr_under c e ->
      ~ List.In x c ->
      expr_subst x v e = e.
  Proof.
    intros c e x v.
    revert c.
    induction e; simpl; intros c H_expr H_not_in.
    - reflexivity.
    - destruct var_eq_dec.
      + congruence.
      + reflexivity.
    - destruct var_eq_dec.
      + reflexivity.
      + rewrite -> (IHe _ H_expr) by now rewrite -> List.not_in_cons.
        reflexivity.
    - destruct var_eq_dec.
      + reflexivity.
      + destruct var_eq_dec.
        * reflexivity.
        * rewrite -> (IHe _ H_expr) by now rewrite ->2 List.not_in_cons.
          reflexivity.
    - destruct H_expr as [H_expr1 H_expr2].
      rewrite -> (IHe1 _ H_expr1 H_not_in).
      rewrite -> (IHe2 _ H_expr2 H_not_in).
      reflexivity.
    - destruct H_expr as [H_expr1 H_expr2].
      rewrite -> (IHe1 _ H_expr1 H_not_in).
      rewrite -> (IHe2 _ H_expr2 H_not_in).
      reflexivity.
    - destruct H_expr as [H_expr1 H_expr2].
      rewrite -> (IHe1 _ H_expr1 H_not_in).
      destruct var_eq_dec.
      + reflexivity.
      + rewrite -> (IHe2 _ H_expr2) by now rewrite -> List.not_in_cons.
        reflexivity.
    - destruct H_expr as [H_expr1 [H_expr2 H_expr3]].
      rewrite -> (IHe1 _ H_expr1 H_not_in).
      rewrite -> (IHe2 _ H_expr2 H_not_in).
      rewrite -> (IHe3 _ H_expr3 H_not_in).
      reflexivity.
    - rewrite -> (IHe _ H_expr H_not_in).
      reflexivity.
    - destruct H_expr as [H_expr1 H_expr2].
      rewrite -> (IHe1 _ H_expr1 H_not_in).
      rewrite -> (IHe2 _ H_expr2 H_not_in).
      reflexivity.
    - destruct var_eq_dec.
      + reflexivity.
      + rewrite -> (IHe _ H_expr) by now rewrite -> List.not_in_cons.
        reflexivity.
    - rewrite -> (IHe _ H_expr H_not_in).
      reflexivity.
    - destruct H_expr as [H_expr1 H_expr2].
      rewrite -> (IHe1 _ H_expr1 H_not_in).
      destruct var_eq_dec.
      + reflexivity.
      + rewrite -> (IHe2 _ H_expr2) by now rewrite -> List.not_in_cons.
        reflexivity.
  Qed.

  Corollary expr_subst_on_closed_expr :
    forall (e : expr)
           (x : var)
           (v : val),
      closed_expr e ->
      expr_subst x v e = e.
  Proof.
    eauto using expr_subst_with_nonfree_var, List.in_nil.
  Qed.

  Corollary expr_subst_with_closed_cont :
    forall (x : var)
           (k e : expr)
           (x' : var)
           (v : val),
      closed_cont x k ->
      expr_subst x' v (expr_cont e x k) = expr_cont (expr_subst x' v e) x k.
  Proof.
    introv H_cont. simpl.
    destruct var_eq_dec.
    + reflexivity.
    + rewrite -> (expr_subst_with_nonfree_var _ _ _ _ H_cont) by (simpl; tauto).
      reflexivity.
  Qed.

  Lemma ctx_incl_cons_cons :
    forall (x : var)
           (c c' : ctx),
      List.incl c c' ->
      List.incl (x :: c) (x :: c').
  Proof.
    unfold List.incl. simpl. intuition auto.
  Qed.

  Lemma weakening_preserves_closedness :
    forall (c : ctx)
           (e : expr)
           (c' : ctx),
      closed_expr_under c e ->
      List.incl c c' ->
      closed_expr_under c' e.
  Proof.
    intros c e.
    revert c.
    induction e; simpl; intuition eauto using ctx_incl_cons_cons.
  Qed.

  Ltac ctx_incl := unfold List.incl; simpl; tauto.
  Ltac revert_weakening := eapply weakening_preserves_closedness; [eassumption | ctx_incl].
  Ltac ensure_closed := unfold closed_expr, closed_cont;
                        simpl closed_expr_under;
                        repeat match goal with
                          | [ _ : _ |- _ /\ _ ] => split
                          | [ _ : _ |- closed_val _ ] => assumption
                          | [ _ : _ |- closed_expr_under _ _ ] => assumption || revert_weakening
                          | [ _ : _ |- _ = _ \/ False ] => left; reflexivity
                          end.

  Lemma expr_subst_preserves_closedness :
    forall (x : var)
           (c : ctx)
           (e : expr)
           (v : val),
      closed_expr_under (x :: c) e ->
      closed_val v ->
      closed_expr_under c (expr_subst x v e).
  Proof.
    introv H_expr H_val.
    revert c H_expr.
    induction e; simpl; intros c H_expr.
    - assumption.
    - destruct var_eq_dec; simpl.
      + assumption.
      + intuition congruence.
    - destruct var_eq_dec; [subst | apply IHe]; revert_weakening.
    - destruct var_eq_dec; [subst |].
      + revert_weakening.
      + destruct var_eq_dec; [subst | apply IHe]; revert_weakening.
    - intuition auto.
    - intuition auto.
    - intuition auto.
      destruct var_eq_dec; [subst | apply IHe2]; revert_weakening.
    - intuition auto.
    - intuition auto.
    - intuition auto.
    - destruct var_eq_dec; [subst | apply IHe]; revert_weakening.
    - intuition auto.
    - intuition auto.
      destruct var_eq_dec; [subst | apply IHe2]; revert_weakening.
  Qed.

  Ltac revert_expr_subst := apply expr_subst_preserves_closedness; try assumption.

  Lemma eval_prim1_aux_preserves_closedness :
    forall (h1 : heap)
           (op : prim1)
           (v : val)
           (h2 : heap)
           (r : val),
      eval_prim1_aux h1 op v h2 r ->
      closed_heap h1 ->
      closed_val v ->
      closed_heap h2 /\ closed_val r.
  Proof.
    unfold closed_heap.
    introv H_eval_prim1_aux H_heap H_val.
    inverts H_eval_prim1_aux as; simpl in *.
    - intuition auto.
    - intros _. split; [| exact I].
      intros p' H_indom.
      destruct (loc_eq_dec p p') as [H_eq | H_neq].
      + rewrite -> H_eq.
        rewrite -> fmap_read_update.
        exact H_val.
      + rewrite -> Fmap.indom_update_eq in H_indom.
        rewrite -> fmap_neq_read_update by exact H_neq.
        destruct H_indom as [H_eq | H_indom].
        * congruence.
        * exact (H_heap p' H_indom).
    - intuition auto.
    - intros _. split; [| exact I].
      intros p' H_indom.
      rewrite -> Fmap.indom_remove_eq in H_indom.
      destruct H_indom as [H_neq H_indom].
      rewrite -> fmap_neq_read_remove by exact H_neq.
      exact (H_heap p' H_indom).
    - intuition auto.
    - intuition auto.
  Qed.

  Lemma eval_prim2_aux_preserves_closedness :
    forall (h1 : heap)
           (op : prim2)
           (v1 v2 : val)
           (h2 : heap)
           (r : val),
      eval_prim2_aux h1 op v1 v2 h2 r ->
      closed_heap h1 ->
      closed_val v1 ->
      closed_val v2 ->
      closed_heap h2 /\ closed_val r.
  Proof.
    unfold closed_heap.
    introv H_eval_prim2_aux H_heap H_val1 H_val2.
    inverts H_eval_prim2_aux as; simpl in *.
    - intuition auto.
    - intuition auto.
    - intuition auto.
    - intuition auto.
    - intuition auto.
    - intros _. split; [| exact I].
      intros p' H_indom.
      destruct (loc_eq_dec p p') as [H_eq | H_neq].
      + rewrite -> H_eq.
        rewrite -> fmap_read_update.
        exact H_val2.
      + rewrite -> Fmap.indom_update_eq in H_indom.
        rewrite -> fmap_neq_read_update by exact H_neq.
        destruct H_indom as [H_eq | H_indom].
        * congruence.
        * exact (H_heap p' H_indom).
    - intuition auto.
    - intuition auto.
  Qed.

  Theorem eval_preserves_closedness :
    (forall (h1 : heap)
            (e : expr)
            (h2 : heap)
            (r : val),
        eval h1 e h2 r ->
        closed_heap h1 ->
        closed_expr e ->
        closed_heap h2 /\ closed_val r)
    with eval_cont_aux_preserves_closedness :
      (forall (h1 : heap)
              (e : expr)
              (x : var)
              (k : expr)
              (h2 : heap)
              (r : val),
          eval_cont_aux h1 e x k h2 r ->
          closed_heap h1 ->
          closed_expr e ->
          closed_cont x k ->
          closed_heap h2 /\ closed_val r).
  Proof.
    {
      unfold closed_expr, closed_cont in *.
      introv H_eval H_heap1 H_expr.
      induction H_eval; simpl in *.
      - tauto.
      - tauto.
      - tauto.
      - destruct H_expr as [H_expr1 H_expr2].
        specialize (IHH_eval1 H_heap1 H_expr1) as [H_heap2 H_val1].
        specialize (IHH_eval2 H_heap2 H_expr2) as [H_heap3 H_val2].
        apply IHH_eval3; try assumption. revert_expr_subst.
      - destruct H_expr as [H_expr1 H_expr2].
        specialize (IHH_eval1 H_heap1 H_expr1) as [H_heap2 H_val1].
        specialize (IHH_eval2 H_heap2 H_expr2) as [H_heap3 H_val2].
        apply IHH_eval3; try assumption. revert_expr_subst. revert_expr_subst.
      - intuition auto.
      - destruct H_expr as [H_expr1 H_expr2].
        specialize (IHH_eval1 H_heap1 H_expr1) as [H_heap2 H_val1].
        apply IHH_eval2; try assumption. revert_expr_subst.
      - intuition auto.
      - intuition auto.
      - specialize (IHH_eval H_heap1 H_expr) as [H_heap2 H_val].
        eapply eval_prim1_aux_preserves_closedness; eassumption.
      - destruct H_expr as [H_expr1 H_expr2].
        specialize (IHH_eval1 H_heap1 H_expr1) as [H_heap2 H_val1].
        specialize (IHH_eval2 H_heap2 H_expr2) as [H_heap3 H_val2].
        eapply eval_prim2_aux_preserves_closedness; eassumption.
      - eapply eval_cont_aux_preserves_closedness; eassumption || ensure_closed.
      - destruct H_expr as [H_expr1 H_expr2].
        eapply eval_cont_aux_preserves_closedness; eassumption.
    }
    {
      unfold closed_expr, closed_cont in *.
      introv H_eval_cont_aux H_heap1 H_expr H_cont.
      induction H_eval_cont_aux; simpl in *.
      - eapply eval_preserves_closedness; try eassumption. revert_expr_subst.
      - eapply eval_preserves_closedness; try eassumption. revert_expr_subst.
      - eapply eval_preserves_closedness; try eassumption. revert_expr_subst.
      - destruct H_expr as [H_expr1 H_expr2]. apply IHH_eval_cont_aux; assumption || ensure_closed.
      - destruct H_expr as [H_expr1 H_expr2]. apply IHH_eval_cont_aux; assumption || ensure_closed.
      - destruct H_expr as [H_expr1 H_expr2]. apply IHH_eval_cont_aux; try assumption. revert_expr_subst.
      - destruct H_expr as [H_expr1 H_expr2]. apply IHH_eval_cont_aux; try assumption. revert_expr_subst. revert_expr_subst.
      - destruct H_expr as [H_expr1 H_expr2]. apply IHH_eval_cont_aux; assumption || ensure_closed.
      - destruct H_expr as [H_expr1 H_expr2]. apply IHH_eval_cont_aux; assumption || ensure_closed.
      - destruct H_expr as [H_expr1 [H_expr2 H_expr3]]. apply IHH_eval_cont_aux; assumption || ensure_closed.
      - destruct H_expr as [_ [H_expr1 H_expr2]]. apply IHH_eval_cont_aux; assumption.
      - destruct H_expr as [_ [H_expr1 H_expr2]]. apply IHH_eval_cont_aux; assumption.
      - eapply IHH_eval_cont_aux; assumption || ensure_closed.
      - destruct (eval_prim1_aux_preserves_closedness H H_heap1 H_expr) as [H_heap2 H_val].
        eapply eval_preserves_closedness; try eassumption. revert_expr_subst.
      - destruct H_expr as [H_expr1 H_expr2]. apply IHH_eval_cont_aux; assumption || ensure_closed.
      - destruct H_expr as [H_expr1 H_expr2]. apply IHH_eval_cont_aux; assumption || ensure_closed.
      - destruct H_expr as [H_expr1 H_expr2].
        destruct (eval_prim2_aux_preserves_closedness H H_heap1 H_expr1 H_expr2) as [H_heap2 H_val].
        eapply eval_preserves_closedness; try eassumption. revert_expr_subst.
      - apply IHH_eval_cont_aux; [assumption | revert_expr_subst | ensure_closed].
      - specialize (IHH_eval_cont_aux H_heap1 H_expr ltac:(ensure_closed)) as [H_heap2 H_val].
        eapply eval_preserves_closedness; try eassumption. revert_expr_subst.
      - destruct H_expr as [H_expr1 H_expr2].
        specialize (IHH_eval_cont_aux H_heap1 H_expr1 H_expr2) as [H_heap2 H_val].
        eapply eval_preserves_closedness; try eassumption. revert_expr_subst.
    }
  Qed.

End ClosedProgram.

Module ProgramDeterminism.

  Axiom eval_prim1_aux_is_deterministic :
    forall (h1 : heap)
           (op : prim1)
           (v : val)
           (h2 : heap)
           (r : val),
      eval_prim1_aux h1 op v h2 r ->
      forall (h2' : heap)
             (r' : val),
        eval_prim1_aux h1 op v h2' r' ->
        h2 = h2' /\ r = r'.

  Lemma eval_prim2_aux_is_deterministic :
    forall (h1 : heap)
           (op : prim2)
           (v1 v2 : val)
           (h2 : heap)
           (r : val),
      eval_prim2_aux h1 op v1 v2 h2 r ->
      forall (h2' : heap)
             (r' : val),
        eval_prim2_aux h1 op v1 v2 h2' r' ->
        h2 = h2' /\ r = r'.
  Proof.
    introv H_eval H_eval'.
    now inverts H_eval; inverts H_eval'.
  Qed.

  Theorem eval_is_deterministic :
    (forall (h1 : heap)
            (e : expr)
            (h2 : heap)
            (r : val),
        eval h1 e h2 r ->
        forall (h2' : heap)
               (r' : val),
          eval h1 e h2' r' ->
          h2 = h2' /\ r = r')
    with eval_cont_aux_is_deterministic :
      (forall (h1 : heap)
              (e : expr)
              (x : var)
              (k : expr)
              (h2 : heap)
              (r : val),
          eval_cont_aux h1 e x k h2 r ->
          forall (h2' : heap)
                 (r' : val),
            eval_cont_aux h1 e x k h2' r' ->
            h2 = h2' /\ r = r').
  Proof.
    {
      introv H_eval.
      induction H_eval; introv H_eval'.
      - inverts H_eval' as. tauto.
      - inverts H_eval' as. tauto.
      - inverts H_eval' as. tauto.
      - inverts H_eval' as.
        + introv H_eval'1 H_eval'2 H_eval'3.
          apply IHH_eval1 in H_eval'1 as [? H_eq]. subst. inverts H_eq as.
          apply IHH_eval2 in H_eval'2 as []. subst.
          apply IHH_eval3 in H_eval'3 as []. tauto.
        + introv H_eval'1.
          apply IHH_eval1 in H_eval'1 as []. discriminate.
      - inverts H_eval' as.
        + introv H_eval'1.
          apply IHH_eval1 in H_eval'1 as []. discriminate.
        + introv H_eval'1 H_eval'2 H_eval'3.
          apply IHH_eval1 in H_eval'1 as [? H_eq]. subst. inverts H_eq as.
          apply IHH_eval2 in H_eval'2 as []. subst.
          apply IHH_eval3 in H_eval'3 as []. tauto.
      - inverts H_eval' as.
        introv H_eval'1 H_eval'2.
        apply IHH_eval1 in H_eval'1 as []. subst.
        apply IHH_eval2 in H_eval'2 as []. tauto.
      - inverts H_eval' as.
        introv H_eval'1 H_eval'2.
        apply IHH_eval1 in H_eval'1 as []. subst.
        apply IHH_eval2 in H_eval'2 as []. tauto.
      - inverts H_eval' as.
        + introv H_eval'1 H_eval'2.
          apply IHH_eval1 in H_eval'1 as []. subst.
          apply IHH_eval2 in H_eval'2 as []. tauto.
        + introv H_eval'1.
          apply IHH_eval1 in H_eval'1 as []. discriminate.
      - inverts H_eval' as.
        + introv H_eval'1.
          apply IHH_eval1 in H_eval'1 as []. discriminate.
        + introv H_eval'1 H_eval'2.
          apply IHH_eval1 in H_eval'1 as []. subst.
          apply IHH_eval2 in H_eval'2 as []. tauto.
      - inverts H_eval' as.
        introv H_eval' H_prim1'.
        apply IHH_eval in H_eval' as []. subst.
        eauto using eval_prim1_aux_is_deterministic.
      - inverts H_eval' as.
        introv H_eval'1 H_eval'2 H_prim2'.
        apply IHH_eval1 in H_eval'1 as []. subst.
        apply IHH_eval2 in H_eval'2 as []. subst.
        eauto using eval_prim2_aux_is_deterministic.
      - inverts H_eval'. eauto.
      - inverts H_eval'. eauto.
    }
    {
      introv H_eval_cont_aux.
      induction H_eval_cont_aux; introv H_eval_cont_aux'.
      - inverts H_eval_cont_aux' as. eauto.
      - inverts H_eval_cont_aux' as. eauto.
      - inverts H_eval_cont_aux' as. eauto.
      - inverts H_eval_cont_aux' as; contradiction || auto.
      - inverts H_eval_cont_aux' as; contradiction || auto.
      - inverts H_eval_cont_aux' as; contradiction || auto.
      - inverts H_eval_cont_aux' as; contradiction || auto.
      - inverts H_eval_cont_aux' as; contradiction || auto.
      - inverts H_eval_cont_aux' as; contradiction || auto.
      - inverts H_eval_cont_aux' as; contradiction || auto.
      - inverts H_eval_cont_aux' as; contradiction || auto.
      - inverts H_eval_cont_aux' as; contradiction || auto.
      - inverts H_eval_cont_aux' as; contradiction || auto.
      - inverts H_eval_cont_aux' as.
        + contradiction.
        + introv H_prim1' H_eval_cont_aux'.
          destruct (eval_prim1_aux_is_deterministic H H_prim1'). subst. eauto.
      - inverts H_eval_cont_aux' as; contradiction || auto.
      - inverts H_eval_cont_aux' as; contradiction || auto.
      - inverts H_eval_cont_aux' as.
        + contradiction.
        + contradiction.
        + introv H_prim2' H_eval_cont_aux'.
          destruct (eval_prim2_aux_is_deterministic H H_prim2'). subst. eauto.
      - inverts H_eval_cont_aux' as; contradiction || auto.
      - inverts H_eval_cont_aux' as.
        introv H_eval_cont_aux'.
        apply IHH_eval_cont_aux in H_eval_cont_aux' as []. subst. eauto.
      - inverts H_eval_cont_aux' as.
        introv H_eval_cont_aux'.
        apply IHH_eval_cont_aux in H_eval_cont_aux' as []. subst. eauto.
    }
  Qed.

  Import ClosedProgram.

  Theorem eval_cont_aux_is_cont_of_eval :
    forall (h1 : heap)
           (e : expr)
           (h2 : heap)
           (v : val),
      closed_heap h1 ->
      closed_expr e ->
      eval h1 e h2 v ->
      forall (h3 : heap)
             (x : var)
             (k : expr)
             (r : val),
        closed_cont x k ->
        eval_cont_aux h1 e x k h3 r ->
        eval h2 (expr_subst x v k) h3 r.
  Proof.
    introv H_heap1 H_expr H_eval H_cont.
    revert x k H_cont.
    induction H_eval; introv H_cont H_eval_cont_aux; cbn in *.
    - inverts H_eval_cont_aux as. tauto.
    - inverts H_eval_cont_aux as. tauto.
    - inverts H_eval_cont_aux as. tauto.
    - destruct H_expr as [H_expr1 H_expr2].
      forwards [H_heap2 H_val1]: eval_preserves_closedness H_eval1 H_heap1 H_expr1.
      forwards [H_heap3 H_val2]: eval_preserves_closedness H_eval2 H_heap2 H_expr2.
      forwards H_expr3: expr_subst_preserves_closedness H_val1 H_val2.
      specialize (IHH_eval1 H_heap1 H_expr1).
      specialize (IHH_eval2 H_heap2 H_expr2).
      specialize (IHH_eval3 H_heap3 H_expr3).
      inverts H_eval_cont_aux as.
      + introv _ H_eval_cont_aux.
        apply IHH_eval1 in H_eval_cont_aux; [| ensure_closed].
        rewrite -> expr_subst_with_closed_cont in H_eval_cont_aux by ensure_closed. simpl in H_eval_cont_aux.
        rewrite -> expr_subst_on_closed_expr in H_eval_cont_aux by ensure_closed.
        inverts H_eval_cont_aux as H_eval_cont_aux.
        inverts H_eval_cont_aux as.
        * contradiction.
        * introv _ H_eval_cont_aux.
          apply IHH_eval2 in H_eval_cont_aux; [| ensure_closed].
          rewrite -> expr_subst_with_closed_cont in H_eval_cont_aux by ensure_closed. simpl in H_eval_cont_aux.
          inverts H_eval_cont_aux as H_eval_cont_aux.
          inverts H_eval_cont_aux as.
          { contradiction. }
          { contradiction. }
          { auto. }
        * inverts H_eval2 as. auto.
      + inverts H_eval1 as.
        introv _ H_eval_cont_aux.
        apply IHH_eval2 in H_eval_cont_aux; [| ensure_closed].
        rewrite -> expr_subst_with_closed_cont in H_eval_cont_aux by ensure_closed. simpl in H_eval_cont_aux.
        inverts H_eval_cont_aux as H_eval_cont_aux.
        inverts H_eval_cont_aux as.
        { contradiction. }
        { contradiction. }
        { auto. }
      + inverts H_eval1 as.
        inverts H_eval2 as. auto.
      + inverts H_eval1 as.
    - destruct H_expr as [H_expr1 H_expr2].
      forwards [H_heap2 H_val1]: eval_preserves_closedness H_eval1 H_heap1 H_expr1.
      forwards [H_heap3 H_val2]: eval_preserves_closedness H_eval2 H_heap2 H_expr2.
      forwards H_expr3: expr_subst_preserves_closedness ltac:(applys expr_subst_preserves_closedness H_val1 H_val1) H_val2.
      specialize (IHH_eval1 H_heap1 H_expr1).
      specialize (IHH_eval2 H_heap2 H_expr2).
      specialize (IHH_eval3 H_heap3 H_expr3).
      inverts H_eval_cont_aux as.
      + introv _ H_eval_cont_aux.
        apply IHH_eval1 in H_eval_cont_aux; [| ensure_closed].
        rewrite -> expr_subst_with_closed_cont in H_eval_cont_aux by ensure_closed. simpl in H_eval_cont_aux.
        rewrite -> expr_subst_on_closed_expr in H_eval_cont_aux by ensure_closed.
        inverts H_eval_cont_aux as H_eval_cont_aux.
        inverts H_eval_cont_aux as.
        * contradiction.
        * introv _ H_eval_cont_aux.
          apply IHH_eval2 in H_eval_cont_aux; [| ensure_closed].
          rewrite -> expr_subst_with_closed_cont in H_eval_cont_aux by ensure_closed. simpl in H_eval_cont_aux.
          inverts H_eval_cont_aux as H_eval_cont_aux.
          inverts H_eval_cont_aux as.
          { contradiction. }
          { contradiction. }
          { auto. }
        * inverts H_eval2 as. auto.
      + inverts H_eval1 as.
        introv _ H_eval_cont_aux.
        apply IHH_eval2 in H_eval_cont_aux; [| ensure_closed].
        rewrite -> expr_subst_with_closed_cont in H_eval_cont_aux by ensure_closed. simpl in H_eval_cont_aux.
        inverts H_eval_cont_aux as H_eval_cont_aux.
        inverts H_eval_cont_aux as.
        { contradiction. }
        { contradiction. }
        { auto. }
      + inverts H_eval1 as.
      + inverts H_eval1 as.
        inverts H_eval2 as. auto.
    - destruct H_expr as [H_expr1 H_expr2].
      forwards [H_heap2 H_val1]: eval_preserves_closedness H_eval1 H_heap1 H_expr1.
      forwards [H_heap3 H_val2]: eval_preserves_closedness H_eval2 H_heap2 H_expr2.
      specialize (IHH_eval1 H_heap1 H_expr1).
      specialize (IHH_eval2 H_heap2 H_expr2).
      inverts H_eval_cont_aux as H_eval_cont_aux.
      apply IHH_eval1 in H_eval_cont_aux; [| ensure_closed].
      rewrite -> expr_subst_on_closed_expr in H_eval_cont_aux by ensure_closed.
      inverts H_eval_cont_aux as H_eval_cont_aux.
      apply IHH_eval2 in H_eval_cont_aux; [| ensure_closed].
      assumption.
    - destruct H_expr as [H_expr1 H_expr2].
      forwards [H_heap2 H_val1]: eval_preserves_closedness H_eval1 H_heap1 H_expr1.
      forwards H_expr2': expr_subst_preserves_closedness H_expr2 H_val1.
      forwards [H_heap3 H_val2]: eval_preserves_closedness H_eval2 H_heap2 H_expr2'.
      specialize (IHH_eval1 H_heap1 H_expr1).
      specialize (IHH_eval2 H_heap2 H_expr2').
      inverts H_eval_cont_aux as H_eval_cont_aux.
      apply IHH_eval1 in H_eval_cont_aux; [| ensure_closed].
      rewrite -> expr_subst_with_closed_cont in H_eval_cont_aux by ensure_closed.
      inverts H_eval_cont_aux as H_eval_cont_aux.
      apply IHH_eval2 in H_eval_cont_aux; [| ensure_closed].
      assumption.
    - destruct H_expr as [H_expr1 [H_expr2 H_expr3]].
      forwards [H_heap2 H_val1]: eval_preserves_closedness H_eval1 H_heap1 H_expr1.
      forwards [H_heap3 H_val2]: eval_preserves_closedness H_eval2 H_heap2 H_expr2.
      specialize (IHH_eval1 H_heap1 H_expr1).
      specialize (IHH_eval2 H_heap2 H_expr2).
      inverts H_eval_cont_aux as.
      + introv _ H_eval_cont_aux.
        apply IHH_eval1 in H_eval_cont_aux; [| ensure_closed].
        rewrite -> expr_subst_with_closed_cont in H_eval_cont_aux by ensure_closed. simpl in H_eval_cont_aux.
        rewrite -> expr_subst_on_closed_expr in H_eval_cont_aux by ensure_closed.
        rewrite -> expr_subst_on_closed_expr in H_eval_cont_aux by ensure_closed.
        inverts H_eval_cont_aux as H_eval_cont_aux.
        inverts H_eval_cont_aux as.
        * contradiction.
        * auto.
      + inverts H_eval1 as. auto.
      + inverts H_eval1 as.
    - destruct H_expr as [H_expr1 [H_expr2 H_expr3]].
      forwards [H_heap2 H_val1]: eval_preserves_closedness H_eval1 H_heap1 H_expr1.
      forwards [H_heap3 H_val2]: eval_preserves_closedness H_eval2 H_heap2 H_expr3.
      specialize (IHH_eval1 H_heap1 H_expr1).
      specialize (IHH_eval2 H_heap2 H_expr3).
      inverts H_eval_cont_aux as.
      + introv _ H_eval_cont_aux.
        apply IHH_eval1 in H_eval_cont_aux; [| ensure_closed].
        rewrite -> expr_subst_with_closed_cont in H_eval_cont_aux by ensure_closed. simpl in H_eval_cont_aux.
        rewrite -> expr_subst_on_closed_expr in H_eval_cont_aux by ensure_closed.
        rewrite -> expr_subst_on_closed_expr in H_eval_cont_aux by ensure_closed.
        inverts H_eval_cont_aux as H_eval_cont_aux.
        inverts H_eval_cont_aux as.
        * contradiction.
        * auto.
      + inverts H_eval1 as.
      + inverts H_eval1 as. auto.
    - forwards [H_heap2 H_val]: eval_preserves_closedness H_eval H_heap1 H_expr.
      specialize (IHH_eval H_heap1 H_expr).
      inverts H_eval_cont_aux as.
      + introv _ H_eval_cont_aux.
        apply IHH_eval in H_eval_cont_aux; [| ensure_closed].
        rewrite -> expr_subst_with_closed_cont in H_eval_cont_aux by ensure_closed. simpl in H_eval_cont_aux.
        inverts H_eval_cont_aux as H_eval_cont_aux.
        inverts H_eval_cont_aux as.
        * contradiction.
        * introv H_prim1' H_eval'.
          destruct (eval_prim1_aux_is_deterministic H H_prim1'). subst. auto.
      + inverts H_eval as.
        introv H_prim1' H_eval'.
        destruct (eval_prim1_aux_is_deterministic H H_prim1'). subst. auto.
    - destruct H_expr as [H_expr1 H_expr2].
      forwards [H_heap2 H_val1]: eval_preserves_closedness H_eval1 H_heap1 H_expr1.
      forwards [H_heap3 H_val2]: eval_preserves_closedness H_eval2 H_heap2 H_expr2.
      specialize (IHH_eval1 H_heap1 H_expr1).
      specialize (IHH_eval2 H_heap2 H_expr2).
      inverts H_eval_cont_aux as.
      + introv _ H_eval_cont_aux.
        apply IHH_eval1 in H_eval_cont_aux; [| ensure_closed].
        rewrite -> expr_subst_with_closed_cont in H_eval_cont_aux by ensure_closed. simpl in H_eval_cont_aux.
        rewrite -> expr_subst_on_closed_expr in H_eval_cont_aux by ensure_closed.
        inverts H_eval_cont_aux as H_eval_cont_aux.
        inverts H_eval_cont_aux as.
        * contradiction.
        * introv _ H_eval_cont_aux.
          apply IHH_eval2 in H_eval_cont_aux; [| ensure_closed].
          rewrite -> expr_subst_with_closed_cont in H_eval_cont_aux by ensure_closed. simpl in H_eval_cont_aux.
          inverts H_eval_cont_aux as H_eval_cont_aux.
          inverts H_eval_cont_aux as.
          { contradiction. }
          { contradiction. }
          { introv H_prim2' H_eval'.
            destruct (eval_prim2_aux_is_deterministic H H_prim2'). subst. auto. }
        * inverts H_eval2 as.
          introv H_prim2' H_eval'.
          destruct (eval_prim2_aux_is_deterministic H H_prim2'). subst. auto.
      + inverts H_eval1 as.
        introv _ H_eval_cont_aux.
        apply IHH_eval2 in H_eval_cont_aux; [| ensure_closed].
        rewrite -> expr_subst_with_closed_cont in H_eval_cont_aux by ensure_closed. simpl in H_eval_cont_aux.
        inverts H_eval_cont_aux as H_eval_cont_aux.
        inverts H_eval_cont_aux as.
        { contradiction. }
        { contradiction. }
        { introv H_prim2' H_eval'.
          destruct (eval_prim2_aux_is_deterministic H H_prim2'). subst. auto. }
      + inverts H_eval1 as.
        inverts H_eval2 as.
        introv H_prim2' H_eval'.
        destruct (eval_prim2_aux_is_deterministic H H_prim2'). subst. auto.
    - inverts H_eval_cont_aux as H_eval_cont_aux' H_eval'.
      destruct (eval_cont_aux_is_deterministic H H_eval_cont_aux'). subst. auto.
    - inverts H_eval_cont_aux as H_eval_cont_aux' H_eval'.
      destruct (eval_cont_aux_is_deterministic H H_eval_cont_aux'). subst. auto.
  Qed.

  Print Assumptions eval_cont_aux_is_cont_of_eval.

End ProgramDeterminism.
