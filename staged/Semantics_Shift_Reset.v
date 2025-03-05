(* remove when https://github.com/coq/coq/pull/19673 is merged *)
Set Warnings "-notation-incompatible-prefix".
From Staged Require Export HeapF.
Set Warnings "notation-incompatible-prefix".
From Staged Require Export LibFmap.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Set Implicit Arguments.

(** * Programs *)
Definition var : Type := string.
Definition var_of (x : string) : var := x.
Definition var_eqb (x1 x2 : var) : bool :=
  if String.string_dec x1 x2 then true else false.

Definition loc := nat.
Definition null := 0%nat.
Definition loc_eqb : loc -> loc -> bool := Nat.eqb.

Inductive prim1 : Type :=
| prim1_neg : prim1
| prim1_ref : prim1
| prim1_get : prim1
| prim1_free : prim1.

Inductive prim2 : Type :=
| prim2_add : prim2
| prim2_sub : prim2
| prim2_mul : prim2
| prim2_eq : prim2
| prim2_lt : prim2
| prim2_set : prim2.

Inductive val : Type :=
| val_unit : val
| val_bool : bool -> val
| val_int : Z -> val
| val_loc : loc -> val
| val_fun : var -> expr -> val
| val_fix : var -> var -> expr -> val

with expr : Type :=
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
| expr_cps : expr -> (var * expr) -> expr.

Definition cont : Type := var * expr.

#[global] Instance Inhab_val : Inhab val.
Proof. exact (Inhab_of_val val_unit). Qed.

#[global] Instance Inhab_expr : Inhab expr.
Proof. exact (Inhab_of_val (expr_val val_unit)). Qed.

Module CoerceVal.
  Coercion val_bool : bool >-> val.
  Coercion val_int : Z >-> val.
  Coercion val_loc : loc >-> val.
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
    (expr_let x e1 e2)
      (in custom expr at level 69,
          x at level 0,
          e1 custom expr,
          e2 custom expr,
          right associativity) : expr_scope.

  Notation "'let' f x1 .. xn '=' e1 'in' e2" :=
    (expr_let f (expr_fun x1 .. (expr_fun xn e1) ..) e2)
      (in custom expr at level 69,
          f, x1, xn at level 0,
          e1 custom expr,
          e2 custom expr,
          right associativity) : expr_scope.

  Notation "'let' 'rec' f x '=' e1 'in' e2" :=
    (expr_let f (expr_fix f x e1) e2)
      (in custom expr at level 69,
          f, x at level 0,
          e1 custom expr,
          e2 custom expr,
          right associativity) : expr_scope.

  Notation "'let' 'rec' f x1 x2 .. xn '=' e1 'in' e2" :=
    (expr_let f (expr_fix f x1 (expr_fun x2 .. (expr_fun xn e1) ..)) e2)
      (in custom expr at level 69,
          f, x1, x2, xn at level 0,
          e1 custom expr,
          e2 custom expr,
          right associativity) : expr_scope.

  Notation "'fun' x1 .. xn '=>' e" :=
    (expr_fun x1 .. (expr_fun xn e) ..)
      (in custom expr at level 69,
          x1, xn at level 0,
          e custom expr at level 99) : expr_scope.

  Notation "'fix' f x '=>' e" :=
    (expr_fix f x e)
      (in custom expr at level 69,
          f, x at level 0,
          e custom expr at level 99) : expr_scope.

  Notation "'fix' f x1 x2 .. xn '=>' e" :=
    (expr_fix f x1 (expr_fun x2 .. (expr_fun xn e) ..))
      (in custom expr at level 69,
          f, x1, x2, xn at level 0,
          e custom expr at level 99) : expr_scope.

  (* shift *)
  Notation "'shift' k '=>' e" :=
    (expr_shift k e)
      (in custom expr at level 69,
          k at level 0,
          e custom expr at level 99) : expr_scope.

  (* reset *)
  Notation "< e >" :=
    (expr_reset e)
      (in custom expr at level 69, e custom expr) : expr_scope.

  (* function value *)
  Notation "'\fun' x '=>' e" :=
    (val_fun x e)
      (in custom expr at level 69,
          x at level 0,
          e custom expr at level 99) : val_scope.

  Notation "'\fun' x1 x2 .. xn '=>' e" :=
    (val_fun x1 (expr_fun x2 .. (expr_fun xn e) ..))
      (in custom expr at level 69,
          x1, x2, xn at level 0,
          e custom expr at level 99) : val_scope.

  Notation "'\fix' f x '=>' e" :=
    (val_fix f x e)
      (in custom expr at level 69,
          f, x at level 0,
          e custom expr at level 99) : val_scope.

  Notation "'\fix' f x1 x2 .. xn '=>' e" :=
    (val_fix f x1 (expr_fun x2 .. (expr_fun xn e) ..))
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

  Definition test_get1 : expr := <{ ! {val_loc null} }>.
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
  let if_y_eq x e1 e2 := if var_eqb x y then e1 else e2 in
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
  | expr_cps e' (x, k) => expr_cps (aux e') (x, if_y_eq x k (aux k))
  end.

Definition prim1_eqb (op1 op2 : prim1) : bool :=
  match op1, op2 with
  | prim1_neg, prim1_neg
  | prim1_ref, prim1_ref
  | prim1_get, prim1_get
  | prim1_free, prim1_free => true
  | _, _ => false
  end.

Definition prim2_eqb (op1 op2 : prim2) : bool :=
  match op1, op2 with
  | prim2_add, prim2_add
  | prim2_sub, prim2_sub
  | prim2_mul, prim2_mul
  | prim2_eq, prim2_eq
  | prim2_lt, prim2_lt
  | prim2_set, prim2_set => true
  | _, _ => false
  end.

Fixpoint val_eqb (v1 v2 : val) : bool :=
  match v1, v2 with
  | val_unit, val_unit =>
      true
  | val_bool b1, val_bool b2 =>
      Bool.eqb b1 b2
  | val_int n1, val_int n2 =>
      Z.eqb n1 n2
  | val_loc p1, val_loc p2 =>
      loc_eqb p1 p2
  | val_fun x1 e1, val_fun x2 e2 =>
      var_eqb x1 x2 && expr_eqb e1 e2
  | val_fix f1 x1 e1, val_fix f2 x2 e2 =>
      var_eqb f1 f2 && var_eqb x1 x2 && expr_eqb e1 e2
  | _, _ =>
      false
  end with
expr_eqb (e1 e2 : expr) : bool :=
  match e1, e2 with
  | expr_val v1, expr_val v2 =>
      val_eqb v1 v2
  | expr_var x1, expr_var x2 =>
      var_eqb x1 x2
  | expr_fun x1 e1', expr_fun x2 e2' =>
      var_eqb x1 x2 && expr_eqb e1' e2'
  | expr_fix f1 x1 e1', expr_fix f2 x2 e2' =>
      var_eqb f1 f2 && var_eqb x1 x2 && expr_eqb e1' e2'
  | expr_app e11 e12, expr_app e21 e22 =>
      expr_eqb e11 e21 && expr_eqb e12 e22
  | expr_seq e11 e12, expr_seq e21 e22 =>
      expr_eqb e11 e21 && expr_eqb e12 e22
  | expr_let x1 e11 e12, expr_let x2 e21 e22 =>
      var_eqb x1 x2 && expr_eqb e11 e21 && expr_eqb e12 e22
  | expr_if e11 e12 e13, expr_if e21 e22 e23 =>
      expr_eqb e11 e21 && expr_eqb e12 e22 && expr_eqb e13 e23
  | expr_prim1 op1 e1', expr_prim1 op2 e2' =>
      prim1_eqb op1 op2 && expr_eqb e1' e2'
  | expr_prim2 op1 e11 e12, expr_prim2 op2 e21 e22 =>
      prim2_eqb op1 op2 && expr_eqb e11 e21 && expr_eqb e12 e22
  | expr_shift k1 e1', expr_shift k2 e2' =>
      var_eqb k1 k2 && expr_eqb e1' e2'
  | expr_reset e1', expr_reset e2' =>
      expr_eqb e1' e2'
  | expr_cps e1' (x1, k1), expr_cps e2' (x2, k2) =>
      expr_eqb e1' e2' && var_eqb x1 x2 && expr_eqb k1 k2
  | _, _ =>
      false
  end.

Definition heap := Fmap.fmap loc val.
Definition empty_heap : heap := Fmap.empty.

Inductive eval_prim1_aux : heap -> prim1 -> val -> heap -> val -> Prop :=
| eval_prim1_aux_neg h b :
  eval_prim1_aux h prim1_neg (val_bool b) h (val_bool (neg b))
| eval_prim1_aux_ref h v p :
  ~ Fmap.indom h p ->
  eval_prim1_aux h prim1_ref v (Fmap.update h p v) (val_loc p)
| eval_prim1_aux_get h p :
  Fmap.indom h p ->
  eval_prim1_aux h prim1_get (val_loc p) h (Fmap.read h p)
| eval_prim1_aux_free h p :
  Fmap.indom h p ->
  eval_prim1_aux h prim1_free (val_loc p) (Fmap.remove h p) val_unit.

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
  eval_prim2_aux h prim2_set (val_loc p) v (Fmap.update h p v) val_unit.

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
  eval_cps_aux h1 e ("x", expr_var "x") h2 r ->
  eval h1 (expr_reset e) h2 r
(* cps *)
| eval_cps h1 h2 e k r :
  eval_cps_aux h1 e k h2 r ->
  eval h1 (expr_cps e k) h2 r
with eval_cps_aux : heap -> expr -> cont -> heap -> val -> Prop :=
| eval_cps_aux_val h1 h2 v x k r :
  eval h1 (expr_subst x v k) h2 r ->
  eval_cps_aux h1 (expr_val v) (x, k) h2 r
| eval_cps_aux_fun h1 h2 x e x' k r :
  eval h1 (expr_subst x' (val_fun x e) k) h2 r ->
  eval_cps_aux h1 (expr_fun x e) (x', k) h2 r
| eval_cps_aux_fix h1 h2 f x e x' k r :
  eval h1 (expr_subst x' (val_fix f x e) k) h2 r ->
  eval_cps_aux h1 (expr_fix f x e) (x', k) h2 r
(* cps of application *)
| eval_cps_aux_app_arg1 h1 h2 e1 e2 k r :
  not_expr_val e1 ->
  eval_cps_aux h1 e1
    ("f", expr_cps (expr_app (expr_var "f") e2) k)
    h2 r ->
  eval_cps_aux h1 (expr_app e1 e2) k h2 r
| eval_cps_aux_app_arg2 h1 h2 v1 e2 k r :
  not_expr_val e2 ->
  eval_cps_aux h1 e2
    ("x", expr_cps (expr_app (expr_val v1) (expr_var "x")) k)
    h2 r ->
  eval_cps_aux h1 (expr_app (expr_val v1) e2) k h2 r
| eval_cps_aux_app_fun h1 h2 x e v k r :
  eval_cps_aux h1 (expr_subst x v e) k h2 r ->
  eval_cps_aux h1
    (expr_app (expr_val (val_fun x e)) (expr_val v))
    k h2 r
| eval_cps_aux_app_fix h1 h2 f x e v k r :
  eval_cps_aux h1
    (expr_subst x v (expr_subst f (val_fix f x e) e))
    k h2 r ->
  eval_cps_aux h1
    (expr_app (expr_val (val_fix f x e)) (expr_val v))
    k h2 r
(* cps of seq *)
| eval_cps_aux_seq h1 h2 e1 e2 k r :
  eval_cps_aux h1 e1 ("_", expr_cps e2 k) h2 r ->
  eval_cps_aux h1 (expr_seq e1 e2) k h2 r
(* cps of let binding *)
| eval_cps_aux_let h1 h2 x e1 e2 k r :
  eval_cps_aux h1 e1 (x, expr_cps e2 k) h2 r ->
  eval_cps_aux h1 (expr_let x e1 e2) k h2 r
(* cps of if then else *)
| eval_cps_aux_if_arg h1 h2 e1 e2 e3 k r :
  eval_cps_aux h1 e1
    ("b", expr_cps (expr_if (expr_var "b") e2 e3) k)
    h2 r ->
  eval_cps_aux h1 (expr_if e1 e2 e3) k h2 r
| eval_cps_aux_if_true h1 h2 e1 e2 k r :
  eval_cps_aux h1 e1 k h2 r ->
  eval_cps_aux h1 (expr_if (expr_val (val_bool true)) e1 e2) k h2 r
| eval_cps_aux_if_false h1 h2 e1 e2 k r :
  eval_cps_aux h1 e2 k h2 r ->
  eval_cps_aux h1 (expr_if (expr_val (val_bool false)) e1 e2) k h2 r
(* cps of prim1 *)
| eval_cps_aux_prim1_arg h1 h2 op e k r :
  not_expr_val e ->
  eval_cps_aux h1 e
    ("x", expr_cps (expr_prim1 op (expr_var "x")) k)
    h2 r ->
  eval_cps_aux h1 (expr_prim1 op e) k h2 r
| eval_cps_aux_prim1_val h1 h2 h3 op v v' x k r :
  eval_prim1_aux h1 op v h2 v' ->
  eval h2 (expr_subst x v' k) h3 r ->
  eval_cps_aux h1 (expr_prim1 op (expr_val v)) (x, k) h3 r
(* cps of prim2 *)
| eval_cps_aux_prim2_arg1 h1 h2 op e1 e2 k r :
  not_expr_val e1 ->
  eval_cps_aux h1 e1
    ("x", expr_cps (expr_prim2 op (expr_var "x") e2) k)
    h2 r ->
  eval_cps_aux h1 (expr_prim2 op e1 e2) k h2 r
| eval_cps_aux_prim2_arg2 h1 h2 op v1 e2 k r :
  not_expr_val e2 ->
  eval_cps_aux h1 e2
    ("y", expr_cps (expr_prim2 op (expr_val v1) (expr_var "y")) k)
    h2 r ->
  eval_cps_aux h1 (expr_prim2 op (expr_val v1) e2) k h2 r
| eval_cps_aux_prim2_val h1 h2 h3 op v1 v2 v x k r :
  eval_prim2_aux h1 op v1 v2 h2 v ->
  eval h2 (expr_subst x v k) h3 r ->
  eval_cps_aux h1
    (expr_prim2 op (expr_val v1) (expr_val v2))
    (x, k) h3 r
(* shift inside cps context *)
| eval_cps_aux_shift h1 h2 k e x k' r :
  eval_cps_aux h1
    (expr_subst k (val_fun x k') e)
    ("x", expr_var "x")
    h2 r ->
  eval_cps_aux h1 (expr_shift k e) (x, k') h2 r
(* reset inside cps context *)
| eval_cps_aux_reset h1 h2 h3 e v x k r :
  eval_cps_aux h1 e ("x", expr_var "x") h2 v ->
  eval h2 (expr_subst x v k) h3 r ->
  eval_cps_aux h1 (expr_reset e) (x, k) h3 r
| eval_cps_aux_cps h1 h2 h3 e k v x k' r :
  eval_cps_aux h1 e k h2 v ->
  eval h2 (expr_subst x v k') h3 r ->
  eval_cps_aux h1 (expr_cps e k) (x, k') h3 r.

Module TestProgramSemantics.

  Import CoerceVal.
  Import CoerceExpr.
  Import ProgramNotations.

  Local Open Scope val_scope.
  Local Open Scope expr_scope.

  Ltac do_args := eauto using eval_val, eval_fun, eval_fix.
  Ltac do_prim := eauto using eval_val, eval_prim1_aux, eval_prim2_aux.

  Definition one_plus_one : expr :=
    <{ let "f" "x" = {var_of "x"} + 1 in {var_of "f"} 1 }>.
  Print one_plus_one.

  Goal eval empty_heap one_plus_one empty_heap 2.
  Proof.
    unfold one_plus_one.
    eapply eval_let.
    eapply eval_fun.
    simpl expr_subst.
    eapply eval_app_fun; do_args.
    simpl expr_subst.
    eapply eval_prim2; do_prim.
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
    eapply eval_let.
    eapply eval_fix.
    simpl expr_subst.
    eapply eval_app_fix; do_args.
    simpl expr_subst.
    eapply eval_if_false.
    eapply eval_prim2; do_prim.
    eapply eval_prim2; do_prim.
    eapply eval_app_fix; do_args.
    eapply eval_prim2; do_prim.
    ring_simplify (3 - 1).
    simpl expr_subst.
    eapply eval_if_false.
    eapply eval_prim2; do_prim.
    eapply eval_prim2; do_prim.
    eapply eval_app_fix; do_args.
    eapply eval_prim2; do_prim.
    ring_simplify (2 - 1).
    simpl expr_subst.
    eapply eval_if_false.
    eapply eval_prim2; do_prim.
    eapply eval_prim2; do_prim.
    eapply eval_app_fix; do_args.
    eapply eval_prim2; do_prim.
    ring_simplify (1 - 1).
    simpl expr_subst.
    eapply eval_if_true.
    eapply eval_prim2; do_prim.
    eapply eval_val.
    do_prim.
  Qed.

  Definition sum_2_ref : expr :=
    <{ let "s" = ref 0 in
       let rec "f" "x" =
             if {var_of "x"} = 0 then
               ()
             else
               let {var_of "_"} = {var_of "s"} := !{var_of "s"} + {var_of "x"} in
               {var_of "f"} ({var_of "x"} - 1)
       in
       let "_" = {var_of "f"} 2 in
       !{var_of "s"} }>.
  Print sum_2_ref.

  Goal eval empty_heap sum_2_ref (Fmap.single 1%nat (val_int 3)) 3.
  Proof.
    unfold sum_2_ref.
    eapply eval_let.
    eapply eval_prim1; do_args.
    eapply (@eval_prim1_aux_ref _ _ 1%nat).
    eapply fmap_not_indom_empty.
    simpl expr_subst.
    eapply eval_let.
    eapply eval_fix.
    simpl expr_subst.
    eapply eval_let.
    eapply eval_app_fix; do_args.
    simpl expr_subst.
    eapply eval_if_false.
    eapply eval_prim2; do_prim.
    eapply eval_let.
    eapply eval_prim2; do_args.
    eapply eval_prim2; do_args.
    eapply eval_prim1; do_args.
    rewrite -> update_empty.
    eapply eval_prim1_aux_get.
    eapply indom_single.
    rewrite -> read_single.
    eapply eval_prim2_aux_add.
    eapply eval_prim2_aux_set.
    eapply indom_single.
    ring_simplify (0 + 2).
    simpl expr_subst.
    eapply eval_app_fix; do_args.
    eapply eval_prim2; do_prim.
    ring_simplify (2 - 1).
    simpl expr_subst.
    eapply eval_if_false.
    eapply eval_prim2; do_prim.
    eapply eval_let.
    eapply eval_prim2; do_args.
    eapply eval_prim2; do_args.
    eapply eval_prim1; do_args.
    rewrite -> update_eq_union_single.
    rewrite -> fmap_single_union_single_eq_single.
    eapply eval_prim1_aux_get.
    eapply indom_single.
    rewrite -> read_single.
    eapply eval_prim2_aux_add.
    eapply eval_prim2_aux_set.
    eapply indom_single.
    ring_simplify (2 + 1).
    simpl expr_subst.
    eapply eval_app_fix; do_args.
    eapply eval_prim2; do_prim.
    ring_simplify (1 - 1).
    simpl expr_subst.
    eapply eval_if_true.
    eapply eval_prim2; do_prim.
    eapply eval_val.
    simpl expr_subst.
    eapply eval_prim1; do_args.
    rewrite -> update_eq_union_single.
    rewrite -> fmap_single_union_single_eq_single.
    rewrite <- (read_single 1%nat (val_int 3)) at 3.
    eapply eval_prim1_aux_get.
    eapply indom_single.
  Qed.

  Definition reset_trivial : expr :=
    <{ <1> }>.
  Print reset_trivial.

  Goal eval empty_heap reset_trivial empty_heap 1.
  Proof.
    unfold reset_trivial.
    eapply eval_reset.
    eapply eval_cps_aux_val.
    simpl expr_subst.
    eapply eval_val.
  Qed.

  Definition app_inside_reset : expr :=
    <{ <(fun "x" => {var_of "x"} + 1) 1> }>.
  Print app_inside_reset.

  Goal eval empty_heap app_inside_reset empty_heap 2.
  Proof.
    unfold app_inside_reset.
    eapply eval_reset.
    eapply eval_cps_aux_app_arg1. exact I.
    eapply eval_cps_aux_fun.
    simpl expr_subst.
    eapply eval_cps.
    eapply eval_cps_aux_app_fun.
    simpl expr_subst.
    eapply eval_cps_aux_prim2_val; do_prim.
    simpl expr_subst.
    eapply eval_val.
  Qed.

  Definition let_inside_reset : expr :=
    <{ < let "x" = 1 in {var_of "x"} > }>.
  Print let_inside_reset.

  Goal eval empty_heap let_inside_reset empty_heap 1.
  Proof.
    unfold let_inside_reset.
    eapply eval_reset.
    eapply eval_cps_aux_let.
    eapply eval_cps_aux_val.
    simpl expr_subst.
    eapply eval_cps.
    eapply eval_cps_aux_val.
    simpl expr_subst.
    eapply eval_val.
  Qed.

  Definition prim1_inside_reset : expr :=
    <{ <not false> }>.
  Print prim1_inside_reset.

  Goal eval empty_heap prim1_inside_reset empty_heap true.
  Proof.
    unfold prim1_inside_reset.
    eapply eval_reset.
    eapply eval_cps_aux_prim1_val; do_prim.
    simpl expr_subst.
    eapply eval_val.
  Qed.

  Definition if_inside_reset : expr :=
    <{ <if 1 = 1 then 69 else 42> }>.
  Print if_inside_reset.

  Goal eval empty_heap if_inside_reset empty_heap 69.
  Proof.
    unfold if_inside_reset.
    eapply eval_reset.
    eapply eval_cps_aux_if_arg.
    eapply eval_cps_aux_prim2_val; do_prim.
    simpl expr_subst.
    eapply eval_cps.
    eapply eval_cps_aux_if_true.
    eapply eval_cps_aux_val.
    simpl expr_subst.
    eapply eval_val.
  Qed.

  Definition shift_reset1 : expr :=
    <{ <1 + shift "k" => {var_of "k"} 1> }>.
  Print shift_reset1.

  Goal eval empty_heap shift_reset1 empty_heap 2.
  Proof.
    unfold shift_reset1.
    eapply eval_reset.
    eapply eval_cps_aux_prim2_arg2. exact I.
    eapply eval_cps_aux_shift.
    simpl expr_subst.
    eapply eval_cps_aux_app_fun.
    simpl expr_subst.
    eapply eval_cps_aux_cps.
    eapply eval_cps_aux_prim2_val; do_prim.
    simpl expr_subst.
    eapply eval_val.
    simpl expr_subst.
    eapply eval_val.
  Qed.

  Definition shift_reset2 : expr :=
    <{ < 3 * shift "k" => {var_of "k"} > 23 }>.
  Print shift_reset2.

  Goal eval empty_heap shift_reset2 empty_heap 69.
  Proof.
    unfold shift_reset2.
    eapply eval_app_fun.
    eapply eval_reset.
    eapply eval_cps_aux_prim2_arg2. exact I.
    eapply eval_cps_aux_shift.
    simpl expr_subst.
    eapply eval_cps_aux_val.
    simpl expr_subst.
    eapply eval_val.
    eapply eval_val.
    simpl expr_subst.
    eapply eval_cps.
    eapply eval_cps_aux_prim2_val; do_prim.
    simpl expr_subst.
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
    eapply eval_let. eapply eval_fun. simpl expr_subst.
    eapply eval_let. eapply eval_fun. simpl expr_subst.
    eapply eval_let. eapply eval_fun. simpl expr_subst.
    eapply eval_let. eapply eval_fun. simpl expr_subst.
    eapply eval_app_fun; do_args. simpl expr_subst.
    eapply eval_app_fun; do_args.
    eapply eval_reset.
    eapply eval_cps_aux_let.
    eapply eval_cps_aux_app_fun. simpl expr_subst.
    eapply eval_cps_aux_seq.
    eapply eval_cps_aux_app_fun. simpl expr_subst.
    eapply eval_cps_aux_shift. simpl expr_subst.
    eapply eval_cps_aux_fun. simpl expr_subst.
    eapply eval_val. simpl expr_subst.
    eapply eval_app_fun; do_args.
    eapply eval_app_fun; do_args. simpl expr_subst.
    eapply eval_cps.
    eapply eval_cps_aux_app_fun. simpl expr_subst.
    eapply eval_cps_aux_shift. simpl expr_subst.
    eapply eval_cps_aux_fun. simpl expr_subst.
    eapply eval_val.
    eapply eval_prim2; do_prim. simpl expr_subst.
    eapply eval_app_fun; do_args.
    eapply eval_app_fun; do_args. simpl expr_subst.
    eapply eval_cps.
    eapply eval_cps_aux_fun. simpl expr_subst.
    eapply eval_val. simpl expr_subst.
    eapply eval_val.
  Qed.

End TestProgramSemantics.
