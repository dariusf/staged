From Coq Require Import Classes.RelationClasses.
From Coq Require Morphisms Program.Basics.

From Staged Require Export HeapF.
From Staged Require Export LibFmap.
From Staged Require Export ExtraTactics.

Local Open Scope string_scope.
(* Local Open Scope nat_scope. *)
Local Open Scope Z_scope.
Local Open Scope list_scope.

Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.

(** * Programs *)
(* Definition var : Type := string. *)
Notation var := string.
Implicit Types x k r : var.

Definition var_eq := String.string_dec.

Definition loc := nat.

Inductive val :=
  | vunit : val
  | vint : Z -> val
  | vfun : var -> expr -> val
  (* | vfix : var -> var -> expr -> val
  | vloc : loc -> val
  | vtup : val -> val -> val
  | vstr : string -> val
  | vbool : bool -> val
  | vlist : list val -> val
  | vfptr : var -> val *)

with expr : Type :=
  | pvar (x: var)
  | pval (v: val)
  | plet (x: var) (e1 e2: expr)
  | padd (e1 e2: expr)
  (* | pfix (xf: var) (x: var) (e: expr)
  | pfun (x: var) (e: expr)
  | pfst (e: expr)
  | psnd (e: expr)
  | pminus (e1 e2: expr)
  | passert (v: expr)
  | pref (v: expr)
  | pderef (v: expr)
  | passign (e1: expr) (e2: expr)
  | pif (v: expr) (e1: expr) (e2: expr)
 *)
  | papp (e1: expr) (e2: expr)
  | pshift (k: var) (e: expr)
  | preset (e: expr).

Implicit Types e : expr.

#[global]
Instance Inhab_val : Inhab val.
Proof.
  constructor.
  exists vunit.
  constructor.
Qed.

Fixpoint subst (y:var) (v:val) (e:expr) : expr :=
  let aux t := subst y v t in
  let if_y_eq x t1 t2 := if var_eq x y then t1 else t2 in
  match e with
  | pval v => pval v
  | padd x z => padd x z
(*
  | pminus x z => pminus x z
  | pfst x => pfst x
  | psnd x => psnd x *)
  | pvar x => if_y_eq x (pval v) e
  (* | passert b => passert (aux b)
  | pderef r => pderef (aux r)
  | passign x z => passign (aux x) (aux z)
  | pref v => pref (aux v)
  | pfun x t1 => pfun x (if_y_eq x t1 (aux t1))
  | pfix f x t1 => pfix f x (if_y_eq f t1 (if_y_eq x t1 (aux t1)))
  *)
  | papp e v => papp e v
  | plet x t1 t2 => plet x (aux t1) (if_y_eq x t2 (aux t2))
  (* | pif t0 t1 t2 => pif (aux t0) (aux t1) (aux t2) *)
  | pshift k e1 => pshift k (aux e1)
  | preset e => preset (aux e)
  end.

Module Val.
  Definition value := val.
End Val.

Module Export Heap := HeapF.HeapSetup Val.

Definition empty_heap : heap := Fmap.empty.




Inductive eresult : Type :=
  | enorm : val -> eresult
  | eshft : val -> var -> var -> expr -> eresult.

Notation "'eshft(' eb ',' 'λ' r r1 '.' ek ')'" :=
  (eshft eb r r1 ek) (at level 30, only printing,
  format "'eshft(' eb ','  'λ' r  r1 '.'  ek ')'" ).

(* Definition penv := Fmap.fmap var (val -> expr). *)
Definition pfun : Type := var * expr.
Definition penv := Fmap.fmap var pfun.
Implicit Types p penv : penv.

#[global]
Instance Inhab_pfun : Inhab (var * expr).
Proof.
  constructor.
  exists ("a", pval vunit).
  constructor.
Qed.

Definition empty_penv : penv := Fmap.empty.

Definition store : Type := Fmap.fmap var val.
Definition empty_store : store := Fmap.empty.
Implicit Types s : store.

Definition get_val s e :=
  match e with
  | pval v => Some v
  | pvar x => Some (Fmap.read s x)
  | _ => None
  end.

Inductive bigstep : penv -> store -> heap -> expr -> store -> heap -> var -> eresult -> Prop :=
  | eval_pval : forall s1 s2 h v p r,
    (* s2 = Fmap.update s1 r v -> *)
    bigstep p s1 h (pval v) s2 h r (enorm v)

  | eval_padd : forall s1 s2 h v1 v2 p e1 e2 r,
    (* s2 = Fmap.update s1 r (vint (v1 + v2)) -> *)
    Some (vint v1) = get_val s1 e1 ->
    Some (vint v2) = get_val s1 e2 ->
    bigstep p s1 h (padd e1 e2) s1 h r (enorm (vint (v1 + v2)))

  | eval_pshift : forall s1 h p k eb r,
    (* TODO is r in s1? *)
    bigstep p s1 h (pshift k eb) s1 h r (eshft (vfun k eb) r r (pvar r))

      (* (eshft (vfun k eb) (vfun "x" (preset (pvar "x")))) *)

  (* | eval_plet : forall s1 s2 s3 h1 h3 h2 x e1 e2 v Re p1 r r1,
    bigstep p1 s1 h1 e1 s3 h3 r (enorm v) ->
    bigstep p1 s3 h3 (subst x v e2) s2 h2 r1 Re ->
    bigstep p1 s1 h1 (plet x e1 e2) s2 h2 r1 Re *)

  | eval_pvar : forall s1 h x v p r,
    v = Fmap.read s1 x ->
    bigstep p s1 h (pvar x) s1 h r (enorm v)

  | eval_plet : forall s1 s2 s3 h1 h3 h2 x e1 e2 v Re p1 r r_,
    bigstep p1 s1 h1 e1 s3 h3 r_ (enorm v) ->
    bigstep p1 (Fmap.update s3 x v) h3 e2 s2 h2 r Re ->
    bigstep p1 s1 h1 (plet x e1 e2) s2 h2 r Re

  (* _4 *)
  | eval_plet_sh : forall x e1 e2 h1 h2 p1 k (y:var) eb ek s1 s2 r r1 r_,
    bigstep p1 s1 h1 e1 s2 h2 r_ (eshft (vfun k eb) r1 r_ ek) ->
    bigstep p1 s1 h1 (plet x e1 e2) s2 h2 r
      (eshft (vfun k eb) y r
        (plet x (papp (pval (vfun r1 ek)) (pvar y))
          (plet r e2 (pvar r))))


  | eval_papp_fun : forall v1 v2 h x e Re p s1 s2 s3 r,
    v1 = vfun x e ->
    s3 = Fmap.update s1 x v2 ->
    bigstep p s3 h e s2 h r Re ->
    bigstep p s1 h (papp (pval v1) (pval v2)) s2 h r Re

  | eval_papp_fun_var : forall v1 v2 h x x1 e Re p s1 s2 s3 r,
    v1 = vfun x e ->
    v2 = Fmap.read s1 x1 ->
    s3 = Fmap.update s1 x v2 ->
    bigstep p s3 h e s2 h r Re ->
    bigstep p s1 h (papp (pval v1) (pvar x1)) s2 h r Re
    (* TODO s2 keeps bindings produced by the app? *)

  (* | eval_app_fix : forall v1 v2 h x e Re xf p,
    v1 = vfix xf x e ->
    bigstep p h (subst x v2 (subst xf v1 e)) h Re ->
    bigstep p h (papp (pval v1) (pval v2)) h Re *)

  | eval_papp_unk : forall v h1 h2 Re fe (f:var) p s1 s2 s3 x r,
    Fmap.read p f = (x, fe) ->
    s3 = Fmap.update s1 x v ->
    (* s4 = Fmap.update s2 r r -> *)
    bigstep p s3 h1 fe s2 h2 r Re ->
    bigstep p s1 h1 (papp (pvar f) (pval v)) s2 h2 r Re


  (*

  | eval_preset_val : forall s1 s2 h1 h2 p e v,
    bigstep p s1 h1 e s2 h2 (enorm v) ->
    bigstep p s1 h1 (preset e) s2 h2 (enorm v)

  | eval_preset_sh : forall s1 s2 s3 h1 h2 h3 R p e x1 x2 eb ek,
    bigstep p s1 h1 e s3 h3 (eshft (vfun x1 eb) (vfun x2 ek)) ->
    bigstep p s3 h3 ((* non-0 *) (subst x1 (vfun x2 ek) eb)) s2 h2 R ->
    bigstep p s1 h1 (preset e) s2 h2 R *)

  .


Notation " '[' penv ','  s1 ',' h1  '|'  e ']'  '~~>'  '[' s2 ','  h2  '|'  r ','  Re ']'" :=
  (bigstep penv s1 h1 e s2 h2 r Re) (at level 30, only printing).

Notation "'pshift' k '.' e" :=
  (pshift k e) (at level 30, only printing,
  format "'pshift'  k '.'  e" ).

Coercion pval : val >-> expr.
Coercion pvar : var >-> expr.
Coercion vint : Z >-> val.

Definition store_read s x : val := Fmap.read s x.
Coercion store_read : store >-> Funclass.
(* Coercion papp : expr >-> Funclass. *)




Definition asn := store -> heap -> Prop.
Implicit Types H : asn.
(* Implicit Types Q : val -> asn. *)

(** * Staged formulae *)
Inductive flow : Type :=
  | req : asn -> flow -> flow
  (* | ens : (val -> asn) -> flow *)
  | ens : var -> asn -> flow
  | ens_ : asn -> flow
  | seq : flow -> flow -> flow
  | fexs : var -> flow -> flow (* exists in store *)
  (* | fex_fresh : var -> flow -> flow
  | fex : forall (A:Type), (A -> flow) -> flow *)

  | sh : var -> var -> flow -> var -> flow
  | rs : flow -> val -> flow

  (* may return the result of a shift.
    input is assumed to be a value most of the time. *)
  | unk : var -> val -> var -> flow

  (* 
  | fall : forall (A:Type), (A -> flow) -> flow
  | intersect : flow -> flow -> flow
  | disj : flow -> flow -> flow
  | shc : var -> flow -> val -> (val -> flow) -> flow
  *)
  .

Implicit Types f : flow.

(* Definition ens_ H := ens (fun r s => \[r = vunit] \* H s). *)

(* Definition ufun := val -> val -> flow. *)
Definition ufun : Type := var * var * flow.
(* Definition senv := Fmap.fmap var ufun. *)
Definition senv := Fmap.fmap var ufun.
Implicit Types u : ufun.
Implicit Types env : senv.
Definition empty_env : senv := Fmap.empty.

#[global]
Instance Inhab_ufun : Inhab ufun.
Proof.
  constructor.
  exists ("a", "b", ens_ (fun s => \[True])).
  constructor.
Qed.

Declare Scope flow_scope.
Open Scope flow_scope.

Infix ";;" := seq (at level 38, right associativity) : flow_scope.

Inductive result : Type :=
  | norm : val -> result
  | shft : var -> var -> flow -> var -> var -> flow -> result.

Notation "'shft(λ' k  r '.'  fb ',' 'λ' x  r1 '.'  fk ')'" :=
(* Notation "'shft(λ' k r '.' fb ',' 'λ' x r1 '.' fk ')'" := *)
  (shft k r fb x r1 fk) (at level 30, only printing
  (* , *)
  (* format "'shft(λ' k  r '.'  fb ','  'λ' x  r1 '.'  fk ')'"  *)
  ).

Fixpoint flow_res f : option var :=
  match f with
  | ens r _ => Some r
  | ens_ _ => None
  | req _ f => flow_res f
  | seq _ f => flow_res f
  | sh _ _ _ r => Some r
  | fexs _ f => flow_res f
  (* | fex_fresh _ f => flow_res f *)
  | unk _ _ r => Some r
  (* | fex f => None *)
  (* TODO remove *)
  | rs _ r => None (* TODO remove *)
  end.

Inductive satisfies : senv -> store -> store ->
  heap -> heap -> result -> var -> flow -> Prop :=

  | s_req : forall env s1 s2 H (h1 h2:heap) R f r,
    (forall (hp hr:heap),
      H s1 hp ->
      h1 = Fmap.union hr hp ->
      Fmap.disjoint hr hp ->
      satisfies env s1 s2 hr h2 R r f) ->
    satisfies env s1 s2 h1 h2 R r (req H f)

  | s_ens : forall env s1 s2 H h1 h2 R v h3 r,
      R = norm v ->
      Fmap.read s1 r = v ->
      (* s2 = Fmap.update s1 r v -> *)
      H s1 h3 ->
      h2 = Fmap.union h1 h3 ->
      Fmap.disjoint h1 h3 ->
    satisfies env s1 s2 h1 h2 R r (ens r H)

  | s_ens_ : forall env s1 s2 H h1 h2 h3 r,
      H s1 h3 ->
      (* s2 = Fmap.update s1 r vunit -> *)
      h2 = Fmap.union h1 h3 ->
      Fmap.disjoint h1 h3 ->
    satisfies env s1 s2 h1 h2 (norm vunit) r (ens_ H)
    (* TODO r is a problem, as ens does nothing to it, so *)

  | s_sh : forall env s1 h1 k fb r r1,
    satisfies env s1 s1 h1 h1
      (shft k r1 fb r r (ens r (fun _ => \[]))) r
      (sh k r1 fb r)
(* (fun r1 => rs (ens r (fun s => \[r = v])) r1) *)

  | s_seq : forall env s3 h3 v s1 s2 f1 f2 h1 h2 R r r1 ,
    satisfies env s1 s3 h1 h3 (norm v) r1 f1 ->
    satisfies env s3 s2 h3 h2 R r f2 ->
    satisfies env s1 s2 h1 h2 R r (seq f1 f2)
  (* if it's a value, we ignore the variable of f1, same as before *)

  | s_seq_sh : forall env s1 s2 f1 f2 fk h1 h2 shb k r r1 r2 r3 r4,
    satisfies env s1 s2 h1 h2 (shft k r1 shb r r2 fk) r4 f1 ->
    Some r3 = flow_res f2 ->
    satisfies env s1 s2 h1 h2 (shft k r1 shb r r3 (fk;; f2)) r3 (f1;; f2)
  (* f2 is depending on r *)

  (* | s_fex s1 s2 h1 h2 R (A:Type) (f:A->flow)
    (H: exists b,
      satisfies s1 s2 h1 h2 R (f b)) :
    satisfies s1 s2 h1 h2 R (@fex A f) *)

  (* | s_fex : forall s1 s2 h1 h2 R (A:Type) (f:A->flow) r,
    (exists b,
      satisfies s1 s2 h1 h2 R r (f b)) ->
    satisfies s1 s2 h1 h2 R r (@fex A f) *)

  | s_fexs : forall env s1 s2 h1 h2 R f x r,
    satisfies env (Fmap.update s1 x vunit) s2 h1 h2 R r f ->
    satisfies env s1 s2 h1 h2 R r (fexs x f)

  (* | s_fex_fresh : forall env s1 s2 h1 h2 R f x r,
    (~ Fmap.indom s1 x -> exists v,
      (* ~ Fmap.indom s1 x /\ *)
      satisfies env (Fmap.update s1 x v) s2 h1 h2 R r f) ->
    satisfies env s1 s2 h1 h2 R r (fex_fresh x f) *)

  | s_unk : forall env s1 s2 s3 h1 h2 R xf fb va r y r1,
    Fmap.read env xf = (y, r1, fb) ->
    s3 = Fmap.update s1 y va ->
    satisfies env s3 s2 h1 h2 R r1 fb ->
    satisfies env s1 s2 h1 h2 R r1 (unk xf va r)

  (* | s_fall s1 s2 h1 h2 R (A:Type) (f:A->flow)
    (H: forall b,
      satisfies s1 s2 h1 h2 R (f b)) :
    satisfies s1 s2 h1 h2 R (@fall A f)


  | s_intersect s1 s2 h1 h2 R f1 f2
    (H1: satisfies s1 s2 h1 h2 R f1)
    (H2: satisfies s1 s2 h1 h2 R f2) :
    satisfies s1 s2 h1 h2 R (intersect f1 f2)

  | s_disj_l s1 s2 h1 h2 R f1 f2
    (H: satisfies s1 s2 h1 h2 R f1) :
    satisfies s1 s2 h1 h2 R (disj f1 f2)

  | s_disj_r s1 s2 h1 h2 R f1 f2
    (H: satisfies s1 s2 h1 h2 R f2) :
    satisfies s1 s2 h1 h2 R (disj f1 f2) *)

    (* TODO no constructive shift free yet *)
    (* satisfies env s1 s2 h1 h2 (shft k shb r1 (rs fk r1)) r f1 -> *)
    (* satisfies env s1 s2 h1 h2 (shft k shb r1 (rs (fk;; f2) r1)) r (f1;; f2) *)

  (*
    (** A [sh] on its own reduces to a [shft] containing an identity continuation. *)

    (** This rule extends the continuation in a [shft] on the left side of a [seq]. Notably, it moves whatever comes next #<i>under the reset</i>#, preserving shift-freedom by constructon. *)

  | s_rs_sh s1 s2 f h1 h2 r rf s3 h3 fb fk k v1 :
    satisfies s1 s3 h1 h3 (shft k fb v1 (fun r2 => rs fk r2)) f ->
    (* ~ Fmap.indom s3 k -> *)
    satisfies
        (Fmap.update s3 k (fun a r =>
          rs (ens_ \[v1 = a];; fk) r)) s2
      h3 h2 rf (rs fb r) ->
    satisfies s1 s2 h1 h2 rf (rs f r)

  | s_rs_val s1 s2 h1 h2 v f
    (H: satisfies s1 s2 h1 h2 (norm v) f) :
    satisfies s1 s2 h1 h2 (norm v) (rs f v) *)

  .

(* Notation "'∃' a1 .. an , H" :=
  (fex (fun a1 => .. (fex (fun an => H)) ..))
  (at level 39, a1 binder, H at level 50, right associativity,
   format "'[' '∃' '/ '  a1  ..  an , '/ '  H ']'") : flow_scope. *)

(* Notation "'∀' a1 .. an , H" :=
  (fall (fun a1 => .. (fall (fun an => H)) ..))
  (at level 39, a1 binder, H at level 50, right associativity,
   format "'[' '∀' '/ '  a1  ..  an , '/ '  H ']'") : flow_scope. *)


Notation "env ','  s1 ',' s2 ','  h1 ','  h2 ','  R ','  r  '|=' f" :=
  (satisfies env s1 s2 h1 h2 R r f) (at level 30, only printing).

Notation "'sh(λ' k r '.' fb ',' r1 ')'" :=
  (sh k r fb r1) (at level 30, only printing,
  format "'sh(λ' k  r '.'  fb ','  r1 ')'" ).

Notation "'ens[' r ']' H" :=
  (ens r H) (at level 30, only printing,
  format "ens[ r ] H").

Notation "f '$(' v ',' r ')'" :=
  (unk f v r) (at level 30, only printing,
  format "f '$(' v ','  r ')'").


(* Notation "'ens' H" :=
  (ens_ H) (at level 30, only printing,
  format "'ens' H"). *)

(* plet "x" (pshift "k" (papp (pvar "k") 1))
      (padd (pvar "x") 2) *)


(* Inductive spec_assert : expr -> var -> flow -> Prop :=

  | sa_pval: forall r v,
    spec_assert (pval v) r (fexs r (ens r (fun s => \[Fmap.read s r = v])))

  | sa_pshift: forall r1 r k e fe,
    spec_assert e r1 fe ->
    spec_assert (pshift k e) r (fexs r (sh k fe r))

  . *)


Module Examples.


Example ex0 : exists Re,
  bigstep empty_penv empty_store empty_heap
  (pshift "k" (papp (pvar "k") 1))
    empty_store empty_heap "r" Re.
Proof.
  exs.
  applys eval_pshift.
  Show Proof.
Qed.

Example ex1 : exists Re,
  bigstep empty_penv empty_store empty_heap
  (plet "x" (pshift "k" (papp (pvar "k") 1))
    (padd (pvar "x") 2))
    empty_store empty_heap "r2" Re.
Proof.
  exs.
  applys eval_plet_sh.
  applys eval_pshift.
  Unshelve.
  exact "y".
  exact "r1".
  Show Proof.
Qed.

Example ex2 : exists R,
  satisfies empty_env empty_store empty_store empty_heap empty_heap R "r1"
    (sh "k" "r2" (unk "k" 1 "r2") "r";;
      ens "r1" (fun s => \[exists i, s "r" = vint i /\ s "r1" = i + 2])).
Proof.
  exs.
  applys s_seq_sh.
  (* applys_eq s_sh. *)
  applys s_sh.
  simpl. reflexivity.
  Show Proof.
Qed.

End Examples.


(* The cases in the triple definition have to be disjoint, meaning one must know exactly what the next outcome is to prove

If there is a program which could be either shift or not, you have to case, then pick the appropriate triple case *)
Inductive spec_assert_valid_under penv env : expr -> var -> flow -> Prop :=
  | sav_base: forall e r f,
    (forall s1 s2 h1 h2 v x e1 r,
      not (bigstep penv s1 h1 e s2 h2 r (eshft v x r e1))) ->
    (forall s1 s2 h1 h2 v,
      bigstep penv s1 h1 e s2 h2 r (enorm v) ->
      satisfies env s1 (Fmap.update s2 r v) h1 h2 (norm v) r f) ->
    spec_assert_valid_under penv env e r f

  | sav_shift: forall e r f, forall eb rb fb,
    spec_assert_valid_under penv env eb rb fb ->
    (forall s1 s2 h1 h2 v r,
      not (bigstep penv s1 h1 e s2 h2 r (enorm v))) ->
    (forall s1 s2 h1 h2, forall k r1 ek,
    (* r1 is the input to the continuation *)
      bigstep penv s1 h1 e s2 h2 r (eshft (vfun k eb) r1 r ek) ->
      exists fk,
        spec_assert_valid_under penv env ek r fk /\
          satisfies env s1 s2 h1 h2 (shft k rb fb r1 r fk) r f) ->
    spec_assert_valid_under penv env e r f.
    


(* Notation "penv ',' env '|-' e ':::' r '.' f" :=
  (spec_assert_valid_under penv env e r f) (at level 30, only printing,
  format " '[v  ' penv ','  env  '|-'  e  ':::'  r '.'  f ']' "). *)

Definition env_compatible penv env :=
  forall e (f:var) x r,
    Fmap.read penv f = (x, e) ->
    exists f1, Fmap.read env f = (x, r, f1) /\
    spec_assert_valid_under penv env e r f1.

(* this has the env_compatible premise. kept for posterity, for now. *)
Definition spec_assert_valid_env e r f : Prop :=
  forall penv env,
    env_compatible penv env ->
    spec_assert_valid_under penv env e r f.

Definition spec_assert_valid e r f : Prop :=
  forall penv env,
    spec_assert_valid_under penv env e r f.

(* Notation "e ':::' r '.' f" :=
  (spec_assert_valid e r f) (at level 30, only printing,
  format "'[' e ':::'  r '.' f ']'"). *)

(* trying to use env_compatible, like in the HO work.
  the problem with this is we have to split on something before we know
  whether to use [sav_base] or [sav_shift]. here we only get that
  something after using [sav_base]. *)

(* Lemma papp_unk_sound_fail: forall (f:var) (v:val) r,
  spec_assert_valid_env (papp f v) r (unk f v r).
Proof.
  unfold spec_assert_valid_env. intros * Henv.
  applys sav_base. intros * Hb.
  inverts Hb as Hb.
  specializes Henv Hb. destr Henv.
  applys s_unk.
  eassumption.
  reflexivity.
  inverts H1 as H1.
  { specializes H1 H10.
    assumption. }
  { (* cannot be proved.
      we have to have used sav_shift earlier. *)
    admit. }
Abort. *)


Lemma pvar_sound: forall x,
  spec_assert_valid (pvar x) x (ens x (fun s => \[])).
Proof.
  unfold spec_assert_valid. intros.
  applys sav_base. { intros * H. false_invert H. }
  intros.
  inverts H. (* eval_pvar *)
  applys* s_ens.
  hintro.
  fmap_eq.
Qed.

(* Lemma pvar_sound1: forall x r,
  spec_assert_valid (pvar x) r (fexs "r" (ens r (fun s => \[s "x" = s "r"]))).
Proof.
  unfold spec_assert_valid. intros.
  applys sav_base. { intros * H. false_invert H. }
  intros.
  inverts H. (* eval_pvar *)
  applys* s_fexs. exists (s2 "x").
  applys* s_ens.
  (* hintro. *)
  fmap_eq.
Qed. *)

Lemma pshift_sound: forall r r1 k eb fb,
  spec_assert_valid eb r1 fb ->
  spec_assert_valid (pshift k eb) r (sh k r1 fb r).
Proof.
  unfold spec_assert_valid. intros r **.
  specializes H penv0 env.

  applys sav_shift H. { intros * H0. false_invert H0. }
  introv Hb.
  (* r0 is the input to ek *)

  (* invert Hb. *)
  pose proof Hb as H0.
  inverts Hb.
  (* r2=r0 *)
  exs.
  split.
  (* TODO how to know that r is the return val of the cont in the big step? *)

  apply pvar_sound.
  (* apply pval_sound. *)

  applys s_sh.
  (* f_equal. *)

  (* applys s_sh. *)

Qed.
(* Abort. *)



Lemma papp_unk_sound: forall penv env (f:var) (v:val) r,
  forall x e f1,
  Fmap.read penv f = (x, e) ->
  Fmap.read env f = (x, r, f1) ->
  spec_assert_valid_under penv env e r f1 ->

  spec_assert_valid_under penv env (papp f v) r (unk f v r).
Proof.
  unfold spec_assert_valid. intros * ? ? He.
  inverts He as.
  { intros Hne He.
    (* eval_papp_unk *)
    applys sav_base.
    {
      intros.
      unfold not. intros.
      inverts H1 as H1 H2.
      rewrite H in H1. injects H1.
      unfold not in Hne.
      false Hne H2.
    }

    intros * Hb.
    inverts Hb as. intros * ? Hb.
    rewrite H in H3. injects H3.
    specializes He Hb.
    applys s_unk.
    eassumption.
    reflexivity.
    assumption. }
  { intros * Heb Hne He.
    applys sav_shift Heb.
    { unfold not. intros.
      inverts H1 as H1 H2.
      rewrite H in H1. injects H1.
      false Hne H2. }
    intros * Hb.
    specializes Hb.
    inverts Hb as H3 H4. intros.
    rewrite H in H3. injects H3.
    specializes He H4. destruct He as (fk&?&?).
    exs.
    split*.
    applys s_unk.
    eassumption.
    reflexivity.
    destr H1.
    eassumption. }
Qed.

Lemma pval_sound: forall v r,
  (* spec_assert (pval v) r (fexs r (ens r (fun s => \[Fmap.read s r = v]))) -> *)
  spec_assert_valid (pval v) r (fexs r (ens r (fun s => \[Fmap.read s r = v]))).
Proof.
  unfold spec_assert_valid. intros.
  (* TODO remove these after confirming that they are useless *)
  (* useless, value case must be proved entirely using semantics *)
  (* inverts H. *)
  (* clear H. *)
  applys sav_base.
  {
    unfold not. intros.
    false_invert H.
  }
  intros.
  inverts H as H. (* eval_pval *)
  apply s_fexs. exists v0.
  applys* s_ens.
  resolve_fn_in_env.
  (* rewrite* update_update_idem. *)
  hintro. resolve_fn_in_env.
  fmap_eq.
Qed.


Lemma papp_sound: forall x e r (va:val) f,
  spec_assert_valid e r f ->
  spec_assert_valid (papp (vfun x e) va) r
    (fexs x (ens_ (fun s => \[s x = va]);; f)).
Proof.
  unfold spec_assert_valid.
  intros * He penv env.
  specializes He penv env.
  (* eval_papp_fun *)
  inverts He as.
  { intros Hne He.
    (* no shift in the body of the fn being applied *)
    applys sav_base.
    { intros * H. inverts H as H H1. injects H. false Hne H1. }
    intros.
    inverts H as H H1. injects H.
    specializes He H1. clear H1.
    (* applys s_fex_fresh. intros. exists va. *)
    applys s_fexs. exists va.
    applys s_seq He. clear He.
    applys s_ens_.
    hintro. unfold store_read. resolve_fn_in_env.
    fmap_eq.
    fmap_disjoint.
    Unshelve.
    exact "anything".
    (* this is due to the ens_ variable being unconstrained *)
  }
  {
    intros * Heb Hne He.
    (* shift *)
    applys sav_shift Heb.
    {
      unfold not. intros.
      inverts H as H H1. injects H.
      false Hne H1.
    }
    intros.
    inverts H as H H1. injects H.
    specializes He H1. destr He.
    exs.
    splits*.

    (* applys s_fex_fresh. intros. exists va. *)
    applys s_fexs. exists va.
    applys s_seq.
    applys s_ens_.
    hintro. unfold store_read. resolve_fn_in_env.
    fmap_eq.
    reflexivity.
    fmap_disjoint.
    eassumption.
    Unshelve.
    exact "anything".
    (* this is due to the ens_ variable being unconstrained *)
  }
Qed.



(* papp (pvar "k") (pval (vint 1)) *)

(* Example ex_shift:
  spec_assert_valid (pval (vint 1)) "r"
    (ens "r" (fun s => \[Fmap.read s "r" = vint 1])) ->
  spec_assert_valid
    (pshift "k" (pval (vint 1)))
    "r"
    (fexs "k" (sh "k" (ens "r1" (fun s => \[Fmap.read s "r1" = vint 1])) "r")). *)

(* Example ex_shift: forall eb fb,
  spec_assert_valid eb "r" fb ->
  spec_assert_valid
    (pshift "k" eb)
    "r"
    (fexs "r" (sh "k" fb "r")).
Proof.
  intros.
  applys sav_shift H.
  intros.
  inverts H0 as H0.
  exs.
  apply s_fexs.
  exs.
  applys_eq s_sh.
Qed. *)

(* TODO need a var rule basically *)

(* let x = 1 in x + 2 *)
(* ens x=1; ens[r] r=x+2 *)
(* Example ex_let:
  spec_assert_valid
    (plet "x" (pval (vint 1)) (padd (pval (vint 2)) (pvar "x"))) "r"
    (ens_ (fun s => \[Fmap.read s "x" = (vint 1)]);;
      ens "r" (fun s => \[exists v, vint v = Fmap.read s "x" /\ Fmap.read s "r" = (vint (v + 2))])).
Proof.
  (* apply sav_base.
  intros.
  inverts H as H.
  specializes H "x".
  inverts H as H.
  inverts H10 as H10.
  simpl in H10. injects H10.
  simpl in H9. rew_fmap. injects H9.

  eapply s_seq.
  eapply s_ens_.
  hintro. *)
Abort. *)

(* let x = 1 in x + 2 *)
(* ens x=1; ens[r] r=x+2 *)

(* let x = shift k. k 1 in x + 2 *)
(* sh(k, k(1, r1), x); ens[r] r=x+2 *)
(* Example ex_let_shift:
  (* TODO need a premise about the unknown k *)
  spec_assert_valid
    (plet "x" (pshift "k" ((pvar "k") 1)) (padd 2 (pvar "x")))
    "r"
    (sh "k" (unk "k" 1 "x") "x";;
      ens "r" (fun s => \[exists v, vint v = s "x" /\ s "r" = (v + 2)])).
    (* (ens_ (fun s => \[s "x" = 1]);;
      ens "r" (fun s => \[exists v, vint v = s "x" /\ s "r" = (v + 2)])). *)
Proof.
  (* eapply sav_shift. *)
  (* intros. *)

  (* inverts H as H.
  specializes H "x".
  inverts H as H. *)

  (* inverts H10 as H10.
  simpl in H10. injects H10.
  simpl in H9. rew_fmap. injects H9.

  eapply s_seq.
  eapply s_ens_.
  hintro. *)
Abort. *)

(* Lemma plet_inside: forall p env e2 r f2 rk fk ek x,
  spec_assert_valid_under p env e2 r f2 ->
  spec_assert_valid_under p env ek rk fk ->
  spec_assert_valid_under p env (plet x (papp (vfun r ek) r) e2) rk
    (fk;; fexs x f2).
Proof.
  introv He2 Hek.
  (* _4 *)
  inverts Hek as.
  { (* continuation has no shifts *)
    introv Hnek Hek.
    inverts He2 as.
    { (* e2 has no shifts *)
      (* introv H H1 H2. *)
      introv Hne2 He2.
      applys sav_base.
      { introv Hb.
        inverts Hb.
        false Hne2 H10.
        specializes H8.
        inverts H8. injects H1.
        (* unfold not in Hnek.
        forwards: Hnek. applys_eq H12. f_equal. *)
        (* specializes Hnek H12. *)
        false Hnek H12. }
      (* clear Hnek Hne2. *)
      introv Hb.
      inverts Hb.
      {
        specializes H9.
        inverts H9. injects H1.
        specializes Hek H13.
        (* Search (update _ _ (read _ _)). *)
        erewrite update_idem in Hek.
        3: { reflexivity. }
        2: {
         admit.
        }
        applys s_seq Hek.
        applys s_fexs. exs.

        forwards: He2.
        applys_eq H10.

        (* specializes He2 H10. *)

        admit.
        applys_eq H.
        admit.
        }
    }
    { admit. }


    }
  { admit. }

Abort. *)

Definition plet_test x e1 e2 r f1 f2 :=
  (forall y, spec_assert_valid e1 y f1) ->
  spec_assert_valid e2 r f2 ->
  spec_assert_valid (plet x e1 e2) r
    (f1;; fexs x f2).

Lemma plet_test1:
  plet_test "x"
    (pshift "k" (papp (pvar "k") 1))
      (padd (pvar "x") 2)
    "r"
    (sh "k" "r1" (unk "k" 1 "r1") "x")
      (ens "r" (fun s => \[exists i, s "x" = vint i /\ s "r" = i + 2])).
Proof.
  unfold plet_test.
  unfold spec_assert_valid.
  introv He1 He2. intros.
  specializes He1 "x" penv0 env.
  specializes He2 penv0 env.
  (* preamble done *)
  inverts He1 as. { introv H. exfalso. eapply H. applys eval_pshift. }
  introv Heb Hne1 He1.
  (* e1/f1 is a shift, so we have a triple about the body,
    that it's not norm, and a validity premise for if it's a shift *)

  (* start reasoning backwards using the body premise *)
  applys sav_shift Heb. { intros * Hb. inverts Hb. specializes H9. false_invert H9. }
  introv Hb.
  (* if whole let evaluates to a shift (Hb), then we have to prove a triple about the cont, and that there is a corresponding exec in the spec. *)

  (* see how the let evaluates *)
  inverts Hb. { specializes H9. false_invert H9. }
  pose proof H8 as H.
  inverts H.
  (* the e1 evaluates to a shift *)
  (* use the validity fact we have *)
  (* forwards: He1. applys_eq H8. f_equal. *)

  specializes He1 H8.
  destruct He1 as (r0&fk&Htek&Hek).
  (* now we have a triple about the continuation,
    and we know how the sh evaluates to produce it.
    we have to prove a triple about the continuation's extension. *)
  inverts Hek.
  inverts H8.

  (* first find out what the extension is by swapping to the other goal *)
  exists "x".
  eexists.
  split. 2: {
    applys s_seq_sh.
    applys s_sh.
    simpl. reflexivity.
    }
  (* now we know what the extension looks like. we just need a prove a triple about it *)

  (* find out about ek0, the body of the function being applied.
    it's just the identity *)
  inverts Htek.
  2: { exfalso. applys H0. applys eval_pvar. reflexivity. reflexivity. }
  (* we have that it does not evaluate to a shift, and if value, we have a triple *)

  (* now, prove triple about the extension *)
  applys sav_base.
  {
    (* have to prove the cont has no shift *)
    intros * H3.
    inverts H3.
    { specializes H14. inverts H14. injects H4. inverts H15. }
    { inverts H13. injects H4. false H H16. }
  }
  introv H1.

  (* we have to show given a program execution from s1 to s0,
    there is a corresponding execution in the spec *)

  (* reason about let inside the cont *)
  (* symbolically execute the let to find out about the stores *)
  inverts H1 as Hke1 Hke2.
  (* v0 is the value from evaluating the let, it's bound in s5 *)
  specializes Hke1 "x". inverts Hke1. injects H3.
  inverts H15.
  (* rewrite fmap_read_update in Hke2. *)

  inverts Hke2.
  simpl in H9. injects H9.
  simpl in H14. injects H14.
  rewrite fmap_read_update in TEMP.
  subst.

  applys s_seq.
  { (* trivial ens *)
    applys s_ens.
    reflexivity.
    reflexivity.
    hintro.
    fmap_eq. reflexivity.
    fmap_disjoint.
  }

  (* inverts H15. *)
  (* subst v1. *)

  (* inverts H17. *)

  applys s_fexs. exists v1.
  (* TODO how does ens update the store? *)
  applys s_ens.

  reflexivity.
  (* resolve_fn_in_env. *)
  admit.

  hintro.
  exists v1.
  split.
  unfold store_read. rewrite fmap_read_update.
  reflexivity.
  
  admit.
  fmap_eq.
  fmap_disjoint.

Abort.



Lemma plet_sound: forall x e1 e2 r f1 f2,
  (forall y, spec_assert_valid e1 y f1) ->
  spec_assert_valid e2 r f2 ->
  spec_assert_valid (plet x e1 e2) r
    (f1;; fexs x f2).
    (* (f1;; fex_fresh x (ens_ (fun s => \[Fmap.read s r1 = Fmap.read s x]);; f2)). *)
Proof.
  unfold spec_assert_valid.
  intros * He1 He2 penv env.
  specializes He1 penv env.
  specializes He2 penv env.
  inverts He1 as.
  { intros * Hne1 He1.
    (* no shift in e1 *)
    inverts He2 as.
    { intros * Hne2 He2.
      (* no shift in e2 *)
      (* Abort. *)

      apply sav_base.
      {
        unfold not. intros.
        inverts H as H H1.
        { false Hne2 H1. }
        { false Hne1 H. }
          (* Abort. *)
          (* specializes Hne1 H. Hne1 H. *)
      }
      intros.
      inverts H as H H1.
      specializes He1 H. clear H.
      specializes He2 H1. clear H1.
      applys s_seq He1.
      applys s_fexs. exists v0.
      eassumption. }
    { intros * Heb Hne2 He2.
      (* no shift in e1, shift in e2,
        so the result of the whole let is shift *)
      applys sav_shift Heb.
      {
        unfold not. intros.
        inverts H as H H1.
        { false Hne2 H1. }
      }
      intros * Hb.
      inverts Hb as.
      { intros * Hb1 Hb2.
        (* the shift is from e2 *)
        specializes He2 Hb2.
        destr He2.
        (* destruct He2 as (fk&?&?). *)
        exs.

        (* exists fk. *)
        split.
        eassumption.
        specializes He1 Hb1.
        applys s_seq He1.
        applys s_fexs. eexists.
        eassumption.
      }
      {
        intros * Hb1.
        (* the shift is from e1, which is impossible *)
        false Hne1 Hb1.
      }
    }
  }
  { intros * Heb Hne1 He1.
    (* shift in e1 *)

    (* inverts He2 as.
      {
        intros He2.
        applys sav_shift Heb.
        intros * Hb.
        inverts Hb as Hb.
        {
          (* impossible but stuck *)
          admit. }
        {
          (* r0 <> x? *)
          (* specializes He1 Hb. *)
          admit.
        }
      }
      {
        intros * Hb1 He2.
        admit.
      } *)

    (* the result is a shift *)
    applys sav_shift Heb. { intros * H. inverts H as H. false Hne1 H. }
    clear Heb. intros.
    (* consider the ways in which the let produces a shift *)
    inverts H as. { intros * Hb1 Hb2. false Hne1 Hb1. }
    rename ek0 into ek.
  
    (* finally, the let-shift case *)
    intros * Hb.
    specializes He1 Hb. clear Hb.
    destruct He1 as (rk&fk&Hek&He1). exists rk. eexists.
    (* now we have to prove that the continuation is built correctly *)
    split.
    (* figure out the shape of the continuation fk first *)
    2: {
      applys s_seq_sh.
      (* applys_eq s_sh. *)
      { apply He1. }
      { simpl. admit. }
    }
    (* now we know everything after the seq is part of the continuation *)
    (* case on whether the continuation itself performs any shifts *)

    inverts Hek as.
    { introv Heksf Hefk.
      (* the continuation does not perform any shifts *)
      applys sav_base.
      {
        (* we have to show that applying the continuation does not result in shifts *)
        introv Hb.
        (* the body of a continuation is a let. the e1 can have shifts or not *)
        inverts Hb as H12 H13.
        
        {
          (* the e1 has no shift *)
          clear Heksf.

          specializes H12.
          inverts H12 as H12.
          injects H12.
          specializes Hefk H11.

          (* false Heksf. *)
          (* applys_eq H11. *)
          

          admit. }

        {
          (* the e1 has shifts *)
          specializes H12.
        inverts H12. injects H1.
        false Heksf H11. }

        (* 2: { specializes H12. false_invert H12. }
        (* invert H12. *)
        specializes H12.
        inverts H12. injects H1. *)

      }
      admit.
    }
    { (* the continuation performs more shifts *)
      introv Heb0 Heksh Hefk.
      applys sav_shift Heb0.
      { admit. }
      admit.
    }
    
  }
Abort.
