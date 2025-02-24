
From ShiftReset Require Import Logic.
Local Open Scope string_scope.


Inductive bigstep : (expr -> expr) -> heap -> expr -> heap -> val -> Prop :=
  | eval_pval : forall h v,
    bigstep (fun e => e) h (pval v) h v

  | eval_pval_k : forall h v v1 k,
    bigstep (fun e => e) h (k (pval v1)) h v ->
    bigstep k h (pval v1) h v

  | eval_papp_fn : forall h e0 e1 k v,
    bigstep (fun e => k (papp e e1)) h e0 h v ->
    bigstep k h (papp e0 e1) h v

  | eval_papp_arg : forall h v0 e1 k v,
    bigstep (fun e => k (papp (pval v0) e1)) h e1 h v ->
    bigstep k h (papp (pval v0) e1) h v

  | eval_papp_beta : forall h x e v1 v k,
    bigstep k h (subst x v1 e) h v ->
    bigstep k h (papp (pval (vfun x e)) (pval v1)) h v

  | eval_pshift : forall h k v c e,
    bigstep k h (pshift c e) h v

  .
