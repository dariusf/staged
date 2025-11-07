
From CtxEquivIxFree Require Import lang.

(*

Inside-out and outside-in contexts

Assuming 2 is the innermost application, ((1 2) 3),
and we are trying to plug 1 into its place in this expression,

The syntax of contexts is the same, but their structure is .

E ::= □ | E e | v E

standard outside-in contexts:

  □[□ 3][□ 2]
= (□ 3)[□ 2]
= ((□ 2) 3)

rplug ((□ 2) 3) 1
= ((rplug (□ 2) 1) 3)
= (((rplug □ 1) 2) 3)
= ((1 2) 3)

inside-out contexts:
hole args are the surrounding context,
and the topmost term is the innermost context.

plug ((□ 3) 2) 1
= plug (□ 3) (1 2)
= plug □ ((1 2) 3)
= ((1 2) 3)

https://www.williamjbowman.com/teaching/2020/w1/cpsc509/resources/05-reduction.pdf

*)

(* for one level of nesting, both kinds of contexts behave the same *)
Example ex_plug1:
  plug ectx_hole (vint 1) = rplug rctx_hole (vint 1).
Proof. reflexivity. Qed.

Example ex_plug2:
    plug (ectx_app1 ectx_hole (vint 2)) (vint 1)
  = rplug (rctx_app1 rctx_hole (vint 2)) (vint 1).
Proof. reflexivity. Qed.

(* this is where they start to differ *)
Example ex_plug3: plug (ectx_app1 (ectx_app1 ectx_hole (vint 3)) (vint 2))
  (ret (vint 1)) = app (app (vint 1) (vint 2)) (vint 3).
Proof. reflexivity. Qed.

Example ex_rplug3: rplug (rctx_app1 (rctx_app1 rctx_hole (vint 3)) (vint 2))
  (ret (vint 1)) = app (app (vint 1) (vint 3)) (vint 2).
Proof. reflexivity. Qed.