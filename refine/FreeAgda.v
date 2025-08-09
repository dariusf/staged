

(* Inductive Free (C:Type) (R:C->Type) (a:Type) : Type :=
  | pure : a -> Free C R a
  | step (c:C) : (R c -> Free C R a) -> Free C R a
  .

Set Implicit Arguments.

Fixpoint bind m f :=
  match m with
  | pure _ _ _ x => f x
  | step _ _ _ c k => step _ _ _ c (fun x => bind (k x) f)
  end
  . *)

(* Check pure.
Check pure _ _ _ 1.
Check fun c => step c. *)
(* Check fun c => step c (pure _ _ _ ). *)


(* Definition grec (C:Type) (R:C->Type) : Type := *)
(* fun C R => bool. *)
  (* forall (c:C), Free C R (R c). *)

(* Definition call := fun arg => step arg (fun x => @pure _ _ _ x). *)

(* Check call 1. *)
