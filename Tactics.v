Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.

(** **** Exercise: 2 stars, optional (silly_ex)  *)
Theorem silly_ex:
  (forall n, even n = true -> odd (S n) = true) ->
  even 3 = true ->
  odd 4 = true.
Proof.
  intros H.
  apply H.
Qed.  



(** **** Exercise: 3 stars (apply_exercise1)  *)
Theorem rev_exercise1: forall (l l': list nat),
  l = rev l' -> l' = rev l.
Proof.
Abort.  
  

(** **** Exercise: 1 star, optional (apply_rewrite)  *)

(**
   apply: change goal by forall rule.
   rewrite: change goal by non-forall rule.
 **)



(** **** Exercise: 3 stars, optional (apply_with_exercise)  *)
(*Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
Abort.
(** [] *)*)


(** **** Exercise: 1 star (inversion_ex3)  *)
Example inversion_ex3: forall (X: Type) (x y z: X) (l j: list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  intros X x y z l j P Q.
  inversion P.
  inversion Q.
  rewrite H0.
  reflexivity.
Qed.