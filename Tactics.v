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


(* This is proved in chapter Lists. *)
Theorem rev_involutive: forall l: list nat, rev (rev l) = l.
Proof. Admitted.


(** **** Exercise: 3 stars (apply_exercise1)  *)
Theorem rev_exercise1: forall (l l': list nat),
  l = rev l' -> l' = rev l.
Proof.
  intros l l' H.
  rewrite H.
  symmetry.
  apply rev_involutive.  
Qed.
  

Definition minustwo (n: nat): nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.


(** **** Exercise: 1 star, optional (apply_rewrite)  *)

(**
   apply: change goal by forall rule.
   rewrite: change goal by non-forall rule.
 **)



(** **** Exercise: 3 stars, optional (apply_with_exercise)  *)
Example trans_eq_exercise: forall (n m o p: nat),
   m = (minustwo o) ->
   (n + p) = m ->
   (n + p) = (minustwo o).
Proof.
  intros n m o p P Q.
  rewrite <- P.
  rewrite -> Q.
  reflexivity.
Qed.



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


(** **** Exercise: 1 star (inversion_ex6)  *)
Example inversion_ex6: forall (X: Type) (x y z: X) (l j: list X),
  x :: y :: l = nil ->
  y :: l = z :: j ->
  x = z.
Proof.
  intros X x y z l j P Q.
  inversion P.
Qed.


(** **** Exercise: 3 stars, recommended (plus_n_n_injective)  *)
Theorem plus_n_n_injective: forall n m, n + n = m + m -> n = m.
Proof.
  intros n m P. 
  induction n as [| n'].
  - simpl in P.
Abort.


(* Some Exercises *)


