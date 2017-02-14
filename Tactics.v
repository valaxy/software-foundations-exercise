Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.


 
(* This is proved in chapter Lists. *)
Theorem rev_involutive: forall l: list nat, rev (rev l) = l.
Proof. Admitted.    


Definition minustwo (n: nat): nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.






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
  intros l l' H.
  rewrite H.
  symmetry.
  apply rev_involutive.  
Qed.
  


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
  induction n.
  - simpl in P. 
    destruct m.
    + reflexivity.
    + inversion P.
  - induction m.
    + simpl in P.
      inversion P.
    + simpl in P.
      inversion P.
      rewrite <- plus_n_Sm in H0.
      rewrite <- plus_n_Sm in H0.
      inversion H0.
      rewrite -> H1 in IHn.
Abort.



(* Some Exercises *)




(** **** Exercise: 3 stars, optional (combine_split)  *)
Theorem combine_split: forall X Y (l: list (X * Y)) l1 l2,
  split l = (l1, l2) -> combine l1 l2 = l.
Proof.
  intros X Y l l1 l2 H.
  induction l.
  - unfold split in H.
    inversion H.
    reflexivity.
  - simpl in H.
Abort.


(** **** Exercise: 2 stars (destruct_eqn_practice)  *)
Theorem bool_fn_applied_thrice:
  forall (f: bool -> bool)(b: bool),
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct b.
  - destruct (f true) eqn:H.
    + rewrite H.
      rewrite H.
      reflexivity.
    + destruct (f false) eqn:H1.
      * apply H.
      * apply H1. 
  - destruct (f true) eqn:H.
    + destruct (f false) eqn:H1.
      * rewrite H.
        rewrite H.
        reflexivity.
      * rewrite H1.
        rewrite H1.
        reflexivity.
    + destruct (f false) eqn:H1.
      * rewrite H.
        rewrite H1.
        reflexivity.
      * rewrite H1.
        rewrite H1.
        reflexivity.
Qed.             

  
  

