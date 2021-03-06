(**************************************
  not Finish reading, not Finish exercise
**************************************)

Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.




(* ================================================================= *)
(** * The apply Tactic *)

(* This is proved in chapter Lists. *)
Theorem rev_involutive: forall l: list nat, rev (rev l) = l.
Proof. Admitted.


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
   apply: change goal by forall rule or non-forall rule.
   rewrite: change goal by non-forall rule.
 **)





(* ================================================================= *)
(** * The apply ... with ... Tactic *)

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity.  Qed.


Definition minustwo (n: nat): nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

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
Qed. (* do not know how to use apply with *)





(* ================================================================= *)
(** * The inversion Tactic *)

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





(* ================================================================= *)
(** * Using Tactics on Hypotheses *)

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
Abort. (* TODO *)



(* ================================================================= *)
(** * Varying the Induction Hypothesis *)






(* ================================================================= *)
(** * Using destruct on Compound Expressions *)

(** **** Exercise: 3 stars, optional (combine_split)  *)
Theorem combine_split: forall X Y (l: list (X * Y)) l1 l2,
  split l = (l1, l2) -> combine l1 l2 = l.
Proof.
  induction l as [|(x, y) l'].
  + intros l1 l2 h1.
    simpl in h1.
    inversion h1.
    reflexivity.
  + simpl.
    destruct (split l') as [xs ys].
    intros l1 l2 h1.
    inversion h1.
    simpl.
    rewrite IHl'.
    - reflexivity.
    - reflexivity.
Qed.




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

