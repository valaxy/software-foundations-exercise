(**************************************
  Finish reading, Finish exercise
**************************************)

Require Import Nat Bool.


(* ================================================================= *)
(** * Proof by Induction *)

Theorem plus_n_O: forall n: nat, n = n + 0.
Proof.
  induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity.
Qed.


(** ****  Exercise: 2 stars, recommended (basic_induction)  *)
Theorem mult_0_r: forall n: nat, n * 0 = 0.
Proof.
  induction n as [|n' H].
  - reflexivity.
  - simpl.
    rewrite -> H.
    reflexivity.
Qed.


Theorem plus_n_Sm: forall n m: nat, S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [|n' H].
  - reflexivity.
  - simpl.
    rewrite -> H.
    reflexivity.
Qed.

Theorem plus_comm: forall n m: nat, n + m = m + n.
Proof.
  intros n m.
  induction n as [|n' H].
  - simpl.
    rewrite <- plus_n_O.
    reflexivity.
  - simpl.
    rewrite -> H.
    rewrite -> plus_n_Sm.
    reflexivity.
Qed.



Theorem plus_assoc: forall n m p: nat, n + (m + p) = (n + m) + p.
Proof.
  intros m n p.
  induction n as [|n' H].
  - simpl.
    rewrite <- plus_n_O.
    reflexivity.
  - simpl.
    rewrite -> plus_comm.
    simpl.
    rewrite -> plus_comm.
    rewrite -> H.
    rewrite <- plus_n_Sm.
    simpl.
    reflexivity.
Qed.



(** **** Exercise: 2 stars (double_plus)  *)
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus: forall n, double n = n + n.
Proof.
  intros n.
  induction n as [|n' H].
  - reflexivity.
  - simpl.
    rewrite H.
    rewrite plus_n_Sm.
    reflexivity.
Qed.





(** **** Exercise: 2 stars, optional (evenb_S)  *)
Theorem evenb_S: forall n: nat, even (S n) = negb (even n).
Proof.
  intros n.
  induction n as [|n H].
  - reflexivity.
  - rewrite H.
    rewrite negb_involutive.
    reflexivity.
Qed.



(** **** Exercise: 1 star (destruct_induction)  *)
(*
  destruct: without Hypothesis.
  induction: with Hypothesis.
*)




(* ================================================================= *)
(** * Formal vs. Informal Proof *)


(** **** Exercise: 2 stars, advanced, recommended (plus_comm_informal)  *)
(*
  Proof: (* not do the exercise *)
*)


(** **** Exercise: 2 stars, optional (beq_nat_refl_informal)  *)
(* 
  Proof: (* not do the exercise *)
*)