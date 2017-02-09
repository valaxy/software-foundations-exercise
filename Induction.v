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


Require Import Coq.Init.Nat.


(** **** Exercise: 2 stars, optional (evenb_S)  *)
Theorem evenb_S: forall n: nat, even (S n) = negb (even n).
Proof.
  intros n.
  induction n as [|n H].
  - reflexivity.
  - simpl.
Abort.


(** **** Exercise: 1 star (destruct_induction)  *)
(*
  destruct: without Hypothesis.
  induction: with Hypothesis.
*)


(** **** Exercise: 3 stars, recommended (mult_comm)  *)
Theorem plus_swap: forall n m p: nat, n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  assert (H: n + m = m + n). {
    rewrite -> plus_comm.
    reflexivity.
  }
  rewrite -> H.
  reflexivity.
Qed.


Theorem mult_comm: forall m n: nat, m * n = n * m.
Proof.
  intros m n.
  induction m as [|m' H].
  - rewrite mult_0_r.
    reflexivity.
  - simpl.
    rewrite H.
    induction n as [|n' P].
    + reflexivity.
    + simpl.
Abort.


(* More Exercises *)


(** **** Exercise: 2 stars, advanced, recommended (plus_comm_informal)  *)
(*
  Proof: (* not do the exercise *)
*)


(** **** Exercise: 2 stars, optional (beq_nat_refl_informal)  *)
(* 
  Proof: (* not do the exercise *)
*)