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

(* too long prove *)
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



(* 3 Exercise *)

(* More Exercises *)


(* 2 Exercise *)