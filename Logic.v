(** **** Exercise: 2 stars (and_exercise)  *)
Example and_exercise: forall n m: nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m P.
  split.
Abort.



(** **** Exercise: 1 star, optional (proj2)  *)
Lemma proj2: forall P Q: Prop, P /\ Q -> Q.
Proof.
  intros P Q H.
  destruct H.
  apply H0.
Qed.




(** **** Exercise: 2 stars (and_assoc)  *)
Theorem and_assoc: forall P Q R: Prop, P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split.
    apply HP.
    apply HQ.
  - apply HR.
Qed.





(** **** Exercise: 1 star (mult_eq_0)  *)
Lemma mult_eq_0: forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m P.
Abort.  



(** **** Exercise: 1 star (or_commut)  *)
Theorem or_commut: forall P Q: Prop, P \/ Q  -> Q \/ P.
Proof.
  intros P Q [HP|HQ].
  - right.
    apply HP.
  - left.
    apply HQ.
Qed.






(** **** Exercise: 2 stars, optional (not_implies_our_not)  *)
Fact not_implies_our_not: forall (P: Prop),~P -> (forall (Q: Prop), P -> Q).
Proof.
  intros P nP Q xP.
  destruct nP.
  apply xP.
Qed.





(** **** Exercise: 2 stars, advanced, recommended (double_neg_inf)  *)
(* not do it *)


(** **** Exercise: 2 stars, recommended (contrapositive)  *)
Theorem contrapositive: forall P Q: Prop, (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H G.
  unfold not in G.
Abort.
  



(** **** Exercise: 1 star (not_both_true_and_false)  *)
Theorem not_both_true_and_false: forall P: Prop, ~ (P /\ ~P).
Proof.
  intros P.
  unfold not.
  intros H.
  destruct H as [H1 H2].
  apply H2 in H1.
  apply H1.
Qed.



(** **** Exercise: 1 star, advanced (informal_not_PNP)  *)
(* not do it *)








