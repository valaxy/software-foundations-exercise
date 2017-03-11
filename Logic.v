Require Import Coq.Setoids.Setoid List Nat.
Import ListNotations.

(** **** Exercise: 2 stars (and_exercise)  *)
Example and_exercise: forall n m: nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m P.
  split.
  - destruct n.
    + reflexivity.
    + inversion P.
  - destruct n.
    + simpl in P. 
      rewrite P.
      reflexivity.
    + inversion P.
Qed.



(** **** Exercise: 1 star, optional (proj2)  *)
Lemma proj2: forall P Q: Prop, P /\ Q -> Q.
Proof.
  intros P Q [H1 H2].
  apply H2.
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
  intros [|n] [|m] P.
  - left. reflexivity.
  - left. reflexivity.
  - right. reflexivity.
  - inversion P.
Qed.



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
  unfold not.
  intros P Q H1 H2 H3.
  apply H1 in H3.
  apply H2 in H3.
  apply H3.
Qed.



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




(** **** Exercise: 1 star, optional (iff_properties)  *)
Theorem iff_refl: forall P: Prop, P <-> P.
Proof.
  intros P.
  split.
  - intros.
    apply H.
  - intros.
    apply H.
Qed.      



Theorem iff_trans: forall P Q R: Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R [H1 H2] [H3 H4].
  split.
  - intros.
    apply H3.
    apply H1.
    apply H.
  - intros.
    apply H2.
    apply H4.
    apply H.
Qed.


(** **** Exercise: 3 stars (or_distributes_over_and)  *)
Theorem or_distributes_over_and: forall P Q R: Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  - intros [H1 | H2].
    + split.
      * left. assumption.
      * left. assumption.
    + assert (Q). { apply proj1 in H2. assumption. }
      assert (R). { apply proj2 in H2. assumption. }
      split.
      * right. assumption.
      * right. assumption.
  - intros [[H1|H2] [H3|H4]].
    + left. apply H1.
    + left. apply H1.
    + left. apply H3.
    + right. split. assumption. assumption.
Qed.



(** **** Exercise: 1 star (dist_not_exists)  *)
Theorem dist_not_exists: forall (X: Type)(P: X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  unfold not.
  intros X P S [x].
  apply H.
  apply S.
Qed.
  

(** **** Exercise: 2 stars (dist_exists_or)  *)
Theorem dist_exists_or: forall (X: Type) (P Q: X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  - intros [x0 [H1|H2]].
    + left. exists x0. assumption.
    + right. exists x0. assumption.
  - intros [[x0 H] | [x0 H]].
    + exists x0. left. assumption.
    + exists x0. right. assumption.
Qed.


Fixpoint In {A: Type}(x: A)(l: list A): Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.



(** **** Exercise: 2 stars (In_map_iff)  *)
Lemma In_map_iff:
  forall (A B: Type)(f: A -> B)(l: list A)(y: B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros A B f l y.
  split.
  - intros H.
    induction l as [|a l R].
    + simpl in H.
      destruct H.
    + simpl.
      simpl in H.
      destruct H as [H|H].
      * exists a.
        split.
        apply H.
        left. reflexivity.
      * apply R in H.
        destruct H as [x0 H].
        exists x0.
        destruct H as [H0 H1].
        split.
        apply H0.
        right.
        apply H1.
  - intros [x [H P]].
    induction l as [|a l R].
    + destruct P.
    + simpl.
      simpl in P.
      destruct P as [P|P].
      * left.
        subst.
        reflexivity.
      * right.
        apply R in P.
        apply P.
Qed.



(** **** Exercise: 2 stars (in_app_iff)  *)
Lemma in_app_iff: forall A l l' (a: A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l l' a.
  split.
  - induction l as [|x l H].
    + simpl.
      intros P.
      right.
      apply P.
    + simpl.
      intros P.
      destruct P as [P|P].
      * left.
        left.
        apply P.
      * apply H in P.
        destruct P as [P|P].
        left.
        right.
        apply P.
        right.
        apply P.
  - intros [H|H].
    + induction l as [|x l P].
      * destruct H.
      * simpl.
        simpl in H.
        destruct H as [H|H].
        left. apply H.
        right. apply P in H. apply H.
    + induction l as [|x l P].
      * simpl.
        apply H.
      * simpl.
        right.
        apply P.
Qed.



(** **** Exercise: 3 stars (All)  *)

Fixpoint All {T: Type}(P: T -> Prop)(l: list T): Prop :=
  match l with
  | nil => True
  | h :: t => P h /\ All P t
  end.
  
Lemma All_In:
  forall T (P: T -> Prop)(l: list T), (forall x, In x l -> P x) <-> All P l.
Proof.
  intros T P l.
  split.
  - intros H.
    induction l as [|t l Q].
    + simpl.
      apply I.
    + simpl.
      simpl in H.
      split.
      * apply H.
        left.
        reflexivity.
      * apply Q.
        intros y R.
        apply H.
        right.
        apply R.
  - intros H x R.
    induction l as [|t l Q].
    + simpl in R.
      destruct R.
    + simpl in H.
      simpl in R.
      destruct R.
      * subst.
        destruct H as [H0 H1].
        apply H0.
      * apply Q.
        destruct H.
        apply H1.
        apply H0.
Qed.


(** **** Exercise: 3 stars (combine_odd_even)  *)
Definition combine_odd_even_imp (Podd Peven: nat -> Prop)(n: nat): Prop :=
  if odd n then Podd n else Peven n.
  
Definition combine_odd_even (Podd Peven: nat -> Prop): nat -> Prop :=
  combine_odd_even_imp Podd Peven.

(** To test your definition, prove the following facts: *)

Theorem combine_odd_even_intro:
  forall (Podd Peven: nat -> Prop)(n: nat),
    (odd n = true -> Podd n) ->
    (odd n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n H P.
  unfold combine_odd_even.
  unfold combine_odd_even_imp.
  destruct (odd n).
  - apply H.
    reflexivity.
  - apply P.
    reflexivity.
Qed.

Theorem combine_odd_even_elim_odd:
  forall (Podd Peven: nat -> Prop)(n: nat),
    combine_odd_even Podd Peven n ->
    odd n = true ->
    Podd n.
Proof.
  intros Podd Peven n H P.
  unfold combine_odd_even in H.
  unfold combine_odd_even_imp in H.
  destruct (odd n).
  - apply H.
  - inversion P.
Qed.


Theorem combine_odd_even_elim_even:
  forall (Podd Peven: nat -> Prop)(n: nat),
    combine_odd_even Podd Peven n ->
    odd n = false ->
    Peven n.
Proof.
  intros Podd Peven n P Q.
  unfold combine_odd_even in P.
  unfold combine_odd_even_imp in P.
  destruct (odd n).
  - inversion Q.
  - apply P.
Qed.




(** **** Exercise: 4 stars (tr_rev)  *)
Axiom functional_extensionality: forall {X Y: Type}{f g: X -> Y},
  (forall (x: X), f x = g x) -> f = g.

Fixpoint rev_append {X}(l1 l2: list X): list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X}(l: list X): list X := rev_append l [].

Lemma xyz: forall (X: Type)(l1 l2: list X), rev_append l1 l2 = rev_append l1 [] ++ l2.
Proof.
  intros X l1 l2.
  induction l1 as [|x l H].
  - reflexivity.
  - simpl.
    induction l2 as [|y l2 H2].
    + rewrite app_nil_r.
      reflexivity.
    + simpl.
Admitted.    

Lemma tr_rev_correct: forall X, @tr_rev X = @rev X.
Proof.
  intros X.
  apply functional_extensionality.
  intros l.
  induction l as [|x l H].
  - reflexivity.
  - simpl.
    rewrite <- H.
    unfold tr_rev.
    simpl.
    clear H.
    generalize dependent x.
    induction l as [|y l P].
    + reflexivity.
    + simpl.
      intros x.
      rewrite P.
      simpl.
Admitted.


(** **** Exercise: 3 stars (evenb_double_conv)  *)
Theorem evenb_S: forall n: nat, even (S n) = negb (even n).
Proof. Admitted.

Theorem double_negb: forall b: bool, negb (negb b) = b.
Proof. Admitted.

Theorem evenb_double_conv: forall n,
  exists k, n = if even n then double k
                else S (double k).
Proof.
  intros n.
  induction n as [|n [k0 H]].
  - simpl.
    exists 0.
    reflexivity.
  - simpl.
    destruct (even n) eqn:P.
    + exists k0.
      rewrite <- H.
      simpl.
      destruct n.
      * reflexivity.
      * rewrite evenb_S in P.
        destruct (even n).
        simpl in P.
        inversion P.
        reflexivity.
    + exists (k0+1).
      unfold double.
      unfold double in H.
      destruct n.
      * inversion H.
      * rewrite evenb_S in P.
        destruct (even n).
        rewrite H.
Admitted. (* use omega? *)














