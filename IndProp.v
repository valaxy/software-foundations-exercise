Inductive ev: nat -> Prop :=
| ev_0: ev 0
| ev_SS: forall n : nat, ev n -> ev (S (S n)).


(** **** Exercise: 1 star (ev_double)  *)
Theorem ev_double: forall n, ev (n + n).
Proof.
  intros n.
  induction n as [|n H].
  - simpl.
    apply ev_0.
  - simpl.
    rewrite <- plus_n_Sm.
    apply ev_SS.
    apply H.
Qed.



(** **** Exercise: 1 star (inversion_practice)  *)
Theorem SSSSev__even: forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H.
  inversion H.
  inversion H1.
  apply H3.
Qed.

  
Theorem even5_nonsense: ev 5 -> 2 + 2 = 9.
Proof.
  intros H.
  inversion H.
  inversion H1.
  inversion H3.
Qed.

