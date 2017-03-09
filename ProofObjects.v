Inductive ev: nat -> Prop :=
| ev_0: ev 0
| ev_SS: forall n: nat, ev n -> ev (S (S n)).

(** **** Exercise: 1 star (eight_is_even)  *)
Theorem ev_8: ev 8.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.

Print ev_8.

Definition ev_8' : ev 8 := ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0))).


(** **** Exercise: 2 stars, optional (conj_fact)  *)
Theorem test: forall P Q R, P /\ Q -> Q /\ R -> P /\ R.
Proof.
  intros P Q R H1 H2.
  split.
  - apply H1.
  - apply H2.
Qed.

Print test.  

Definition conj_fact: forall P Q R, P /\ Q -> Q /\ R -> P /\ R := 
  fun (P Q R: Prop)(H1: P /\ Q)(H2: Q /\ R) =>
    conj 
      (let H := match H1 with
                | conj x _ => x
                end : P in H)
      (let H := match H2 with
                | conj _ x0 => x0
                end : R in H).