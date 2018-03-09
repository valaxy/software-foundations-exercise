(**************************************
  Finish reading, Finish exercise
**************************************)

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => 
    match m with
    | O => true
    | S m' => false
    end
  | S n' => 
    match m with
    | O => false
    | S m' => beq_nat n' m'
    end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.


(** **** Exercise: 1 star (nandb)  *)
Definition nandb (b1: bool) (b2: bool): bool :=
  match b1, b2 with
  | true, true => false
  | _, _       => true
  end.


Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.

Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.

Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.

Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.


(** **** Exercise: 1 star (andb3)  *)
Definition andb3 (b1:bool) (b2:bool) (b3:bool): bool :=
  match b1, b2, b3 with
  | true, true, true => true
  | _, _, _          => false
  end.


Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.

Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.

Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.

Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.



(** **** Exercise: 1 star (factorial)  *)
Fixpoint factorial (n:nat): nat :=
  match n with
  | 0 => 1
  | S n => S n * factorial n
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.



(** **** Exercise: 1 star (blt_nat)  *)
Definition blt_nat (n m: nat): bool := andb (leb n m) (negb (beq_nat n m)).

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. reflexivity. Qed.

Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. reflexivity. Qed.

Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. reflexivity. Qed.



(** ****  Exercise: 1 star (plus_id_exercise)  *)
Theorem plus_id_exercise: forall n m o: nat, n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros A B.
  rewrite -> A.
  rewrite -> B.
  reflexivity.
Qed.


(** **** Exercise: 2 stars (mult_S_1)  *)
Theorem mult_S_1: forall n m: nat, 
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m H.
  rewrite -> H.
  reflexivity.
Qed.


(** **** Exercise: 2 stars (andb_true_elim2)  *)
Theorem andb_true_elim2: forall b c: bool, andb b c = true -> c = true.
Proof.
  intros [] [].
  - intros H.
    reflexivity.
  - simpl.
    intros H.
    rewrite H.
    reflexivity.
  - reflexivity.
  - simpl.
    intros H.
    rewrite H.
    reflexivity.
Qed.


(** **** Exercise: 1 star (zero_nbeq_plus_1)  *)
Theorem zero_nbeq_plus_1: forall n: nat, beq_nat 0 (n + 1) = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.
Qed.




(** **** Exercise: 2 stars, optional (decreasing)  *)
(*
Fixpoint func (n: nat) (c: bool): bool := 
  match n, c with
  | 0, false => false
  | 0, true  => true
  | 1, false => false
  | 1, true => true
  | S (S n'), false => func n' true
  | S (S n'), true => func (S n') false
  end.
*)




(** **** Exercise: 2 stars (boolean_functions)  *)
Theorem identity_fn_applied_twice:
  forall (f: bool -> bool),
  (forall (x : bool), f x = x) -> forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros H.
  intros b.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.


(** **** Exercise: 2 stars (andb_eq_orb)  *)
Theorem andb_eq_orb: forall (b c : bool),
  (andb b c = orb b c)-> b = c.
Proof.
  intros [] [].
  - simpl.
    reflexivity.
  - simpl.
    intro H.
    rewrite -> H.
    reflexivity.
  - simpl.
    intro H.
    rewrite H.
    reflexivity.
  - reflexivity.
Qed.


(** **** Exercise: 3 stars (binary)  *)
Inductive bin: Type :=
  | zero: bin
  | twice: bin -> bin
  | extra: bin -> bin.


Fixpoint incr (b: bin): bin := 
  match b with
  | zero => extra zero
  | twice b' => extra b'
  | extra b' => twice (incr b')
  end.

Example test_bin_incr1: incr zero = extra zero.
Proof. reflexivity. Qed.

Example test_bin_incr2: incr (incr zero) = twice (extra zero).
Proof. reflexivity. Qed.

Example test_bin_incr3: incr (incr (incr zero)) = extra (extra zero).
Proof. reflexivity. Qed.

Example test_bin_incr4: incr (incr (incr (incr zero))) = twice (twice (extra zero)).
Proof. reflexivity. Qed.

Example test_bin_incr5: incr (incr (incr (incr (incr zero)))) = extra (twice (extra zero)).
Proof. reflexivity. Qed.


Fixpoint bin_to_nat (b: bin): nat :=
  match b with
  | zero => 0
  | twice b' => 2 * bin_to_nat b'
  | extra b' => 1 + 2 * bin_to_nat b'
  end.


Example test_bin_to_nat1: bin_to_nat zero = 0.
Proof. reflexivity. Qed.

Example test_bin_to_nat2: bin_to_nat (incr zero) = 1.
Proof. reflexivity. Qed.

Example test_bin_to_nat3: bin_to_nat (incr (incr zero)) = 2.
Proof. reflexivity. Qed.

Example test_bin_to_nat4: bin_to_nat (incr (incr (incr zero))) = 3.
Proof. reflexivity. Qed.

Example test_bin_to_nat5: bin_to_nat (incr (incr (incr (incr zero)))) = 4.
Proof. reflexivity. Qed.

