Module NatList.

Require Import Coq.Init.Nat.

Inductive natprod: Type :=
  | pair: nat -> nat -> natprod.

Definition fst (p: natprod): nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p: natprod): nat :=
  match p with
  | pair x y => y
  end.

Notation "( x , y )" := (pair x y).

Definition swap_pair (p: natprod): natprod :=
  match p with
  | (x, y) => (y, x)
  end.

Inductive natlist: Type :=
  | nil : natlist
  | cons: nat -> natlist -> natlist.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint app (l1 l2: natlist): natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)(right associativity, at level 60).

Definition bag := natlist.





(** **** Exercise: 1 star (snd_fst_is_swap)  *)
Theorem snd_fst_is_swap: forall (p: natprod), (snd p, fst p) = swap_pair p.
Proof.
  intros [].
  reflexivity.
Qed.



(** **** Exercise: 1 star, optional (fst_swap_is_snd)  *)
Theorem fst_swap_is_snd: forall (p: natprod), fst (swap_pair p) = snd p.
Proof.
  intros [].
  reflexivity.
Qed.


(** **** Exercise: 2 stars, recommended (list_funs)  *)
Fixpoint nonzeros (l:natlist): natlist  :=
  match l with
  | nil => nil
  | h :: t => 
    match h with
    | O => nonzeros t
    | S n => (S n) :: nonzeros t
    end
  end.

Example test_nonzeros: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.


Fixpoint oddmembers (l: natlist): natlist := 
  match l with
  | nil => nil
  | h :: t =>
    match odd(h) with
    | false => oddmembers t
    | true => h :: oddmembers t
    end  
  end.

Example test_oddmembers: oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.  


Fixpoint countoddmembers (l:natlist): nat :=
  match l with
  | nil => 0
  | h :: t =>
    match odd(h) with
    | false => countoddmembers t
    | true => 1 + countoddmembers t
    end
  end.

Example test_countoddmembers1: countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers2: countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers3: countoddmembers nil = 0.
Proof. reflexivity. Qed.


(** **** Exercise: 3 stars, advanced (alternate)  *)
Fixpoint alternate (l1 l2 :natlist): natlist :=
  match l1, l2 with
  | nil, l2 => l2
  | h :: t, nil => h :: t
  | h :: t, h2 :: t2 => h :: h2 :: alternate t t2
  end.


Example test_alternate1: alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.

Example test_alternate2: alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.

Example test_alternate3: alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.

Example test_alternate4: alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed. 


(** **** Exercise: 3 stars, recommended (bag_functions)  *)
Fixpoint count (v: nat)(s: bag): nat :=
  match s with
  | nil => 0
  | h :: t => 
    match eqb v h with
    | true => 1 + count v t
    | false => count v t
    end
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.


Definition sum (v1 v2: bag): bag := v1 ++ v2.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add (v:nat)(s:bag): bag := v :: s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.

Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Definition member (v:nat)(s:bag): bool := leb 1 (count v s).

Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.

Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.


(* 2 Exercise *)

(* More Exercise *)


(** * Partial Maps *)

Inductive id: Type :=
  | Id: nat -> id.

Definition beq_id x1 x2 :=
  match x1, x2 with
  | Id n1, Id n2 => eqb n1 n2
  end.

(** **** Exercise: 1 star (beq_id_refl)  *)
Theorem beq_id_refl: forall x, true = beq_id x x.
Proof.
  intros x.
  destruct x.
  simpl.
Abort.

End NatList.