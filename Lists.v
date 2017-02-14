Require Import Coq.Init.Nat.
Require Import Coq.Arith.EqNat.
 
 
Module NatList.

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


Theorem app_assoc: forall l1 l2 l3: natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. 
  induction l1 as [| n l1' IHl1'].
  - reflexivity.
  - simpl. 
    rewrite -> IHl1'. 
    reflexivity.  
Qed.


Fixpoint rev (l: natlist): natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.
  
  

  


  



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


Definition bag := natlist.

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



(** **** Exercise: 3 stars, optional (bag_more_functions)  *)
Fixpoint remove_one (v: nat) (s: bag): bag :=
  match s with
  | nil => nil
  | h :: t => 
    if eqb h v then t
    else h :: remove_one v t
  end.

Example test_remove_one1: count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one2: count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one3: count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_one4: count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.


Fixpoint remove_all (v: nat) (s: bag): bag :=
  match s with
  | nil => nil
  | h :: t =>
    if eqb h v then remove_all v t
    else  h :: remove_all v t
  end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.



Fixpoint subset (s1: bag) (s2: bag): bool :=
  match s1 with
  | nil => true
  | h :: t =>
    if leb (count h s1) (count h s2) then subset t s2
    else false
  end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.

Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.


(** **** Exercise: 3 stars, recommended (bag_theorem)  *)
(* not do the exercese *)



(* ================================================================= *)
(** ** List Exercises, Part 1 *)

(** **** Exercise: 3 stars (list_exercises)  *)
Theorem app_nil_r: forall l: natlist, l ++ [] = l.
Proof.
  induction l as [|l L H].
  - reflexivity.
  - simpl.
    rewrite H.
    reflexivity.
Qed. 


(* for prove rev_involutive *)
Theorem rev_swap: forall l1 l2: natlist, rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2.
  induction l1.
  - simpl.
    symmetry.
    apply app_nil_r.
  - simpl.
    rewrite IHl1.
    apply app_assoc.
Qed.   


Theorem rev_involutive: forall l: natlist, rev (rev l) = l.
Proof.
  induction l as [|l L H].
  - reflexivity.
  - simpl.
    rewrite rev_swap.
    rewrite H.
    reflexivity.
Qed.


(** **** Exercise: 2 stars (beq_natlist)  *)
Fixpoint beq_natlist (l1 l2: natlist): bool :=
  match l1, l2 with
  | nil, nil => true
  | nil, _ => false
  | h1 :: t1, h2 :: t2 => 
    if eqb h1 h2 then beq_natlist t1 t2 else false
  | _, _ => false
  end.

Example test_beq_natlist1: (beq_natlist nil nil = true).
Proof. reflexivity. Qed.

Example test_beq_natlist2: beq_natlist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.

Example test_beq_natlist3: beq_natlist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Theorem beq_natlist_refl: forall l: natlist, true = beq_natlist l l.
Proof. 
  intros l.
  induction l.
  - reflexivity.
  - simpl.
    rewrite <- beq_nat_refl.
    apply IHl.
Qed.


(* ================================================================= *)
(** ** List Exercises, Part 2 *)

(** **** Exercise: 3 stars, advanced (bag_proofs)  *) 
Theorem count_member_nonzero: forall (s: bag),
  leb 1 (count 1 (1 :: s)) = true.
Proof.
  intros s.
  destruct s.
  - reflexivity.
  - reflexivity.
Qed.


(** The following lemma about [leb] might help you in the next proof. *)

Theorem ble_n_Sn : forall n,
  leb n (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl.  reflexivity.
  - (* S n' *)
    simpl.  rewrite IHn'.  reflexivity.  
Qed.

Theorem remove_decreases_count: forall (s: bag),
  leb (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intros s.
Abort.

(** **** Exercise: 3 stars, optional (bag_count_sum)  *)
(* not do it *)


(** **** Exercise: 4 stars, advanced (rev_injective)  *)
(* dont know how to do *)

Definition hd (default: nat)(l: natlist): nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

Definition option_elim (d: nat)(o: natoption): nat :=
  match o with
  | Some n' => n'
  | None => d
  end.


(** **** Exercise: 2 stars (hd_error)  *)
 
Definition hd_error (l: natlist): natoption :=
  match l with
  | nil => None
  | h :: t => Some h
  end.

Example test_hd_error1: hd_error [] = None.
Proof. reflexivity. Qed.

Example test_hd_error2: hd_error [1] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_error3: hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.
 

(** **** Exercise: 1 star, optional (option_elim_hd)  *)
Theorem option_elim_hd: forall (l: natlist)(default: nat),
  hd default l = option_elim default (hd_error l).
Proof.
  intros l default.
  destruct l.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.


End NatList.





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
  intros [x].
  simpl.
  apply beq_nat_refl.
Qed.


Module PartialMap.
Import NatList.
  
Inductive partial_map : Type :=
  | empty  : partial_map
  | record : id -> nat -> partial_map -> partial_map.


Definition update (d: partial_map)(key: id)(value: nat): partial_map :=
  record key value d.
 
Fixpoint find (key: id)(d: partial_map): natoption :=
  match d with
  | empty         => None
  | record k v d' => if beq_id key k
                     then Some v
                     else find key d'
  end.



(** **** Exercise: 1 star (update_eq)  *)
Theorem update_eq: forall (d: partial_map)(k: id)(v: nat),
  find k (update d k v) = Some v.
Proof.
  intros d k v.
  destruct k.
  induction d.
  - simpl.
    rewrite <- beq_nat_refl.
    reflexivity.
  - simpl.
    rewrite <- beq_nat_refl.
    reflexivity.
Qed.
 

(** **** Exercise: 1 star (update_neq)  *)
Theorem update_neq: forall (d: partial_map)(m n: id)(o: nat),
    beq_id m n = false -> find m (update d n o) = find m d.
Proof.
  intros d m n o P.
  destruct m.
  destruct n.
  assert (Q: forall m n, beq_id (Id m) (Id n) = false -> eqb m n = false). {
    intros m' n' H.
    simpl in H.
    apply H.
  }
  apply Q in P.
    
  destruct d.
  - simpl.
    rewrite P.
    reflexivity.
  - simpl.
    rewrite P.
    reflexivity.
Qed.
      
    

End PartialMap.


(** **** Exercise: 2 stars (baz_num_elts)  *)
Inductive baz : Type :=
  | Baz1 : baz -> baz
  | Baz2 : baz -> bool -> baz.

(* Zero. *)

