(** finish reading, not finish exercise **)
Require Import List Bool Nat.
Import ListNotations.
Local Open Scope list_scope.

(** **** Exercise: 2 stars (mumble_grumble)  *)
Module MumbleGrumble.

Inductive mumble: Type :=
  | a: mumble
  | b: mumble -> nat -> mumble
  | c: mumble.


Inductive grumble (X: Type): Type :=
  | d: mumble -> grumble X
  | e: X -> grumble X.

(* Check (d (b a 5)). *)
Check (d mumble (b a 5)).
Check (d bool (b a 5)).
Check (e bool true).
Check (e mumble (b c 0)).
(* Check (e bool (b c 0)). *)
Check c.

(*  
 - × [d (b a 5)]
 - √ [d mumble (b a 5)]
 - √ [d bool (b a 5)]
 - √ [e bool true]
 - √ [e mumble (b c 0)]
 - × [e bool (b c 0)]
 - × [c]
*)


End MumbleGrumble.






Fixpoint fold {X Y:Type}(f: X->Y->Y)(l: list X)(b: Y): Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Definition fold_length {X: Type} (l: list X): nat :=
  fold (fun _ n => S n) l 0.



  

(** **** Exercise: 2 stars, optional (poly_exercises)  *)

Theorem app_nil_r: forall (X: Type), forall l: list X, l ++ nil = l.
Proof.
  intros X l.
  induction l as [|X' l' H].
  - reflexivity.
  - simpl.
    rewrite -> H.
    reflexivity.
Qed.


Theorem app_assoc: forall A (l m n: list A), l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n.
  induction l as [|X' l' H].
  - reflexivity.
  - simpl.
    rewrite -> H.
    reflexivity.
Qed.
 

Lemma app_length: forall (X: Type) (l1 l2: list X), length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2.
  induction l1 as [|X' l' H].
  - reflexivity.
  - simpl.
    rewrite -> H.
    reflexivity.
Qed.


(** **** Exercise: 2 stars, optional (more_poly_exercises)  *)
Theorem rev_app_distr: forall X (l1 l2: list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2.
  induction l1.
  - simpl.
    rewrite app_nil_r.
    reflexivity.
  - simpl.
    rewrite IHl1.
    rewrite app_assoc.
    reflexivity.   
Qed. 


Theorem rev_involutive: forall X: Type, forall l: list X,
  rev (rev l) = l.
Proof.
  induction l.
  - reflexivity.
  - simpl.
    rewrite rev_app_distr.
    rewrite IHl.
    reflexivity.
Qed.    
  



(** **** Exercise: 1 star, optional (combine_checks)  *)
(* not do it *)


(** **** Exercise: 2 stars, recommended (split)  *)
Fixpoint split {X Y: Type}(l: list (X*Y)): (list X) * (list Y) :=
  match l with
  | nil => (nil, nil)
  | (x,y) :: t => let (l,r) := split t in (x :: l, y :: r)
  end.
  
Example test_split: split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.


 
(** **** Exercise: 1 star, optional (hd_error_poly)  *)
Definition hd_error {X: Type}(l: list X): option X :=
  match l with
  | nil => None
  | h :: t => Some h
  end.

Example test_hd_error1: hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_error2: hd_error [[1];[2]] = Some [1].
Proof. reflexivity. Qed.



(** **** Exercise: 2 stars (filter_even_gt7)  *)
Definition filter_even_gt7 (l: list nat): list nat :=
  filter (fun x => andb (7 <? x) (even x)) l.

Example test_filter_even_gt7_1: filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2: filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.




(** **** Exercise: 3 stars (partition)  *)
Definition partition {X: Type}(test: X -> bool)(l: list X): list X * list X :=
  (filter test l, filter (fun x => negb (test x)) l).  

Example test_partition1: partition odd [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.

Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.



(** **** Exercise: 3 stars (map_rev)  *)
Theorem map_rev: forall (X Y: Type)(f: X -> Y)(l: list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l.
  induction l.
  - reflexivity.
  - simpl.
    rewrite map_app. (* map_app is a inner Lemma *)
    rewrite IHl.
    reflexivity.
Qed.



(** **** Exercise: 2 stars, recommended (flat_map)  *)
Fixpoint flat_map {X Y: Type}(f: X -> list Y)(l: list X): (list Y) :=
  match l with
  | nil => nil
  | x :: t => (f x) ++ (flat_map f t)
  end.
 
Example test_flat_map1: flat_map (fun n => [n;n;n]) [1;5;4] = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity.  Qed.

   

(** **** Exercise: 2 stars, optional (implicit_args)  *)
(* not do it *)


(** **** Exercise: 1 star, advanced (fold_types_different) *)
(* sum with nat to Z *)


(** **** Exercise: 2 stars (fold_length)  *)
Theorem fold_length_correct: forall X (l: list X), fold_length l = length l.
Proof.
  intros X l.
  induction l.
  - reflexivity.
  - simpl.
    assert (P: forall X (a: X)(l: list X), fold_length (a :: l) = fold_length (a :: nil) + fold_length l). {
      intros Y a' l'.
      unfold fold_length.
      simpl.
      reflexivity.
    }
    rewrite P.
    simpl.
    rewrite IHl.
    reflexivity.
Qed.    


(* More exercises *)



