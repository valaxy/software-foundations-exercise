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

Require Import Coq.Lists.List.

Notation "x ++ y" := (app x y). (* Why I should introduce '++' explicitly *)


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
  induction l1 as [|X' l' H].
  - simpl.
    induction l2 as [|X2 l2 H2].
    + reflexivity.
    + simpl.
Abort.           

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
Abort.





