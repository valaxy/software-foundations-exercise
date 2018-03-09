Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import String.
Import ListNotations.


Module AExp.

Inductive aexp: Type:=
  | ANum: nat -> aexp
  | APlus: aexp -> aexp -> aexp
  | AMinus: aexp -> aexp -> aexp
  | AMult: aexp -> aexp -> aexp.


Inductive bexp: Type :=
  | BTrue: bexp
  | BFalse: bexp
  | BEq: aexp -> aexp -> bexp
  | BLe: aexp -> aexp -> bexp
  | BNot: bexp -> bexp
  | BAnd: bexp -> bexp -> bexp.


Fixpoint aeval (a: aexp): nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2  => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.


Fixpoint beval (b: bexp): bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval a1) (aeval a2)
  | BLe a1 a2   => leb (aeval a1) (aeval a2)
  | BNot b1     => negb (beval b1)
  | BAnd b1 b2  => andb (beval b1) (beval b2)
  end.


Fixpoint optimize_0plus (a: aexp): aexp :=
  match a with
  | ANum n =>
      ANum n
  | APlus (ANum 0) e2 =>
      optimize_0plus e2
  | APlus e1 e2 =>
      APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 =>
      AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 =>
      AMult (optimize_0plus e1) (optimize_0plus e2)
  end.


(* proved in Imp *)
Axiom optimize_0plus_sound: forall a, aeval (optimize_0plus a) = aeval a.


(** **** Exercise: 3 stars (optimize_0plus_b)  *)

Fixpoint optimize_0plus_b (b: bexp): bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BNot b1 => BNot (optimize_0plus_b b1)
  | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
  end.

Theorem optimize_0plus_b_sound: forall b, beval (optimize_0plus_b b) = beval b.
Proof.
  intros b.
  induction b;
    try (
      reflexivity
    );
    try (
      simpl;
      repeat (rewrite optimize_0plus_sound);
      reflexivity
    ).
  - simpl.
    rewrite IHb.
    reflexivity.
  - simpl.
    rewrite IHb1.
    rewrite IHb2.
    reflexivity.
Qed.


(** **** Exercise: 4 stars, optional (optimizer)  *)
(* not do it *)


End AExp.




Inductive id: Type :=
  | Id: string -> id.

Definition beq_id x y :=
  match x, y with
  | Id n1, Id n2 => if string_dec n1 n2 then true else false
  end.

Definition total_map (A: Type) := id -> A.

Definition t_empty {A: Type}(v: A): total_map A := (fun _ => v).

Definition t_update {A:Type}(m: total_map A)(x: id)(v: A) :=
  fun x' => if beq_id x x' then v else m x'.


Definition state := total_map nat.

Definition empty_state : state :=  t_empty 0.


Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp                (* <----- NEW *)
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Definition W : id := Id "W".
Definition X : id := Id "X".
Definition Y : id := Id "Y".
Definition Z : id := Id "Z".

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                (* <----- NEW *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2   => leb (aeval st a1) (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

Inductive com: Type :=
  | CSkip: com
  | CAss: id -> aexp -> com
  | CSeq: com -> com -> com
  | CIf: bexp -> com -> com -> com
  | CWhile: bexp -> com -> com.


Notation "'SKIP'" := CSkip.
Notation "x '::=' a" := (CAss x a) (at level 60).
Notation "c1 ;; c2" := (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).


Reserved Notation "c1 '/' st '\\' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st \\ st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      (x ::= a1) / st \\ (t_update st x n)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st  \\ st' ->
      c2 / st' \\ st'' ->
      (c1 ;; c2) / st \\ st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      c1 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      c2 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileEnd : forall b st c,
      beval st b = false ->
      (WHILE b DO c END) / st \\ st
  | E_WhileLoop : forall st st' st'' b c,
      beval st b = true ->
      c / st \\ st' ->
      (WHILE b DO c END) / st' \\ st'' ->
      (WHILE b DO c END) / st \\ st''

  where "c1 '/' st '\\' st'" := (ceval c1 st st').


(** **** Exercise: 2 stars (ceval_example2)  *)
Example ceval_example2:
    (X ::= ANum 0;; Y ::= ANum 1;; Z ::= ANum 2) / empty_state \\
    (t_update (t_update (t_update empty_state X 0) Y 1) Z 2).
Proof.
  apply E_Seq with (t_update empty_state X 0).
  - apply E_Ass.
    reflexivity.
  - apply E_Seq with (t_update (t_update empty_state X 0) Y 1).
    + apply E_Ass.
      reflexivity.
    + apply E_Ass.
      reflexivity.
Qed.



(** **** Exercise: 3 stars, advanced (pup_to_n)  *)

Definition pup_to_n: com :=
  Y ::= ANum 0;;
  WHILE (BLe (AId X) (ANum 0)) DO
    Y ::= APlus (AId X) (AId Y);;
    X ::= AMinus (AId X) (ANum 1)
  END.

(*
Theorem pup_to_2_ceval :
  pup_to_n / (t_update empty_state X 2) \\
    t_update (t_update (t_update (t_update (t_update (t_update empty_state
      X 2) Y 0) Y 2) X 1) Y 3) X 0.
Proof.
  unfold pup_to_n.
  apply E_Seq with (t_update (t_update empty_state X 2) Y 0).
  - apply E_Ass.
    reflexivity.
Abort.
*)


(** **** Exercise: 3 stars, recommendedM (XtimesYinZ_spec)  *)
Definition XtimesYinZ : com := Z ::= (AMult (AId X) (AId Y)).

(* proved in Maps *)
Axiom t_update_eq: forall A (m: total_map A) x v, (t_update m x v) x = v.


Theorem xtimesyinz_spec: forall st n m st',
  st X = n ->
  st Y = m ->
  XtimesYinZ / st \\ st' ->
  st' Z = n * m.
Proof.
  intros st n m st' H P Q.
  inversion Q.
  subst.
  simpl.
  apply t_update_eq.
Qed.


(* More exercises *)













(** **** Exercise: 3 stars (stack_compiler)  *)

Module stack_compiler.
Inductive aexp: Type:=
  | ANum: nat -> aexp
  | AId: id-> aexp
  | APlus: aexp -> aexp -> aexp
  | AMinus: aexp -> aexp -> aexp
  | AMult: aexp -> aexp -> aexp.



Inductive sinstr: Type :=
  | SPush: nat -> sinstr
  | SLoad: id -> sinstr
  | SPlus: sinstr
  | SMinus: sinstr
  | SMult: sinstr
  .


Fixpoint s_execute (st: state)(stack: list nat)(prog: list sinstr): list nat :=
  match prog with
  | nil => stack
  | SPush n :: h  => s_execute st (n :: stack) h
  | SLoad id :: h => s_execute st (st id :: stack) h
  | SPlus :: h => 
    match stack with
    | x :: y :: t => s_execute st ((y + x) :: t) h
    | _ => stack 
    end
  | SMinus :: h =>
    match stack with
    | x :: y :: t => s_execute st ((y - x) :: t) h
    | _ => stack
    end
  | SMult :: h =>
    match stack with
    | x :: y :: t => s_execute st ((y * x) :: t) h
    | _ => stack
    end
  end.



Example s_execute1: s_execute empty_state [] [SPush 5; SPush 3; SPush 1; SMinus] = [2; 5].
Proof. reflexivity. Qed.

Definition X: id := Id "X".
Definition Y: id := Id "Y".

Example s_execute2: s_execute (t_update empty_state X 3) [3;4][SPush 4; SLoad X; SMult; SPlus]
   = [15; 4].
Proof. reflexivity. Qed.


Fixpoint s_compile (e: aexp): list sinstr :=
  match e with
  | ANum n =>     SPush n :: nil
  | AId id =>     SLoad id :: nil
  | APlus x y =>  s_compile x ++ s_compile y ++ [SPlus]
  | AMinus x y => s_compile x ++ s_compile y ++ [SMinus] 
  | AMult x y =>  s_compile x ++ s_compile y ++ [SMult]
  end.


Example s_compile1: s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof. reflexivity. Qed.

End stack_compiler.
