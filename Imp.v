Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import String.
Import ListNotations.

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
  
  
Theorem optimize_0plus_sound: forall a, aeval (optimize_0plus a) = aeval a.
Proof. (* proved by other program *) Admitted.




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


(* More exercises *)



(** **** Exercise: 3 stars (stack_compiler)  *)

Module stack_compiler.

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

Inductive aexp: Type:=
  | ANum: nat -> aexp
  | AId: id-> aexp
  | APlus: aexp -> aexp -> aexp
  | AMinus: aexp -> aexp -> aexp
  | AMult: aexp -> aexp -> aexp.

Definition state := total_map nat.

Definition empty_state : state :=  t_empty 0.
  
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
