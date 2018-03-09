
(** **** Exercise: 3 stars, recommended (mult_comm)  *)
Theorem plus_swap: forall n m p: nat, n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  assert (H: n + m = m + n). {
    rewrite -> plus_comm.
    reflexivity.
  }
  rewrite -> H.
  reflexivity.
Qed.


Lemma mult_distr: forall n m: nat, (n * m) + n = n * (S m).
Proof.
  intros n m.
  induction n as [|n H].
  - reflexivity.
  - simpl. 
    rewrite <- H.
    rewrite -> plus_n_Sm.
    rewrite -> plus_n_Sm.
    rewrite -> plus_assoc.
    reflexivity.
Qed.


Lemma mult_distr2: forall n m: nat, (n * m) + m = (S n) * m.
Proof.
  intros n m. 
  induction n as [|n H].
  - simpl.
    apply plus_n_O.
  - simpl.
    rewrite -> plus_assoc.
    assert (P: n*m + m = m + n*m). {
      rewrite -> plus_comm.
      reflexivity.
    }
    rewrite <- P.
    rewrite <- plus_comm with (n := n*m) (m := m + m).
    rewrite -> plus_assoc.
    reflexivity. 
Qed.
    
   
Theorem mult_comm: forall m n: nat, m * n = n * m.
Proof.
  intros m n.
  induction n as [|n H].
  (* n = 0 *)
  - simpl.
    rewrite -> mult_0_r.
    reflexivity.
  (* n = S n' *)
  - rewrite <- mult_distr.
    rewrite -> H.
    rewrite -> mult_distr2.
    reflexivity. 
Qed.



Theorem leb_refl: forall n: nat, true = leb n n.
Proof.
  intros n.
  induction n as [|n H].
  - reflexivity.
  - simpl.
    apply H.
Qed.



Theorem zero_nbeq_S: forall n: nat, eqb 0 (S n) = false.
Proof.
  intros n.
  reflexivity.
Qed.
  
  
Theorem andb_false_r: forall b: bool, andb b false = false.
Proof.
  intros b.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.
  


Theorem plus_ble_compat_l: forall n m p: nat,
  leb n m = true -> leb (p + n) (p + m) = true.
Proof.
  intros n m p H.
  induction p as [|p P].
  - simpl.
    apply H.
  - simpl.
    apply P.
Qed.    
  
    
Theorem S_nbeq_0: forall n: nat, eqb (S n) 0 = false.
Proof.
  intros n.
  reflexivity.
Qed.



Theorem mult_1_l: forall n: nat, 1 * n = n.
Proof.
  intros n.
  simpl.
  symmetry.
  apply plus_n_O.
Qed.


  
Theorem all3_spec: forall b c: bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  intros b c.
  destruct b.
  destruct c.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.



Theorem mult_plus_distr_r: forall n m p: nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction p.
  - rewrite !mult_0_r.
    reflexivity.
  - rewrite <- !mult_n_Sm.
    rewrite IHp.
    assert (P: n + (m * p + m) = m * p + (n + m)). { 
      apply plus_swap.
    }
Abort. (*
    assert (Q: forall x y z: nat, x + y + z = x + (y + z)). {
      intros x y z.
      induction x.
      + reflexivity.
      + simpl.
        rewrite IHx.
        reflexivity.
    }
    assert (R: n * p + n + (m * p + m) = n * p + m * p + m + n). {
      rewrite Q.
      
      reflexivity.
    } 
    rewrite Q.    
Abort.
    (*rewrite plus_swap.*)
*)    



Theorem mult_assoc: forall n m p: nat,
  n * (m * p) = (n * m) * p.
Proof.
Abort.

