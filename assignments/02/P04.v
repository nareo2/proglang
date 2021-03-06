Require Export P03.



Theorem plus_tec3 : forall a b c : nat,
  a + (b + c) = a+ b + c.
Proof.
  intros a b c.
  induction a as [|a' IHa].
  - reflexivity.
  - simpl. rewrite -> IHa.
    reflexivity.
Qed.


(** **** Problem : 3 stars (mult_comm) *)

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.  
  intros n m p.
  induction n as [|n' IHn].
  - reflexivity.
  - simpl. rewrite -> IHn.
    rewrite -> plus_tec3.
    reflexivity.
Qed.
