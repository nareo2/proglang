Require Export D.



Theorem plus_tech : forall m n : nat,
  S (m + n) = m + S n.
Proof.
  intros m n.
  induction m as [|m' IHm].
  - reflexivity.
  - simpl. rewrite <- IHm.
    reflexivity.
Qed. 


Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof. (*
  intros n m.
  induction n as [|n' IHn].
  - simpl.
    induction m as [|m' IHm].
    + reflexivity.
    + simpl. rewrite <- IHm.
      reflexivity.
  - simpl. rewrite -> IHn.
*)
  intros n m.
  induction n as [|n' IHn].
  - simpl.
    induction m as [|m' IHm].
    + reflexivity.
    + simpl. rewrite <- IHm.
      reflexivity.
  - simpl. rewrite -> IHn.
    rewrite -> plus_tech.
    reflexivity.
Qed.

