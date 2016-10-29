Require Export P03.



Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  unfold iff.
  split.
  - intros [Hl | Hr].
    split.
    + left.
      apply Hl.
    + left.
      apply Hl.
    + split.
      * right.
        apply Hr.
      * right.
        apply Hr.
  - intros [[HP | HQ]  [HP' | HR']].
    + left.
      apply HP.
    + left.
      apply HP.
  + left.
      apply HP'.
  + right.
    split.
    * apply HQ.
    * apply HR'.
Qed.

