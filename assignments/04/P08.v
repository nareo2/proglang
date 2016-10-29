Require Export P03.

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof.
  intros.
  generalize dependent n.
  induction l as [|h t IHt].
  - reflexivity.
  - simpl.
    induction n as [|n' IHn'].
    + simpl.
      intros H.
      inversion H.
    + simpl.
      intros H.
      apply IHt.
      inversion H.
      reflexivity.
Qed.

