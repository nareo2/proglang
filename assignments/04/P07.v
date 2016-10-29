Require Export P02.


Theorem s_equal : forall n m,
  n = m -> S n = S m .
Proof.
  intros.
  rewrite -> H.
  reflexivity.
Qed.

Theorem ss_equal : forall n m,
  S n + S m = S (S (n + m)).
Proof.
  intros n m.
  simpl.
  apply s_equal.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  - intros m.
    intros H.
    simpl in H.
    rewrite -> H.
    induction m as [| m'].
    + reflexivity.
    + simpl.
      inversion H.
  - intros m H.
    generalize dependent m.
    induction m as [|h t IHt].
    + intros.
      inversion H.
    + rewrite -> ss_equal. 
      rewrite -> ss_equal. 
      intros H'.
      apply s_equal.
      apply IHn'.
      inversion H'.
      reflexivity.
Qed.

