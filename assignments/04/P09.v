Require Export P04.

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.

Proof.
  intros X test x l.

  induction l as [|h t IHt].
  - simpl.
    intros lf H.
    inversion H.
  - simpl.
    destruct (test h) eqn :eq.
    + intros lf.
      intros H.
      inversion H.
      rewrite <- H1.
      apply eq.
    + apply IHt.
Qed.

