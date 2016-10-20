Require Export P03.



Theorem snoc_with_append : forall X : Type,
                         forall l1 l2 : list X,
                         forall v : X,
  snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
  intros X.
  intros l1 l2.
  intros v.
  induction l1 as [|h t IHl'].
  - reflexivity.
  - simpl. rewrite <- IHl'.
    reflexivity.
Qed.

