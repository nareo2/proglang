Require Export P08.



Theorem snoc_append : forall (l:natlist) (n:nat),
  snoc l n = l ++ [n].
Proof.
  intros l n.
  induction l as [|h t].
  - reflexivity.
  - simpl. rewrite -> IHt.
    reflexivity.
Qed.

