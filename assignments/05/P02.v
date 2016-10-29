Require Export P01.



Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof. 
  intros n m.
  intros H.
  induction n as [|n' Hn].
  - destruct m. 
    + left.
      reflexivity.
    + left.
      reflexivity.
  - induction m as [|m' Hm'].
    + right.
      reflexivity.
    + inversion H. 
Qed.

